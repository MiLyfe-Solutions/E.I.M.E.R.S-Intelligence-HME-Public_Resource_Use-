import V185TrunkScan23Chunk0446

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2643414 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_2643414 : Nat := 118140960795 + 2643414 * 2 ^ 59
def prefixEnd_2643414 : Nat := 4983230072969 + 3 ^ 40 * 2643414 * 2
def baseEnd_2643414 : Nat := 1357341950824225864268167

theorem tailTrace_2643414 : CollatzResearch.WordTrace tailWord_2643414 prefixEnd_2643414 1357341950824225864268167 := by
  unfold tailWord_2643414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025826827835625750863081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64275486163580008009206197 6025826827835625750863081)
  ·
    refine ⟨4519370120876719313147311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6025826827835625750863081 4519370120876719313147311)
    ·
      refine ⟨6779055181315078969720967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4519370120876719313147311 6779055181315078969720967)
      ·
        refine ⟨10168582771972618454581451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6779055181315078969720967 10168582771972618454581451)
        ·
          refine ⟨15252874157958927681872177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10168582771972618454581451 15252874157958927681872177)
          ·
            refine ⟨11439655618469195761404133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15252874157958927681872177 11439655618469195761404133)
            ·
              refine ⟨2144935428462974205263275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11439655618469195761404133 2144935428462974205263275)
              ·
                refine ⟨3217403142694461307894913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144935428462974205263275 3217403142694461307894913)
                ·
                  refine ⟨2413052357020845980921185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3217403142694461307894913 2413052357020845980921185)
                  ·
                    refine ⟨1809789267765634485690889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2413052357020845980921185 1809789267765634485690889)
                    ·
                      refine ⟨1357341950824225864268167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809789267765634485690889 1357341950824225864268167)
                      ·
                        rfl

theorem cell23_2643414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_2643414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643414 prefixEnd_2643414 := by exact prefixLift 2643414
  have htrace : WordTrace (prefixWord ++ tailWord_2643414) baseStart_2643414 baseEnd_2643414 := by
    simpa [prefixWord, tailWord_2643414, baseEnd_2643414] using wordTrace_append hprefix tailTrace_2643414
  have hstable : (prefixWord ++ tailWord_2643414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643414).length < 2 ^ (prefixWord ++ tailWord_2643414).sum := by decide
  have hdescent : baseEnd_2643414 < baseStart_2643414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643436 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 3, 6, 2]
def baseStart_2643436 : Nat := 118140960795 + 2643436 * 2 ^ 59
def prefixEnd_2643436 : Nat := 4983230072969 + 3 ^ 40 * 2643436 * 2
def baseEnd_2643436 : Nat := 1357353247398624778193065

theorem tailTrace_2643436 : CollatzResearch.WordTrace tailWord_2643436 prefixEnd_2643436 1357353247398624778193065 := by
  unfold tailWord_2643436
  simp only [CollatzResearch.WordTrace]
  refine ⟨48207015825645154885555081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64276021100860206514073441 48207015825645154885555081)
  ·
    refine ⟨36155261869233866164166311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48207015825645154885555081 36155261869233866164166311)
    ·
      refine ⟨54232892803850799246249467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36155261869233866164166311 54232892803850799246249467)
      ·
        refine ⟨81349339205776198869374201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54232892803850799246249467 81349339205776198869374201)
        ·
          refine ⟨61012004404332149152030651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81349339205776198869374201 61012004404332149152030651)
          ·
            refine ⟨91518006606498223728045977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61012004404332149152030651 91518006606498223728045977)
            ·
              refine ⟨68638504954873667796034483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91518006606498223728045977 68638504954873667796034483)
              ·
                refine ⟨102957757432310501694051725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68638504954873667796034483 102957757432310501694051725)
                ·
                  refine ⟨38609159037116438135269397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102957757432310501694051725 38609159037116438135269397)
                  ·
                    refine ⟨1809804329864833037590753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38609159037116438135269397 1809804329864833037590753)
                    ·
                      refine ⟨1357353247398624778193065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809804329864833037590753 1357353247398624778193065)
                      ·
                        rfl

theorem cell23_2643436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_2643436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643436 prefixEnd_2643436 := by exact prefixLift 2643436
  have htrace : WordTrace (prefixWord ++ tailWord_2643436) baseStart_2643436 baseEnd_2643436 := by
    simpa [prefixWord, tailWord_2643436, baseEnd_2643436] using wordTrace_append hprefix tailTrace_2643436
  have hstable : (prefixWord ++ tailWord_2643436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643436).length < 2 ^ (prefixWord ++ tailWord_2643436).sum := by decide
  have hdescent : baseEnd_2643436 < baseStart_2643436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643449 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2643449 : Nat := 118140960795 + 2643449 * 2 ^ 59
def prefixEnd_2643449 : Nat := 4983230072969 + 3 ^ 40 * 2643449 * 2
def baseEnd_2643449 : Nat := 1357359922647133227330505

theorem tailTrace_2643449 : CollatzResearch.WordTrace tailWord_2643449 prefixEnd_2643449 1357359922647133227330505 := by
  unfold tailWord_2643449
  simp only [CollatzResearch.WordTrace]
  refine ⟨96414505800243212991333401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64276337200162141994222267 96414505800243212991333401)
  ·
    refine ⟨72310879350182409743500051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96414505800243212991333401 72310879350182409743500051)
    ·
      refine ⟨108466319025273614615250077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72310879350182409743500051 108466319025273614615250077)
      ·
        refine ⟨40674869634477605480718779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108466319025273614615250077 40674869634477605480718779)
        ·
          refine ⟨61012304451716408221078169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40674869634477605480718779 61012304451716408221078169)
          ·
            refine ⟨45759228338787306165808627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61012304451716408221078169 45759228338787306165808627)
            ·
              refine ⟨68638842508180959248712941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45759228338787306165808627 68638842508180959248712941)
              ·
                refine ⟨25739565940567859718267353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68638842508180959248712941 25739565940567859718267353)
                ·
                  refine ⟨19304674455425894788700515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25739565940567859718267353 19304674455425894788700515)
                  ·
                    refine ⟨28957011683138842183050773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19304674455425894788700515 28957011683138842183050773)
                    ·
                      refine ⟨1357359922647133227330505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28957011683138842183050773 1357359922647133227330505)
                      ·
                        rfl

theorem cell23_2643449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2643449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643449 prefixEnd_2643449 := by exact prefixLift 2643449
  have htrace : WordTrace (prefixWord ++ tailWord_2643449) baseStart_2643449 baseEnd_2643449 := by
    simpa [prefixWord, tailWord_2643449, baseEnd_2643449] using wordTrace_append hprefix tailTrace_2643449
  have hstable : (prefixWord ++ tailWord_2643449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643449).length < 2 ^ (prefixWord ++ tailWord_2643449).sum := by decide
  have hdescent : baseEnd_2643449 < baseStart_2643449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643454 : List Nat := [4, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_2643454 : Nat := 118140960795 + 2643454 * 2 ^ 59
def prefixEnd_2643454 : Nat := 4983230072969 + 3 ^ 40 * 2643454 * 2
def baseEnd_2643454 : Nat := 150818054450045078640887

theorem tailTrace_2643454 : CollatzResearch.WordTrace tailWord_2643454 prefixEnd_2643454 150818054450045078640887 := by
  unfold tailWord_2643454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12051836020653137355658177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64276458776816732563510277 12051836020653137355658177)
  ·
    refine ⟨9038877015489853016743633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12051836020653137355658177 9038877015489853016743633)
    ·
      refine ⟨6779157761617389762557725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9038877015489853016743633 6779157761617389762557725)
      ·
        refine ⟨2542184160606521160959147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6779157761617389762557725 2542184160606521160959147)
        ·
          refine ⟨3813276240909781741438721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542184160606521160959147 3813276240909781741438721)
          ·
            refine ⟨2859957180682336306079041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813276240909781741438721 2859957180682336306079041)
            ·
              refine ⟨2144967885511752229559281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2859957180682336306079041 2144967885511752229559281)
              ·
                refine ⟨1608725914133814172169461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2144967885511752229559281 1608725914133814172169461)
                ·
                  refine ⟨150818054450045078640887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1608725914133814172169461 150818054450045078640887)
                  ·
                    rfl

theorem cell23_2643454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_2643454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643454 prefixEnd_2643454 := by exact prefixLift 2643454
  have htrace : WordTrace (prefixWord ++ tailWord_2643454) baseStart_2643454 baseEnd_2643454 := by
    simpa [prefixWord, tailWord_2643454, baseEnd_2643454] using wordTrace_append hprefix tailTrace_2643454
  have hstable : (prefixWord ++ tailWord_2643454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643454).length < 2 ^ (prefixWord ++ tailWord_2643454).sum := by decide
  have hdescent : baseEnd_2643454 < baseStart_2643454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643470 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_2643470 : Nat := 118140960795 + 2643470 * 2 ^ 59
def prefixEnd_2643470 : Nat := 4983230072969 + 3 ^ 40 * 2643470 * 2
def baseEnd_2643470 : Nat := 1357370705740877645167909

theorem tailTrace_2643470 : CollatzResearch.WordTrace tailWord_2643470 prefixEnd_2643470 1357370705740877645167909 := by
  unfold tailWord_2643470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12051908966645891697230983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64276847822111422385231909 12051908966645891697230983)
  ·
    refine ⟨18077863449968837545846475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12051908966645891697230983 18077863449968837545846475)
    ·
      refine ⟨27116795174953256318769713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18077863449968837545846475 27116795174953256318769713)
      ·
        refine ⟨20337596381214942239077285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27116795174953256318769713 20337596381214942239077285)
        ·
          refine ⟨3813299321477801669826991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20337596381214942239077285 3813299321477801669826991)
          ·
            refine ⟨5719948982216702504740487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3813299321477801669826991 5719948982216702504740487)
            ·
              refine ⟨8579923473325053757110731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5719948982216702504740487 8579923473325053757110731)
              ·
                refine ⟨12869885209987580635666097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8579923473325053757110731 12869885209987580635666097)
                ·
                  refine ⟨9652413907490685476749573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12869885209987580635666097 9652413907490685476749573)
                  ·
                    refine ⟨1809827607654503526890545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9652413907490685476749573 1809827607654503526890545)
                    ·
                      refine ⟨1357370705740877645167909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1809827607654503526890545 1357370705740877645167909)
                      ·
                        rfl

theorem cell23_2643470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_2643470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643470 prefixEnd_2643470 := by exact prefixLift 2643470
  have htrace : WordTrace (prefixWord ++ tailWord_2643470) baseStart_2643470 baseEnd_2643470 := by
    simpa [prefixWord, tailWord_2643470, baseEnd_2643470] using wordTrace_append hprefix tailTrace_2643470
  have hstable : (prefixWord ++ tailWord_2643470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643470).length < 2 ^ (prefixWord ++ tailWord_2643470).sum := by decide
  have hdescent : baseEnd_2643470 < baseStart_2643470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643499 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 5]
def baseStart_2643499 : Nat := 118140960795 + 2643499 * 2 ^ 59
def prefixEnd_2643499 : Nat := 4983230072969 + 3 ^ 40 * 2643499 * 2
def baseEnd_2643499 : Nat := 1357385596679858031705275

theorem tailTrace_2643499 : CollatzResearch.WordTrace tailWord_2643499 prefixEnd_2643499 1357385596679858031705275 := by
  unfold tailWord_2643499
  simp only [CollatzResearch.WordTrace]
  refine ⟨96416329450062071530653551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64277552966708047687102367 96416329450062071530653551)
  ·
    refine ⟨144624494175093107295980327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96416329450062071530653551 144624494175093107295980327)
    ·
      refine ⟨216936741262639660943970491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144624494175093107295980327 216936741262639660943970491)
      ·
        refine ⟨325405111893959491415955737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216936741262639660943970491 325405111893959491415955737)
        ·
          refine ⟨244053833920469618561966803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325405111893959491415955737 244053833920469618561966803)
          ·
            refine ⟨366080750880704427842950205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244053833920469618561966803 366080750880704427842950205)
            ·
              refine ⟨137280281580264160441106327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366080750880704427842950205 137280281580264160441106327)
              ·
                refine ⟨205920422370396240661659491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137280281580264160441106327 205920422370396240661659491)
                ·
                  refine ⟨308880633555594360992489237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205920422370396240661659491 308880633555594360992489237)
                  ·
                    refine ⟨14478779697918485671522933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 308880633555594360992489237 14478779697918485671522933)
                    ·
                      refine ⟨1357385596679858031705275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14478779697918485671522933 1357385596679858031705275)
                      ·
                        rfl

theorem cell23_2643499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_2643499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643499 prefixEnd_2643499 := by exact prefixLift 2643499
  have htrace : WordTrace (prefixWord ++ tailWord_2643499) baseStart_2643499 baseEnd_2643499 := by
    simpa [prefixWord, tailWord_2643499, baseEnd_2643499] using wordTrace_append hprefix tailTrace_2643499
  have hstable : (prefixWord ++ tailWord_2643499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643499).length < 2 ^ (prefixWord ++ tailWord_2643499).sum := by decide
  have hdescent : baseEnd_2643499 < baseStart_2643499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643543 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_2643543 : Nat := 118140960795 + 2643543 * 2 ^ 59
def prefixEnd_2643543 : Nat := 4983230072969 + 3 ^ 40 * 2643543 * 2
def baseEnd_2643543 : Nat := 1357408189828655859555073

theorem tailTrace_2643543 : CollatzResearch.WordTrace tailWord_2643543 prefixEnd_2643543 1357408189828655859555073 := by
  unfold tailWord_2643543
  simp only [CollatzResearch.WordTrace]
  refine ⟨96417934261902667045255283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64278622841268444696836855 96417934261902667045255283)
  ·
    refine ⟨144626901392854000567882925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96417934261902667045255283 144626901392854000567882925)
    ·
      refine ⟨54235088022320250212956097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144626901392854000567882925 54235088022320250212956097)
      ·
        refine ⟨40676316016740187659717073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54235088022320250212956097 40676316016740187659717073)
        ·
          refine ⟨30507237012555140744787805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40676316016740187659717073 30507237012555140744787805)
          ·
            refine ⟨11440213879708177779295427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30507237012555140744787805 11440213879708177779295427)
            ·
              refine ⟨17160320819562266668943141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11440213879708177779295427 17160320819562266668943141)
              ·
                refine ⟨3217560153667925000426839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17160320819562266668943141 3217560153667925000426839)
                ·
                  refine ⟨4826340230501887500640259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217560153667925000426839 4826340230501887500640259)
                  ·
                    refine ⟨7239510345752831250960389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4826340230501887500640259 7239510345752831250960389)
                    ·
                      refine ⟨1357408189828655859555073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7239510345752831250960389 1357408189828655859555073)
                      ·
                        rfl

theorem cell23_2643543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_2643543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643543 prefixEnd_2643543 := by exact prefixLift 2643543
  have htrace : WordTrace (prefixWord ++ tailWord_2643543) baseStart_2643543 baseEnd_2643543 := by
    simpa [prefixWord, tailWord_2643543, baseEnd_2643543] using wordTrace_append hprefix tailTrace_2643543
  have hstable : (prefixWord ++ tailWord_2643543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643543).length < 2 ^ (prefixWord ++ tailWord_2643543).sum := by decide
  have hdescent : baseEnd_2643543 < baseStart_2643543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643546 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_2643546 : Nat := 118140960795 + 2643546 * 2 ^ 59
def prefixEnd_2643546 : Nat := 4983230072969 + 3 ^ 40 * 2643546 * 2
def baseEnd_2643546 : Nat := 1357409730270619347817559

theorem tailTrace_2643546 : CollatzResearch.WordTrace tailWord_2643546 prefixEnd_2643546 1357409730270619347817559 := by
  unfold tailWord_2643546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24104510920222949639403623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64278695787261199038409661 24104510920222949639403623)
  ·
    refine ⟨36156766380334424459105435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24104510920222949639403623 36156766380334424459105435)
    ·
      refine ⟨54235149570501636688658153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36156766380334424459105435 54235149570501636688658153)
      ·
        refine ⟨40676362177876227516493615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54235149570501636688658153 40676362177876227516493615)
        ·
          refine ⟨61014543266814341274740423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40676362177876227516493615 61014543266814341274740423)
          ·
            refine ⟨91521814900221511912110635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61014543266814341274740423 91521814900221511912110635)
            ·
              refine ⟨137282722350332267868165953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91521814900221511912110635 137282722350332267868165953)
              ·
                refine ⟨102962041762749200901124465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137282722350332267868165953 102962041762749200901124465)
                ·
                  refine ⟨77221531322061900675843349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102962041762749200901124465 77221531322061900675843349)
                  ·
                    refine ⟨3619759280721651594180157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77221531322061900675843349 3619759280721651594180157)
                    ·
                      refine ⟨1357409730270619347817559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3619759280721651594180157 1357409730270619347817559)
                      ·
                        rfl

theorem cell23_2643546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_2643546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643546 prefixEnd_2643546 := by exact prefixLift 2643546
  have htrace : WordTrace (prefixWord ++ tailWord_2643546) baseStart_2643546 baseEnd_2643546 := by
    simpa [prefixWord, tailWord_2643546, baseEnd_2643546] using wordTrace_append hprefix tailTrace_2643546
  have hstable : (prefixWord ++ tailWord_2643546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643546).length < 2 ^ (prefixWord ++ tailWord_2643546).sum := by decide
  have hdescent : baseEnd_2643546 < baseStart_2643546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643560 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2643560 : Nat := 118140960795 + 2643560 * 2 ^ 59
def prefixEnd_2643560 : Nat := 4983230072969 + 3 ^ 40 * 2643560 * 2
def baseEnd_2643560 : Nat := 1357416918999782293042495

theorem tailTrace_2643560 : CollatzResearch.WordTrace tailWord_2643560 prefixEnd_2643560 1357416918999782293042495 := by
  unfold tailWord_2643560
  simp only [CollatzResearch.WordTrace]
  refine ⟨48209277151420539474312067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64279036201894052632416089 48209277151420539474312067)
  ·
    refine ⟨72313915727130809211468101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48209277151420539474312067 72313915727130809211468101)
    ·
      refine ⟨13558859198837026727150269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72313915727130809211468101 13558859198837026727150269)
      ·
        refine ⟨5084572199563885022681351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13558859198837026727150269 5084572199563885022681351)
        ·
          refine ⟨7626858299345827534022027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5084572199563885022681351 7626858299345827534022027)
          ·
            refine ⟨11440287449018741301033041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7626858299345827534022027 11440287449018741301033041)
            ·
              refine ⟨8580215586764055975774781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11440287449018741301033041 8580215586764055975774781)
              ·
                refine ⟨3217580845036520990915543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8580215586764055975774781 3217580845036520990915543)
                ·
                  refine ⟨4826371267554781486373315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217580845036520990915543 4826371267554781486373315)
                  ·
                    refine ⟨7239556901332172229559973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4826371267554781486373315 7239556901332172229559973)
                    ·
                      refine ⟨1357416918999782293042495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7239556901332172229559973 1357416918999782293042495)
                      ·
                        rfl

theorem cell23_2643560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2643560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643560 prefixEnd_2643560 := by exact prefixLift 2643560
  have htrace : WordTrace (prefixWord ++ tailWord_2643560) baseStart_2643560 baseEnd_2643560 := by
    simpa [prefixWord, tailWord_2643560, baseEnd_2643560] using wordTrace_append hprefix tailTrace_2643560
  have hstable : (prefixWord ++ tailWord_2643560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643560).length < 2 ^ (prefixWord ++ tailWord_2643560).sum := by decide
  have hdescent : baseEnd_2643560 < baseStart_2643560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643573 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2643573 : Nat := 118140960795 + 2643573 * 2 ^ 59
def prefixEnd_2643573 : Nat := 4983230072969 + 3 ^ 40 * 2643573 * 2
def baseEnd_2643573 : Nat := 1357423594248290742179935

theorem tailTrace_2643573 : CollatzResearch.WordTrace tailWord_2643573 prefixEnd_2643573 1357423594248290742179935 := by
  unfold tailWord_2643573
  simp only [CollatzResearch.WordTrace]
  refine ⟨96419028451793982168847373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64279352301195988112564915 96419028451793982168847373)
  ·
    refine ⟨36157135669422743313317765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96419028451793982168847373 36157135669422743313317765)
    ·
      refine ⟨6779462938016764371247081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36157135669422743313317765 6779462938016764371247081)
      ·
        refine ⟨5084597203512573278435311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6779462938016764371247081 5084597203512573278435311)
        ·
          refine ⟨7626895805268859917652967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5084597203512573278435311 7626895805268859917652967)
          ·
            refine ⟨11440343707903289876479451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7626895805268859917652967 11440343707903289876479451)
            ·
              refine ⟨17160515561854934814719177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11440343707903289876479451 17160515561854934814719177)
              ·
                refine ⟨12870386671391201111039383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17160515561854934814719177 12870386671391201111039383)
                ·
                  refine ⟨19305580007086801666559075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12870386671391201111039383 19305580007086801666559075)
                  ·
                    refine ⟨28958370010630202499838613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19305580007086801666559075 28958370010630202499838613)
                    ·
                      refine ⟨1357423594248290742179935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28958370010630202499838613 1357423594248290742179935)
                      ·
                        rfl

theorem cell23_2643573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2643573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643573 prefixEnd_2643573 := by exact prefixLift 2643573
  have htrace : WordTrace (prefixWord ++ tailWord_2643573) baseStart_2643573 baseEnd_2643573 := by
    simpa [prefixWord, tailWord_2643573, baseEnd_2643573] using wordTrace_append hprefix tailTrace_2643573
  have hstable : (prefixWord ++ tailWord_2643573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643573).length < 2 ^ (prefixWord ++ tailWord_2643573).sum := by decide
  have hdescent : baseEnd_2643573 < baseStart_2643573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643576 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_2643576 : Nat := 118140960795 + 2643576 * 2 ^ 59
def prefixEnd_2643576 : Nat := 4983230072969 + 3 ^ 40 * 2643576 * 2
def baseEnd_2643576 : Nat := 1357425134690254230442421

theorem tailTrace_2643576 : CollatzResearch.WordTrace tailWord_2643576 prefixEnd_2643576 1357425134690254230442421 := by
  unfold tailWord_2643576
  simp only [CollatzResearch.WordTrace]
  refine ⟨48209568935391556840603291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64279425247188742454137721 48209568935391556840603291)
  ·
    refine ⟨72314353403087335260904937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48209568935391556840603291 72314353403087335260904937)
    ·
      refine ⟨54235765052315501445678703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72314353403087335260904937 54235765052315501445678703)
      ·
        refine ⟨81353647578473252168518055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54235765052315501445678703 81353647578473252168518055)
        ·
          refine ⟨122030471367709878252777083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81353647578473252168518055 122030471367709878252777083)
          ·
            refine ⟨183045707051564817379165625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122030471367709878252777083 183045707051564817379165625)
            ·
              refine ⟨137284280288673613034374219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183045707051564817379165625 137284280288673613034374219)
              ·
                refine ⟨205926420433010419551561329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137284280288673613034374219 205926420433010419551561329)
                ·
                  refine ⟨154444815324757814663670997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205926420433010419551561329 154444815324757814663670997)
                  ·
                    refine ⟨3619800359174011281179789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 154444815324757814663670997 3619800359174011281179789)
                    ·
                      refine ⟨1357425134690254230442421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3619800359174011281179789 1357425134690254230442421)
                      ·
                        rfl

theorem cell23_2643576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_2643576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643576 prefixEnd_2643576 := by exact prefixLift 2643576
  have htrace : WordTrace (prefixWord ++ tailWord_2643576) baseStart_2643576 baseEnd_2643576 := by
    simpa [prefixWord, tailWord_2643576, baseEnd_2643576] using wordTrace_append hprefix tailTrace_2643576
  have hstable : (prefixWord ++ tailWord_2643576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643576).length < 2 ^ (prefixWord ++ tailWord_2643576).sum := by decide
  have hdescent : baseEnd_2643576 < baseStart_2643576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643614 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_2643614 : Nat := 118140960795 + 2643614 * 2 ^ 59
def prefixEnd_2643614 : Nat := 4983230072969 + 3 ^ 40 * 2643614 * 2
def baseEnd_2643614 : Nat := 1357444646955125081767247

theorem tailTrace_2643614 : CollatzResearch.WordTrace tailWord_2643614 prefixEnd_2643614 1357444646955125081767247 := by
  unfold tailWord_2643614
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052565480580680771386237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64280349229763630780726597 12052565480580680771386237)
  ·
    refine ⟨4519712055217755289269839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12052565480580680771386237 4519712055217755289269839)
    ·
      refine ⟨6779568082826632933904759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4519712055217755289269839 6779568082826632933904759)
      ·
        refine ⟨10169352124239949400857139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6779568082826632933904759 10169352124239949400857139)
        ·
          refine ⟨15254028186359924101285709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10169352124239949400857139 15254028186359924101285709)
          ·
            refine ⟨5720260569884971537982141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15254028186359924101285709 5720260569884971537982141)
            ·
              refine ⟨2145097713706864326743303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5720260569884971537982141 2145097713706864326743303)
              ·
                refine ⟨3217646570560296490114955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145097713706864326743303 3217646570560296490114955)
                ·
                  refine ⟨4826469855840444735172433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217646570560296490114955 4826469855840444735172433)
                  ·
                    refine ⟨3619852391880333551379325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4826469855840444735172433 3619852391880333551379325)
                    ·
                      refine ⟨1357444646955125081767247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3619852391880333551379325 1357444646955125081767247)
                      ·
                        rfl

theorem cell23_2643614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_2643614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643614 prefixEnd_2643614 := by exact prefixLift 2643614
  have htrace : WordTrace (prefixWord ++ tailWord_2643614) baseStart_2643614 baseEnd_2643614 := by
    simpa [prefixWord, tailWord_2643614, baseEnd_2643614] using wordTrace_append hprefix tailTrace_2643614
  have hstable : (prefixWord ++ tailWord_2643614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643614).length < 2 ^ (prefixWord ++ tailWord_2643614).sum := by decide
  have hdescent : baseEnd_2643614 < baseStart_2643614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643690 : List Nat := [3, 1, 3, 1, 1, 1, 4, 4, 5]
def baseStart_2643690 : Nat := 118140960795 + 2643690 * 2 ^ 59
def prefixEnd_2643690 : Nat := 4983230072969 + 3 ^ 40 * 2643690 * 2
def baseEnd_2643690 : Nat := 150831519053874087157433

theorem tailTrace_2643690 : CollatzResearch.WordTrace tailWord_2643690 prefixEnd_2643690 150831519053874087157433 := by
  unfold tailWord_2643690
  simp only [CollatzResearch.WordTrace]
  refine ⟨24105823948092527787714131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64282197194913407433904349 24105823948092527787714131)
  ·
    refine ⟨36158735922138791681571197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24105823948092527787714131 36158735922138791681571197)
    ·
      refine ⟨13559525970802046880589199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36158735922138791681571197 13559525970802046880589199)
      ·
        refine ⟨20339288956203070320883799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13559525970802046880589199 20339288956203070320883799)
        ·
          refine ⟨30508933434304605481325699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20339288956203070320883799 30508933434304605481325699)
          ·
            refine ⟨45763400151456908221988549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30508933434304605481325699 45763400151456908221988549)
            ·
              refine ⟨8580637528398170291622853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45763400151456908221988549 8580637528398170291622853)
              ·
                refine ⟨1608869536574656929679285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8580637528398170291622853 1608869536574656929679285)
                ·
                  refine ⟨150831519053874087157433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1608869536574656929679285 150831519053874087157433)
                  ·
                    rfl

theorem cell23_2643690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_2643690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643690 prefixEnd_2643690 := by exact prefixLift 2643690
  have htrace : WordTrace (prefixWord ++ tailWord_2643690) baseStart_2643690 baseEnd_2643690 := by
    simpa [prefixWord, tailWord_2643690, baseEnd_2643690] using wordTrace_append hprefix tailTrace_2643690
  have hstable : (prefixWord ++ tailWord_2643690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643690).length < 2 ^ (prefixWord ++ tailWord_2643690).sum := by decide
  have hdescent : baseEnd_2643690 < baseStart_2643690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643723 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 4]
def baseStart_2643723 : Nat := 118140960795 + 2643723 * 2 ^ 59
def prefixEnd_2643723 : Nat := 4983230072969 + 3 ^ 40 * 2643723 * 2
def baseEnd_2643723 : Nat := 1357500616346465155304245

theorem tailTrace_2643723 : CollatzResearch.WordTrace tailWord_2643723 prefixEnd_2643723 1357500616346465155304245 := by
  unfold tailWord_2643723
  simp only [CollatzResearch.WordTrace]
  refine ⟨96424499401250557786807823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64282999600833705191205215 96424499401250557786807823)
  ·
    refine ⟨144636749101875836680211735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96424499401250557786807823 144636749101875836680211735)
    ·
      refine ⟨216955123652813755020317603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144636749101875836680211735 216955123652813755020317603)
      ·
        refine ⟨325432685479220632530476405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216955123652813755020317603 325432685479220632530476405)
        ·
          refine ⟨30509314263676934299732163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 325432685479220632530476405 30509314263676934299732163)
          ·
            refine ⟨45763971395515401449598245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30509314263676934299732163 45763971395515401449598245)
            ·
              refine ⟨8580744636659137771799671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45763971395515401449598245 8580744636659137771799671)
              ·
                refine ⟨12871116954988706657699507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8580744636659137771799671 12871116954988706657699507)
                ·
                  refine ⟨19306675432483059986549261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12871116954988706657699507 19306675432483059986549261)
                  ·
                    refine ⟨7240003287181147494955973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19306675432483059986549261 7240003287181147494955973)
                    ·
                      refine ⟨1357500616346465155304245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7240003287181147494955973 1357500616346465155304245)
                      ·
                        rfl

theorem cell23_2643723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 4].length) (baseStart_2643723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643723 prefixEnd_2643723 := by exact prefixLift 2643723
  have htrace : WordTrace (prefixWord ++ tailWord_2643723) baseStart_2643723 baseEnd_2643723 := by
    simpa [prefixWord, tailWord_2643723, baseEnd_2643723] using wordTrace_append hprefix tailTrace_2643723
  have hstable : (prefixWord ++ tailWord_2643723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643723).length < 2 ^ (prefixWord ++ tailWord_2643723).sum := by decide
  have hdescent : baseEnd_2643723 < baseStart_2643723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643740 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2643740 : Nat := 118140960795 + 2643740 * 2 ^ 59
def prefixEnd_2643740 : Nat := 4983230072969 + 3 ^ 40 * 2643740 * 2
def baseEnd_2643740 : Nat := 1357509345517591588791667

theorem tailTrace_2643740 : CollatzResearch.WordTrace tailWord_2643740 prefixEnd_2643740 1357509345517591588791667 := by
  unfold tailWord_2643740
  simp only [CollatzResearch.WordTrace]
  refine ⟨48212559721094484845088337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64283412961459313126784449 48212559721094484845088337)
  ·
    refine ⟨36159419790820863633816253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48212559721094484845088337 36159419790820863633816253)
    ·
      refine ⟨13559782421557823862681095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36159419790820863633816253 13559782421557823862681095)
      ·
        refine ⟨20339673632336735794021643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13559782421557823862681095 20339673632336735794021643)
        ·
          refine ⟨30509510448505103691032465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20339673632336735794021643 30509510448505103691032465)
          ·
            refine ⟨22882132836378827768274349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30509510448505103691032465 22882132836378827768274349)
            ·
              refine ⟨8580799813642060413102881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22882132836378827768274349 8580799813642060413102881)
              ·
                refine ⟨6435599860231545309827161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8580799813642060413102881 6435599860231545309827161)
                ·
                  refine ⟨4826699895173658982370371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6435599860231545309827161 4826699895173658982370371)
                  ·
                    refine ⟨7240049842760488473555557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4826699895173658982370371 7240049842760488473555557)
                    ·
                      refine ⟨1357509345517591588791667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7240049842760488473555557 1357509345517591588791667)
                      ·
                        rfl

theorem cell23_2643740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2643740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643740 prefixEnd_2643740 := by exact prefixLift 2643740
  have htrace : WordTrace (prefixWord ++ tailWord_2643740) baseStart_2643740 baseEnd_2643740 := by
    simpa [prefixWord, tailWord_2643740, baseEnd_2643740] using wordTrace_append hprefix tailTrace_2643740
  have hstable : (prefixWord ++ tailWord_2643740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643740).length < 2 ^ (prefixWord ++ tailWord_2643740).sum := by decide
  have hdescent : baseEnd_2643740 < baseStart_2643740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643800 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 5, 5, 2]
def baseStart_2643800 : Nat := 118140960795 + 2643800 * 2 ^ 59
def prefixEnd_2643800 : Nat := 4983230072969 + 3 ^ 40 * 2643800 * 2
def baseEnd_2643800 : Nat := 1357540154356861354041391

theorem tailTrace_2643800 : CollatzResearch.WordTrace tailWord_2643800 prefixEnd_2643800 1357540154356861354041391 := by
  unfold tailWord_2643800
  simp only [CollatzResearch.WordTrace]
  refine ⟨48213653910985799968680427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64284871881314399958240569 48213653910985799968680427)
  ·
    refine ⟨72320480866478699953020641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48213653910985799968680427 72320480866478699953020641)
    ·
      refine ⟨54240360649859024964765481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72320480866478699953020641 54240360649859024964765481)
      ·
        refine ⟨40680270487394268723574111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54240360649859024964765481 40680270487394268723574111)
        ·
          refine ⟨61020405731091403085361167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40680270487394268723574111 61020405731091403085361167)
          ·
            refine ⟨91530608596637104628041751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61020405731091403085361167 91530608596637104628041751)
            ·
              refine ⟨137295912894955656942062627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91530608596637104628041751 137295912894955656942062627)
              ·
                refine ⟨205943869342433485413093941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137295912894955656942062627 205943869342433485413093941)
                ·
                  refine ⟨19307237750853139257477557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205943869342433485413093941 19307237750853139257477557)
                  ·
                    refine ⟨1810053539142481805388521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19307237750853139257477557 1810053539142481805388521)
                    ·
                      refine ⟨1357540154356861354041391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810053539142481805388521 1357540154356861354041391)
                      ·
                        rfl

theorem cell23_2643800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_2643800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643800 prefixEnd_2643800 := by exact prefixLift 2643800
  have htrace : WordTrace (prefixWord ++ tailWord_2643800) baseStart_2643800 baseEnd_2643800 := by
    simpa [prefixWord, tailWord_2643800, baseEnd_2643800] using wordTrace_append hprefix tailTrace_2643800
  have hstable : (prefixWord ++ tailWord_2643800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643800).length < 2 ^ (prefixWord ++ tailWord_2643800).sum := by decide
  have hdescent : baseEnd_2643800 < baseStart_2643800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643840 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 4, 4]
def baseStart_2643840 : Nat := 118140960795 + 2643840 * 2 ^ 59
def prefixEnd_2643840 : Nat := 4983230072969 + 3 ^ 40 * 2643840 * 2
def baseEnd_2643840 : Nat := 452520231194347065847069

theorem tailTrace_2643840 : CollatzResearch.WordTrace tailWord_2643840 prefixEnd_2643840 452520231194347065847069 := by
  unfold tailWord_2643840
  simp only [CollatzResearch.WordTrace]
  refine ⟨48214383370913343384408487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64285844494551124512544649 48214383370913343384408487)
  ·
    refine ⟨72321575056370015076612731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48214383370913343384408487 72321575056370015076612731)
    ·
      refine ⟨108482362584555022614919097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72321575056370015076612731 108482362584555022614919097)
      ·
        refine ⟨81361771938416266961189323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108482362584555022614919097 81361771938416266961189323)
        ·
          refine ⟨122042657907624400441783985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81361771938416266961189323 122042657907624400441783985)
          ·
            refine ⟨91531993430718300331337989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122042657907624400441783985 91531993430718300331337989)
            ·
              refine ⟨17162248768259681312125873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91531993430718300331337989 17162248768259681312125873)
              ·
                refine ⟨12871686576194760984094405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17162248768259681312125873 12871686576194760984094405)
                ·
                  refine ⟨2413441233036517684517701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12871686576194760984094405 2413441233036517684517701)
                  ·
                    refine ⟨452520231194347065847069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2413441233036517684517701 452520231194347065847069)
                    ·
                      rfl

theorem cell23_2643840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 4, 4].length) (baseStart_2643840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643840 prefixEnd_2643840 := by exact prefixLift 2643840
  have htrace : WordTrace (prefixWord ++ tailWord_2643840) baseStart_2643840 baseEnd_2643840 := by
    simpa [prefixWord, tailWord_2643840, baseEnd_2643840] using wordTrace_append hprefix tailTrace_2643840
  have hstable : (prefixWord ++ tailWord_2643840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643840).length < 2 ^ (prefixWord ++ tailWord_2643840).sum := by decide
  have hdescent : baseEnd_2643840 < baseStart_2643840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643857 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 2, 4]
def baseStart_2643857 : Nat := 118140960795 + 2643857 * 2 ^ 59
def prefixEnd_2643857 : Nat := 4983230072969 + 3 ^ 40 * 2643857 * 2
def baseEnd_2643857 : Nat := 452523140918055877009543

theorem tailTrace_2643857 : CollatzResearch.WordTrace tailWord_2643857 prefixEnd_2643857 452523140918055877009543 := by
  unfold tailWord_2643857
  simp only [CollatzResearch.WordTrace]
  refine ⟨96429386782765098672185825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64286257855176732448123883 96429386782765098672185825)
  ·
    refine ⟨72322040087073824004139369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96429386782765098672185825 72322040087073824004139369)
    ·
      refine ⟨54241530065305368003104527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72322040087073824004139369 54241530065305368003104527)
      ·
        refine ⟨81362295097958052004656791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54241530065305368003104527 81362295097958052004656791)
        ·
          refine ⟨122043442646937078006985187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81362295097958052004656791 122043442646937078006985187)
          ·
            refine ⟨183065163970405617010477781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122043442646937078006985187 183065163970405617010477781)
            ·
              refine ⟨4290589780556381648683073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 183065163970405617010477781 4290589780556381648683073)
              ·
                refine ⟨3217942335417286236512305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4290589780556381648683073 3217942335417286236512305)
                ·
                  refine ⟨2413456751562964677384229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3217942335417286236512305 2413456751562964677384229)
                  ·
                    refine ⟨452523140918055877009543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2413456751562964677384229 452523140918055877009543)
                    ·
                      rfl

theorem cell23_2643857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_2643857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643857 prefixEnd_2643857 := by exact prefixLift 2643857
  have htrace : WordTrace (prefixWord ++ tailWord_2643857) baseStart_2643857 baseEnd_2643857 := by
    simpa [prefixWord, tailWord_2643857, baseEnd_2643857] using wordTrace_append hprefix tailTrace_2643857
  have hstable : (prefixWord ++ tailWord_2643857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643857).length < 2 ^ (prefixWord ++ tailWord_2643857).sum := by decide
  have hdescent : baseEnd_2643857 < baseStart_2643857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643874 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2643874 : Nat := 118140960795 + 2643874 * 2 ^ 59
def prefixEnd_2643874 : Nat := 4983230072969 + 3 ^ 40 * 2643874 * 2
def baseEnd_2643874 : Nat := 452526050641764688172017

theorem tailTrace_2643874 : CollatzResearch.WordTrace tailWord_2643874 prefixEnd_2643874 452526050641764688172017 := by
  unfold tailWord_2643874
  simp only [CollatzResearch.WordTrace]
  refine ⟨24107501705925877643888669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64286671215802340383703117 24107501705925877643888669)
  ·
    refine ⟨9040313139722204116458251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24107501705925877643888669 9040313139722204116458251)
    ·
      refine ⟨13560469709583306174687377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040313139722204116458251 13560469709583306174687377)
      ·
        refine ⟨10170352282187479631015533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13560469709583306174687377 10170352282187479631015533)
        ·
          refine ⟨3813882105820304861630825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10170352282187479631015533 3813882105820304861630825)
          ·
            refine ⟨2860411579365228646223119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813882105820304861630825 2860411579365228646223119)
            ·
              refine ⟨4290617369047842969334679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860411579365228646223119 4290617369047842969334679)
              ·
                refine ⟨6435926053571764454002019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290617369047842969334679 6435926053571764454002019)
                ·
                  refine ⟨9653889080357646681003029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6435926053571764454002019 9653889080357646681003029)
                  ·
                    refine ⟨452526050641764688172017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9653889080357646681003029 452526050641764688172017)
                    ·
                      rfl

theorem cell23_2643874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2643874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643874 prefixEnd_2643874 := by exact prefixLift 2643874
  have htrace : WordTrace (prefixWord ++ tailWord_2643874) baseStart_2643874 baseEnd_2643874 := by
    simpa [prefixWord, tailWord_2643874, baseEnd_2643874] using wordTrace_append hprefix tailTrace_2643874
  have hstable : (prefixWord ++ tailWord_2643874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643874).length < 2 ^ (prefixWord ++ tailWord_2643874).sum := by decide
  have hdescent : baseEnd_2643874 < baseStart_2643874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643892 : List Nat := [2, 5, 2, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_2643892 : Nat := 118140960795 + 2643892 * 2 ^ 59
def prefixEnd_2643892 : Nat := 4983230072969 + 3 ^ 40 * 2643892 * 2
def baseEnd_2643892 : Nat := 1357587394577074994090969

theorem tailTrace_2643892 : CollatzResearch.WordTrace tailWord_2643892 prefixEnd_2643892 1357587394577074994090969 := by
  unfold tailWord_2643892
  simp only [CollatzResearch.WordTrace]
  refine ⟨48215331668819149824854965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64287108891758866433139953 48215331668819149824854965)
  ·
    refine ⟨4520187343951795296080153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48215331668819149824854965 4520187343951795296080153)
    ·
      refine ⟨3390140507963846472060115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4520187343951795296080153 3390140507963846472060115)
      ·
        refine ⟨5085210761945769708090173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3390140507963846472060115 5085210761945769708090173)
        ·
          refine ⟨1906954035729663640533815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5085210761945769708090173 1906954035729663640533815)
          ·
            refine ⟨2860431053594495460800723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906954035729663640533815 2860431053594495460800723)
            ·
              refine ⟨4290646580391743191201085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860431053594495460800723 4290646580391743191201085)
              ·
                refine ⟨1608992467646903696700407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4290646580391743191201085 1608992467646903696700407)
                ·
                  refine ⟨2413488701470355545050611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608992467646903696700407 2413488701470355545050611)
                  ·
                    refine ⟨3620233052205533317575917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2413488701470355545050611 3620233052205533317575917)
                    ·
                      refine ⟨1357587394577074994090969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3620233052205533317575917 1357587394577074994090969)
                      ·
                        rfl

theorem cell23_2643892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_2643892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643892 prefixEnd_2643892 := by exact prefixLift 2643892
  have htrace : WordTrace (prefixWord ++ tailWord_2643892) baseStart_2643892 baseEnd_2643892 := by
    simpa [prefixWord, tailWord_2643892, baseEnd_2643892] using wordTrace_append hprefix tailTrace_2643892
  have hstable : (prefixWord ++ tailWord_2643892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643892).length < 2 ^ (prefixWord ++ tailWord_2643892).sum := by decide
  have hdescent : baseEnd_2643892 < baseStart_2643892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643897 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2643897 : Nat := 118140960795 + 2643897 * 2 ^ 59
def prefixEnd_2643897 : Nat := 4983230072969 + 3 ^ 40 * 2643897 * 2
def baseEnd_2643897 : Nat := 1357589961980347474528445

theorem tailTrace_2643897 : CollatzResearch.WordTrace tailWord_2643897 prefixEnd_2643897 1357589961980347474528445 := by
  unfold tailWord_2643897
  simp only [CollatzResearch.WordTrace]
  refine ⟨96430845702620185503641945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64287230468413457002427963 96430845702620185503641945)
  ·
    refine ⟨72323134276965139127731459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96430845702620185503641945 72323134276965139127731459)
    ·
      refine ⟨108484701415447708691597189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72323134276965139127731459 108484701415447708691597189)
      ·
        refine ⟨20340881515396445379674473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108484701415447708691597189 20340881515396445379674473)
        ·
          refine ⟨15255661136547334034755855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20340881515396445379674473 15255661136547334034755855)
          ·
            refine ⟨22883491704821001052133783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15255661136547334034755855 22883491704821001052133783)
            ·
              refine ⟨34325237557231501578200675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22883491704821001052133783 34325237557231501578200675)
              ·
                refine ⟨51487856335847252367301013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34325237557231501578200675 51487856335847252367301013)
                ·
                  refine ⟨2413493265742839954717235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51487856335847252367301013 2413493265742839954717235)
                  ·
                    refine ⟨3620239898614259932075853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2413493265742839954717235 3620239898614259932075853)
                    ·
                      refine ⟨1357589961980347474528445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3620239898614259932075853 1357589961980347474528445)
                      ·
                        rfl

theorem cell23_2643897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2643897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643897 prefixEnd_2643897 := by exact prefixLift 2643897
  have htrace : WordTrace (prefixWord ++ tailWord_2643897) baseStart_2643897 baseEnd_2643897 := by
    simpa [prefixWord, tailWord_2643897, baseEnd_2643897] using wordTrace_append hprefix tailTrace_2643897
  have hstable : (prefixWord ++ tailWord_2643897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643897).length < 2 ^ (prefixWord ++ tailWord_2643897).sum := by decide
  have hdescent : baseEnd_2643897 < baseStart_2643897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643924 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_2643924 : Nat := 118140960795 + 2643924 * 2 ^ 59
def prefixEnd_2643924 : Nat := 4983230072969 + 3 ^ 40 * 2643924 * 2
def baseEnd_2643924 : Nat := 1357603825958018868890821

theorem tailTrace_2643924 : CollatzResearch.WordTrace tailWord_2643924 prefixEnd_2643924 1357603825958018868890821 := by
  unfold tailWord_2643924
  simp only [CollatzResearch.WordTrace]
  refine ⟨48215915236761184557437413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64287886982348246076583217 48215915236761184557437413)
  ·
    refine ⟨9040484106892722104519515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48215915236761184557437413 9040484106892722104519515)
    ·
      refine ⟨13560726160339083156779273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040484106892722104519515 13560726160339083156779273)
      ·
        refine ⟨10170544620254312367584455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13560726160339083156779273 10170544620254312367584455)
        ·
          refine ⟨15255816930381468551376683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10170544620254312367584455 15255816930381468551376683)
          ·
            refine ⟨22883725395572202827065025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15255816930381468551376683 22883725395572202827065025)
            ·
              refine ⟨17162794046679152120298769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22883725395572202827065025 17162794046679152120298769)
              ·
                refine ⟨12872095535009364090224077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17162794046679152120298769 12872095535009364090224077)
                ·
                  refine ⟨4827035825628511533834029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12872095535009364090224077 4827035825628511533834029)
                  ·
                    refine ⟨1810138434610691825187761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4827035825628511533834029 1810138434610691825187761)
                    ·
                      refine ⟨1357603825958018868890821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810138434610691825187761 1357603825958018868890821)
                      ·
                        rfl

theorem cell23_2643924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_2643924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643924 prefixEnd_2643924 := by exact prefixLift 2643924
  have htrace : WordTrace (prefixWord ++ tailWord_2643924) baseStart_2643924 baseEnd_2643924 := by
    simpa [prefixWord, tailWord_2643924, baseEnd_2643924] using wordTrace_append hprefix tailTrace_2643924
  have hstable : (prefixWord ++ tailWord_2643924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643924).length < 2 ^ (prefixWord ++ tailWord_2643924).sum := by decide
  have hdescent : baseEnd_2643924 < baseStart_2643924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2643940 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_2643940 : Nat := 118140960795 + 2643940 * 2 ^ 59
def prefixEnd_2643940 : Nat := 4983230072969 + 3 ^ 40 * 2643940 * 2
def baseEnd_2643940 : Nat := 1357612041648490806290747

theorem tailTrace_2643940 : CollatzResearch.WordTrace tailWord_2643940 prefixEnd_2643940 1357612041648490806290747 := by
  unfold tailWord_2643940
  simp only [CollatzResearch.WordTrace]
  refine ⟨48216207020732201923728637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64288276027642935898304849 48216207020732201923728637)
  ·
    refine ⟨18081077632774575721398239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48216207020732201923728637 18081077632774575721398239)
    ·
      refine ⟨27121616449161863582097359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18081077632774575721398239 27121616449161863582097359)
      ·
        refine ⟨40682424673742795373146039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27121616449161863582097359 40682424673742795373146039)
        ·
          refine ⟨61023637010614193059719059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40682424673742795373146039 61023637010614193059719059)
          ·
            refine ⟨91535455515921289589578589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61023637010614193059719059 91535455515921289589578589)
            ·
              refine ⟨34325795818470483596091971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91535455515921289589578589 34325795818470483596091971)
              ·
                refine ⟨51488693727705725394137957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34325795818470483596091971 51488693727705725394137957)
                ·
                  refine ⟨9654130073944823511400867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51488693727705725394137957 9654130073944823511400867)
                  ·
                    refine ⟨14481195110917235267101301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9654130073944823511400867 14481195110917235267101301)
                    ·
                      refine ⟨1357612041648490806290747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14481195110917235267101301 1357612041648490806290747)
                      ·
                        rfl

theorem cell23_2643940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_2643940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2643940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2643940 prefixEnd_2643940 := by exact prefixLift 2643940
  have htrace : WordTrace (prefixWord ++ tailWord_2643940) baseStart_2643940 baseEnd_2643940 := by
    simpa [prefixWord, tailWord_2643940, baseEnd_2643940] using wordTrace_append hprefix tailTrace_2643940
  have hstable : (prefixWord ++ tailWord_2643940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2643940).length < 2 ^ (prefixWord ++ tailWord_2643940).sum := by decide
  have hdescent : baseEnd_2643940 < baseStart_2643940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2643940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644027 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 3, 6, 2]
def baseStart_2644027 : Nat := 118140960795 + 2644027 * 2 ^ 59
def prefixEnd_2644027 : Nat := 4983230072969 + 3 ^ 40 * 2644027 * 2
def baseEnd_2644027 : Nat := 1357656714465431965902847

theorem tailTrace_2644027 : CollatzResearch.WordTrace tailWord_2644027 prefixEnd_2644027 1357656714465431965902847 := by
  unfold tailWord_2644027
  simp only [CollatzResearch.WordTrace]
  refine ⟨96435587192149217705874335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64290391461432811803916223 96435587192149217705874335)
  ·
    refine ⟨144653380788223826558811503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96435587192149217705874335 144653380788223826558811503)
    ·
      refine ⟨216980071182335739838217255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144653380788223826558811503 216980071182335739838217255)
      ·
        refine ⟨325470106773503609757325883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216980071182335739838217255 325470106773503609757325883)
        ·
          refine ⟨488205160160255414635988825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325470106773503609757325883 488205160160255414635988825)
          ·
            refine ⟨366153870120191560976991619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488205160160255414635988825 366153870120191560976991619)
            ·
              refine ⟨549230805180287341465487429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366153870120191560976991619 549230805180287341465487429)
              ·
                refine ⟨102980775971303876524778893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 549230805180287341465487429 102980775971303876524778893)
                ·
                  refine ⟨38617790989238953696792085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102980775971303876524778893 38617790989238953696792085)
                  ·
                    refine ⟨1810208952620575954537129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38617790989238953696792085 1810208952620575954537129)
                    ·
                      refine ⟨1357656714465431965902847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810208952620575954537129 1357656714465431965902847)
                      ·
                        rfl

theorem cell23_2644027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 6, 2].length) (baseStart_2644027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644027 prefixEnd_2644027 := by exact prefixLift 2644027
  have htrace : WordTrace (prefixWord ++ tailWord_2644027) baseStart_2644027 baseEnd_2644027 := by
    simpa [prefixWord, tailWord_2644027, baseEnd_2644027] using wordTrace_append hprefix tailTrace_2644027
  have hstable : (prefixWord ++ tailWord_2644027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644027).length < 2 ^ (prefixWord ++ tailWord_2644027).sum := by decide
  have hdescent : baseEnd_2644027 < baseStart_2644027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644044 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 2, 4, 2]
def baseStart_2644044 : Nat := 118140960795 + 2644044 * 2 ^ 59
def prefixEnd_2644044 : Nat := 4983230072969 + 3 ^ 40 * 2644044 * 2
def baseEnd_2644044 : Nat := 1357665443636558399390269

theorem tailTrace_2644044 : CollatzResearch.WordTrace tailWord_2644044 prefixEnd_2644044 1357665443636558399390269 := by
  unfold tailWord_2644044
  simp only [CollatzResearch.WordTrace]
  refine ⟨48218103616543814804621593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64290804822058419739495457 48218103616543814804621593)
  ·
    refine ⟨36163577712407861103466195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48218103616543814804621593 36163577712407861103466195)
    ·
      refine ⟨54245366568611791655199293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36163577712407861103466195 54245366568611791655199293)
      ·
        refine ⟨20342012463229421870699735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54245366568611791655199293 20342012463229421870699735)
        ·
          refine ⟨30513018694844132806049603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20342012463229421870699735 30513018694844132806049603)
          ·
            refine ⟨45769528042266199209074405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30513018694844132806049603 45769528042266199209074405)
            ·
              refine ⟨8581786507924912351701451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45769528042266199209074405 8581786507924912351701451)
              ·
                refine ⟨12872679761887368527552177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8581786507924912351701451 12872679761887368527552177)
                ·
                  refine ⟨9654509821415526395664133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12872679761887368527552177 9654509821415526395664133)
                  ·
                    refine ⟨1810220591515411199187025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9654509821415526395664133 1810220591515411199187025)
                    ·
                      refine ⟨1357665443636558399390269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810220591515411199187025 1357665443636558399390269)
                      ·
                        rfl

theorem cell23_2644044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_2644044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644044 prefixEnd_2644044 := by exact prefixLift 2644044
  have htrace : WordTrace (prefixWord ++ tailWord_2644044) baseStart_2644044 baseEnd_2644044 := by
    simpa [prefixWord, tailWord_2644044, baseEnd_2644044] using wordTrace_append hprefix tailTrace_2644044
  have hstable : (prefixWord ++ tailWord_2644044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644044).length < 2 ^ (prefixWord ++ tailWord_2644044).sum := by decide
  have hdescent : baseEnd_2644044 < baseStart_2644044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644047 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 3]
def baseStart_2644047 : Nat := 118140960795 + 2644047 * 2 ^ 59
def prefixEnd_2644047 : Nat := 4983230072969 + 3 ^ 40 * 2644047 * 2
def baseEnd_2644047 : Nat := 1357666984078521887652755

theorem tailTrace_2644047 : CollatzResearch.WordTrace tailWord_2644047 prefixEnd_2644047 1357666984078521887652755 := by
  unfold tailWord_2644047
  simp only [CollatzResearch.WordTrace]
  refine ⟨96436316652076761121602395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64290877768051174081068263 96436316652076761121602395)
  ·
    refine ⟨144654474978115141682403593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96436316652076761121602395 144654474978115141682403593)
    ·
      refine ⟨108490856233586356261802695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144654474978115141682403593 108490856233586356261802695)
      ·
        refine ⟨162736284350379534392704043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108490856233586356261802695 162736284350379534392704043)
        ·
          refine ⟨244104426525569301589056065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162736284350379534392704043 244104426525569301589056065)
          ·
            refine ⟨183078319894176976191792049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244104426525569301589056065 183078319894176976191792049)
            ·
              refine ⟨137308739920632732143844037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183078319894176976191792049 137308739920632732143844037)
              ·
                refine ⟨25745388735118637276970757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137308739920632732143844037 25745388735118637276970757)
                ·
                  refine ⟨4827260387834744489432017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25745388735118637276970757 4827260387834744489432017)
                  ·
                    refine ⟨3620445290876058367074013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4827260387834744489432017 3620445290876058367074013)
                    ·
                      refine ⟨1357666984078521887652755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3620445290876058367074013 1357666984078521887652755)
                      ·
                        rfl

theorem cell23_2644047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_2644047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644047 prefixEnd_2644047 := by exact prefixLift 2644047
  have htrace : WordTrace (prefixWord ++ tailWord_2644047) baseStart_2644047 baseEnd_2644047 := by
    simpa [prefixWord, tailWord_2644047, baseEnd_2644047] using wordTrace_append hprefix tailTrace_2644047
  have hstable : (prefixWord ++ tailWord_2644047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644047).length < 2 ^ (prefixWord ++ tailWord_2644047).sum := by decide
  have hdescent : baseEnd_2644047 < baseStart_2644047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644062 : List Nat := [4, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2644062 : Nat := 118140960795 + 2644062 * 2 ^ 59
def prefixEnd_2644062 : Nat := 4983230072969 + 3 ^ 40 * 2644062 * 2
def baseEnd_2644062 : Nat := 150852742920926592107243

theorem tailTrace_2644062 : CollatzResearch.WordTrace tailWord_2644062 prefixEnd_2644062 150852742920926592107243 := by
  unfold tailWord_2644062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054607968377802335424805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64291242498014945788932293 12054607968377802335424805)
  ·
    refine ⟨2260238994070837937892151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12054607968377802335424805 2260238994070837937892151)
    ·
      refine ⟨3390358491106256906838227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260238994070837937892151 3390358491106256906838227)
      ·
        refine ⟨5085537736659385360257341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3390358491106256906838227 5085537736659385360257341)
        ·
          refine ⟨1907076651247269510096503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5085537736659385360257341 1907076651247269510096503)
          ·
            refine ⟨2860614976870904265144755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907076651247269510096503 2860614976870904265144755)
            ·
              refine ⟨4290922465306356397717133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860614976870904265144755 4290922465306356397717133)
              ·
                refine ⟨1609095924489883649143925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4290922465306356397717133 1609095924489883649143925)
                ·
                  refine ⟨150852742920926592107243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1609095924489883649143925 150852742920926592107243)
                  ·
                    rfl

theorem cell23_2644062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2644062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644062 prefixEnd_2644062 := by exact prefixLift 2644062
  have htrace : WordTrace (prefixWord ++ tailWord_2644062) baseStart_2644062 baseEnd_2644062 := by
    simpa [prefixWord, tailWord_2644062, baseEnd_2644062] using wordTrace_append hprefix tailTrace_2644062
  have hstable : (prefixWord ++ tailWord_2644062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644062).length < 2 ^ (prefixWord ++ tailWord_2644062).sum := by decide
  have hdescent : baseEnd_2644062 < baseStart_2644062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644101 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 6]
def baseStart_2644101 : Nat := 118140960795 + 2644101 * 2 ^ 59
def prefixEnd_2644101 : Nat := 4983230072969 + 3 ^ 40 * 2644101 * 2
def baseEnd_2644101 : Nat := 150854968003762741819723

theorem tailTrace_2644101 : CollatzResearch.WordTrace tailWord_2644101 prefixEnd_2644101 150854968003762741819723 := by
  unfold tailWord_2644101
  simp only [CollatzResearch.WordTrace]
  refine ⟨96438286193881128344068157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64292190795920752229378771 96438286193881128344068157)
  ·
    refine ⟨36164357322705423129025559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96438286193881128344068157 36164357322705423129025559)
    ·
      refine ⟨54246535984058134693538339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36164357322705423129025559 54246535984058134693538339)
      ·
        refine ⟨81369803976087202040307509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54246535984058134693538339 81369803976087202040307509)
        ·
          refine ⟨7628419122758175191278829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81369803976087202040307509 7628419122758175191278829)
          ·
            refine ⟨2860657171034315696729561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7628419122758175191278829 2860657171034315696729561)
            ·
              refine ⟨2145492878275736772547171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860657171034315696729561 2145492878275736772547171)
              ·
                refine ⟨3218239317413605158820757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145492878275736772547171 3218239317413605158820757)
                ·
                  refine ⟨150854968003762741819723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3218239317413605158820757 150854968003762741819723)
                  ·
                    rfl

theorem cell23_2644101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_2644101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644101 prefixEnd_2644101 := by exact prefixLift 2644101
  have htrace : WordTrace (prefixWord ++ tailWord_2644101) baseStart_2644101 baseEnd_2644101 := by
    simpa [prefixWord, tailWord_2644101, baseEnd_2644101] using wordTrace_append hprefix tailTrace_2644101
  have hstable : (prefixWord ++ tailWord_2644101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644101).length < 2 ^ (prefixWord ++ tailWord_2644101).sum := by decide
  have hdescent : baseEnd_2644101 < baseStart_2644101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644114 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2644114 : Nat := 118140960795 + 2644114 * 2 ^ 59
def prefixEnd_2644114 : Nat := 4983230072969 + 3 ^ 40 * 2644114 * 2
def baseEnd_2644114 : Nat := 452567129094124375171649

theorem tailTrace_2644114 : CollatzResearch.WordTrace tailWord_2644114 prefixEnd_2644114 452567129094124375171649 := by
  unfold tailWord_2644114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24109690085708507891072849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64292506895222687709527597 24109690085708507891072849)
  ·
    refine ⟨18082267564281380918304637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24109690085708507891072849 18082267564281380918304637)
    ·
      refine ⟨6780850336605517844364239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18082267564281380918304637 6780850336605517844364239)
      ·
        refine ⟨10171275504908276766546359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6780850336605517844364239 10171275504908276766546359)
        ·
          refine ⟨15256913257362415149819539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10171275504908276766546359 15256913257362415149819539)
          ·
            refine ⟨22885369886043622724729309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15256913257362415149819539 22885369886043622724729309)
            ·
              refine ⟨8582013707266358521773491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22885369886043622724729309 8582013707266358521773491)
              ·
                refine ⟨12873020560899537782660237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8582013707266358521773491 12873020560899537782660237)
                ·
                  refine ⟨4827382710337326668497589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12873020560899537782660237 4827382710337326668497589)
                  ·
                    refine ⟨452567129094124375171649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4827382710337326668497589 452567129094124375171649)
                    ·
                      rfl

theorem cell23_2644114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2644114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644114 prefixEnd_2644114 := by exact prefixLift 2644114
  have htrace : WordTrace (prefixWord ++ tailWord_2644114) baseStart_2644114 baseEnd_2644114 := by
    simpa [prefixWord, tailWord_2644114, baseEnd_2644114] using wordTrace_append hprefix tailTrace_2644114
  have hstable : (prefixWord ++ tailWord_2644114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644114).length < 2 ^ (prefixWord ++ tailWord_2644114).sum := by decide
  have hdescent : baseEnd_2644114 < baseStart_2644114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644145 : List Nat := [1, 2, 2, 5, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2644145 : Nat := 118140960795 + 2644145 * 2 ^ 59
def prefixEnd_2644145 : Nat := 4983230072969 + 3 ^ 40 * 2644145 * 2
def baseEnd_2644145 : Nat := 1357717305182662504227305

theorem tailTrace_2644145 : CollatzResearch.WordTrace tailWord_2644145 prefixEnd_2644145 1357717305182662504227305 := by
  unfold tailWord_2644145
  simp only [CollatzResearch.WordTrace]
  refine ⟨96439891005721723858669889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64293260670481149239113259 96439891005721723858669889)
  ·
    refine ⟨72329918254291292894002417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96439891005721723858669889 72329918254291292894002417)
    ·
      refine ⟨54247438690718469670501813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72329918254291292894002417 54247438690718469670501813)
      ·
        refine ⟨5085697377254856531609545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54247438690718469670501813 5085697377254856531609545)
        ·
          refine ⟨3814273032941142398707159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5085697377254856531609545 3814273032941142398707159)
          ·
            refine ⟨5721409549411713598060739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3814273032941142398707159 5721409549411713598060739)
            ·
              refine ⟨8582114324117570397091109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5721409549411713598060739 8582114324117570397091109)
              ·
                refine ⟨1609146435772044449454583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8582114324117570397091109 1609146435772044449454583)
                ·
                  refine ⟨2413719653658066674181875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609146435772044449454583 2413719653658066674181875)
                  ·
                    refine ⟨3620579480487100011272813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2413719653658066674181875 3620579480487100011272813)
                    ·
                      refine ⟨1357717305182662504227305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3620579480487100011272813 1357717305182662504227305)
                      ·
                        rfl

theorem cell23_2644145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2644145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644145 prefixEnd_2644145 := by exact prefixLift 2644145
  have htrace : WordTrace (prefixWord ++ tailWord_2644145) baseStart_2644145 baseEnd_2644145 := by
    simpa [prefixWord, tailWord_2644145, baseEnd_2644145] using wordTrace_append hprefix tailTrace_2644145
  have hstable : (prefixWord ++ tailWord_2644145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644145).length < 2 ^ (prefixWord ++ tailWord_2644145).sum := by decide
  have hdescent : baseEnd_2644145 < baseStart_2644145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644147 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 4]
def baseStart_2644147 : Nat := 118140960795 + 2644147 * 2 ^ 59
def prefixEnd_2644147 : Nat := 4983230072969 + 3 ^ 40 * 2644147 * 2
def baseEnd_2644147 : Nat := 1357718332143971496402295

theorem tailTrace_2644147 : CollatzResearch.WordTrace tailWord_2644147 prefixEnd_2644147 1357718332143971496402295 := by
  unfold tailWord_2644147
  simp only [CollatzResearch.WordTrace]
  refine ⟨96439963951714478200242695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64293309301142985466828463 96439963951714478200242695)
  ·
    refine ⟨144659945927571717300364043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96439963951714478200242695 144659945927571717300364043)
    ·
      refine ⟨216989918891357575950546065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144659945927571717300364043 216989918891357575950546065)
      ·
        refine ⟨162742439168518181962909549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216989918891357575950546065 162742439168518181962909549)
        ·
          refine ⟨61028414688194318236091081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162742439168518181962909549 61028414688194318236091081)
          ·
            refine ⟨45771311016145738677068311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61028414688194318236091081 45771311016145738677068311)
            ·
              refine ⟨68656966524218608015602467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45771311016145738677068311 68656966524218608015602467)
              ·
                refine ⟨102985449786327912023403701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68656966524218608015602467 102985449786327912023403701)
                ·
                  refine ⟨9654885917468241752194097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102985449786327912023403701 9654885917468241752194097)
                  ·
                    refine ⟨7241164438101181314145573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9654885917468241752194097 7241164438101181314145573)
                    ·
                      refine ⟨1357718332143971496402295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7241164438101181314145573 1357718332143971496402295)
                      ·
                        rfl

theorem cell23_2644147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_2644147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644147 prefixEnd_2644147 := by exact prefixLift 2644147
  have htrace : WordTrace (prefixWord ++ tailWord_2644147) baseStart_2644147 baseEnd_2644147 := by
    simpa [prefixWord, tailWord_2644147, baseEnd_2644147] using wordTrace_append hprefix tailTrace_2644147
  have hstable : (prefixWord ++ tailWord_2644147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644147).length < 2 ^ (prefixWord ++ tailWord_2644147).sum := by decide
  have hdescent : baseEnd_2644147 < baseStart_2644147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644154 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_2644154 : Nat := 118140960795 + 2644154 * 2 ^ 59
def prefixEnd_2644154 : Nat := 4983230072969 + 3 ^ 40 * 2644154 * 2
def baseEnd_2644154 : Nat := 1357721926508552969014763

theorem tailTrace_2644154 : CollatzResearch.WordTrace tailWord_2644154 prefixEnd_2644154 1357721926508552969014763 := by
  unfold tailWord_2644154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24110054815672279598936879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64293479508459412263831677 24110054815672279598936879)
  ·
    refine ⟨36165082223508419398405319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24110054815672279598936879 36165082223508419398405319)
    ·
      refine ⟨54247623335262629097607979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36165082223508419398405319 54247623335262629097607979)
      ·
        refine ⟨81371435002893943646411969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54247623335262629097607979 81371435002893943646411969)
        ·
          refine ⟨61028576252170457734808977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81371435002893943646411969 61028576252170457734808977)
          ·
            refine ⟨45771432189127843301106733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61028576252170457734808977 45771432189127843301106733)
            ·
              refine ⟨17164287070922941237915025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45771432189127843301106733 17164287070922941237915025)
              ·
                refine ⟨12873215303192205928436269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17164287070922941237915025 12873215303192205928436269)
                ·
                  refine ⟨4827455738697077223163601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12873215303192205928436269 4827455738697077223163601)
                  ·
                    refine ⟨3620591804022807917372701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4827455738697077223163601 3620591804022807917372701)
                    ·
                      refine ⟨1357721926508552969014763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3620591804022807917372701 1357721926508552969014763)
                      ·
                        rfl

theorem cell23_2644154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_2644154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644154 prefixEnd_2644154 := by exact prefixLift 2644154
  have htrace : WordTrace (prefixWord ++ tailWord_2644154) baseStart_2644154 baseEnd_2644154 := by
    simpa [prefixWord, tailWord_2644154, baseEnd_2644154] using wordTrace_append hprefix tailTrace_2644154
  have hstable : (prefixWord ++ tailWord_2644154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644154).length < 2 ^ (prefixWord ++ tailWord_2644154).sum := by decide
  have hdescent : baseEnd_2644154 < baseStart_2644154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644172 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2644172 : Nat := 118140960795 + 2644172 * 2 ^ 59
def prefixEnd_2644172 : Nat := 4983230072969 + 3 ^ 40 * 2644172 * 2
def baseEnd_2644172 : Nat := 1357731169160333898589681

theorem tailTrace_2644172 : CollatzResearch.WordTrace tailWord_2644172 prefixEnd_2644172 1357731169160333898589681 := by
  unfold tailWord_2644172
  simp only [CollatzResearch.WordTrace]
  refine ⟨48220437888311953734951385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64293917184415938313268513 48220437888311953734951385)
  ·
    refine ⟨36165328416233965301213539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48220437888311953734951385 36165328416233965301213539)
    ·
      refine ⟨54247992624350947951820309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36165328416233965301213539 54247992624350947951820309)
      ·
        refine ⟨2542874654266450685241577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54247992624350947951820309 2542874654266450685241577)
        ·
          refine ⟨1907155990699838013931183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2542874654266450685241577 1907155990699838013931183)
          ·
            refine ⟨2860733986049757020896775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907155990699838013931183 2860733986049757020896775)
            ·
              refine ⟨4291100979074635531345163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860733986049757020896775 4291100979074635531345163)
              ·
                refine ⟨6436651468611953297017745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291100979074635531345163 6436651468611953297017745)
                ·
                  refine ⟨4827488601458964972763309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6436651468611953297017745 4827488601458964972763309)
                  ·
                    refine ⟨1810308225547111864786241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4827488601458964972763309 1810308225547111864786241)
                    ·
                      refine ⟨1357731169160333898589681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810308225547111864786241 1357731169160333898589681)
                      ·
                        rfl

theorem cell23_2644172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2644172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644172 prefixEnd_2644172 := by exact prefixLift 2644172
  have htrace : WordTrace (prefixWord ++ tailWord_2644172) baseStart_2644172 baseEnd_2644172 := by
    simpa [prefixWord, tailWord_2644172, baseEnd_2644172] using wordTrace_append hprefix tailTrace_2644172
  have hstable : (prefixWord ++ tailWord_2644172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644172).length < 2 ^ (prefixWord ++ tailWord_2644172).sum := by decide
  have hdescent : baseEnd_2644172 < baseStart_2644172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644195 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 2, 4]
def baseStart_2644195 : Nat := 118140960795 + 2644195 * 2 ^ 59
def prefixEnd_2644195 : Nat := 4983230072969 + 3 ^ 40 * 2644195 * 2
def baseEnd_2644195 : Nat := 452580993071795769534025

theorem tailTrace_2644195 : CollatzResearch.WordTrace tailWord_2644195 prefixEnd_2644195 452580993071795769534025 := by
  unfold tailWord_2644195
  simp only [CollatzResearch.WordTrace]
  refine ⟨96441714655540582397990039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64294476437027054931993359 96441714655540582397990039)
  ·
    refine ⟨144662571983310873596985059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96441714655540582397990039 144662571983310873596985059)
    ·
      refine ⟨216993857974966310395477589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144662571983310873596985059 216993857974966310395477589)
      ·
        refine ⟨2542896773144136449947003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 216993857974966310395477589 2542896773144136449947003)
        ·
          refine ⟨3814345159716204674920505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542896773144136449947003 3814345159716204674920505)
          ·
            refine ⟨2860758869787153506190379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3814345159716204674920505 2860758869787153506190379)
            ·
              refine ⟨4291138304680730259285569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860758869787153506190379 4291138304680730259285569)
              ·
                refine ⟨3218353728510547694464177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4291138304680730259285569 3218353728510547694464177)
                ·
                  refine ⟨2413765296382910770848133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3218353728510547694464177 2413765296382910770848133)
                  ·
                    refine ⟨452580993071795769534025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2413765296382910770848133 452580993071795769534025)
                    ·
                      rfl

theorem cell23_2644195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 4].length) (baseStart_2644195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644195 prefixEnd_2644195 := by exact prefixLift 2644195
  have htrace : WordTrace (prefixWord ++ tailWord_2644195) baseStart_2644195 baseEnd_2644195 := by
    simpa [prefixWord, tailWord_2644195, baseEnd_2644195] using wordTrace_append hprefix tailTrace_2644195
  have hstable : (prefixWord ++ tailWord_2644195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644195).length < 2 ^ (prefixWord ++ tailWord_2644195).sum := by decide
  have hdescent : baseEnd_2644195 < baseStart_2644195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644217 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 1, 8]
def baseStart_2644217 : Nat := 118140960795 + 2644217 * 2 ^ 59
def prefixEnd_2644217 : Nat := 4983230072969 + 3 ^ 40 * 2644217 * 2
def baseEnd_2644217 : Nat := 452584758596595407508991

theorem tailTrace_2644217 : CollatzResearch.WordTrace tailWord_2644217 prefixEnd_2644217 452584758596595407508991 := by
  unfold tailWord_2644217
  simp only [CollatzResearch.WordTrace]
  refine ⟨96442517061460880155290905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64295011374307253436860603 96442517061460880155290905)
  ·
    refine ⟨72331887796095660116468179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96442517061460880155290905 72331887796095660116468179)
    ·
      refine ⟨108497831694143490174702269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72331887796095660116468179 108497831694143490174702269)
      ·
        refine ⟨40686686885303808815513351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108497831694143490174702269 40686686885303808815513351)
        ·
          refine ⟨61030030327955713223270027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40686686885303808815513351 61030030327955713223270027)
          ·
            refine ⟨91545045491933569834905041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61030030327955713223270027 91545045491933569834905041)
            ·
              refine ⟨68658784118950177376178781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91545045491933569834905041 68658784118950177376178781)
              ·
                refine ⟨25747044044606316516067043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68658784118950177376178781 25747044044606316516067043)
                ·
                  refine ⟨38620566066909474774100565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25747044044606316516067043 38620566066909474774100565)
                  ·
                    refine ⟨452584758596595407508991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38620566066909474774100565 452584758596595407508991)
                    ·
                      rfl

theorem cell23_2644217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_2644217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644217 prefixEnd_2644217 := by exact prefixLift 2644217
  have htrace : WordTrace (prefixWord ++ tailWord_2644217) baseStart_2644217 baseEnd_2644217 := by
    simpa [prefixWord, tailWord_2644217, baseEnd_2644217] using wordTrace_append hprefix tailTrace_2644217
  have hstable : (prefixWord ++ tailWord_2644217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644217).length < 2 ^ (prefixWord ++ tailWord_2644217).sum := by decide
  have hdescent : baseEnd_2644217 < baseStart_2644217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644269 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_2644269 : Nat := 118140960795 + 2644269 * 2 ^ 59
def prefixEnd_2644269 : Nat := 4983230072969 + 3 ^ 40 * 2644269 * 2
def baseEnd_2644269 : Nat := 1357780976783820019076735

theorem tailTrace_2644269 : CollatzResearch.WordTrace tailWord_2644269 prefixEnd_2644269 1357780976783820019076735 := by
  unfold tailWord_2644269
  simp only [CollatzResearch.WordTrace]
  refine ⟨96444413657272493036183861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64296275771514995357455907 96444413657272493036183861)
  ·
    refine ⟨9041663780369296222142237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96444413657272493036183861 9041663780369296222142237)
    ·
      refine ⟨3390623917638486083303339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9041663780369296222142237 3390623917638486083303339)
      ·
        refine ⟨5085935876457729124955009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3390623917638486083303339 5085935876457729124955009)
        ·
          refine ⟨3814451907343296843716257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5085935876457729124955009 3814451907343296843716257)
          ·
            refine ⟨2860838930507472632787193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3814451907343296843716257 2860838930507472632787193)
            ·
              refine ⟨2145629197880604474590395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860838930507472632787193 2145629197880604474590395)
              ·
                refine ⟨3218443796820906711885593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145629197880604474590395 3218443796820906711885593)
                ·
                  refine ⟨2413832847615680033914195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3218443796820906711885593 2413832847615680033914195)
                  ·
                    refine ⟨3620749271423520050871293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2413832847615680033914195 3620749271423520050871293)
                    ·
                      refine ⟨1357780976783820019076735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3620749271423520050871293 1357780976783820019076735)
                      ·
                        rfl

theorem cell23_2644269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_2644269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644269 prefixEnd_2644269 := by exact prefixLift 2644269
  have htrace : WordTrace (prefixWord ++ tailWord_2644269) baseStart_2644269 baseEnd_2644269 := by
    simpa [prefixWord, tailWord_2644269, baseEnd_2644269] using wordTrace_append hprefix tailTrace_2644269
  have hstable : (prefixWord ++ tailWord_2644269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644269).length < 2 ^ (prefixWord ++ tailWord_2644269).sum := by decide
  have hdescent : baseEnd_2644269 < baseStart_2644269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644304 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_2644304 : Nat := 118140960795 + 2644304 * 2 ^ 59
def prefixEnd_2644304 : Nat := 4983230072969 + 3 ^ 40 * 2644304 * 2
def baseEnd_2644304 : Nat := 1357798948606727382139073

theorem tailTrace_2644304 : CollatzResearch.WordTrace tailWord_2644304 prefixEnd_2644304 1357798948606727382139073 := by
  unfold tailWord_2644304
  simp only [CollatzResearch.WordTrace]
  refine ⟨48222845106072847006853983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64297126808097129342471977 48222845106072847006853983)
  ·
    refine ⟨72334267659109270510280975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48222845106072847006853983 72334267659109270510280975)
    ·
      refine ⟨108501401488663905765421463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72334267659109270510280975 108501401488663905765421463)
      ·
        refine ⟨162752102232995858648132195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108501401488663905765421463 162752102232995858648132195)
        ·
          refine ⟨244128153349493787972198293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162752102232995858648132195 244128153349493787972198293)
          ·
            refine ⟨11443507188257521311196795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 244128153349493787972198293 11443507188257521311196795)
            ·
              refine ⟨17165260782386281966795193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11443507188257521311196795 17165260782386281966795193)
              ·
                refine ⟨12873945586789711475096395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17165260782386281966795193 12873945586789711475096395)
                ·
                  refine ⟨19310918380184567212644593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12873945586789711475096395 19310918380184567212644593)
                  ·
                    refine ⟨14483188785138425409483445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19310918380184567212644593 14483188785138425409483445)
                    ·
                      refine ⟨1357798948606727382139073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14483188785138425409483445 1357798948606727382139073)
                      ·
                        rfl

theorem cell23_2644304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_2644304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644304 prefixEnd_2644304 := by exact prefixLift 2644304
  have htrace : WordTrace (prefixWord ++ tailWord_2644304) baseStart_2644304 baseEnd_2644304 := by
    simpa [prefixWord, tailWord_2644304, baseEnd_2644304] using wordTrace_append hprefix tailTrace_2644304
  have hstable : (prefixWord ++ tailWord_2644304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644304).length < 2 ^ (prefixWord ++ tailWord_2644304).sum := by decide
  have hdescent : baseEnd_2644304 < baseStart_2644304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644314 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_2644314 : Nat := 118140960795 + 2644314 * 2 ^ 59
def prefixEnd_2644314 : Nat := 4983230072969 + 3 ^ 40 * 2644314 * 2
def baseEnd_2644314 : Nat := 1357804083413272343014027

theorem tailTrace_2644314 : CollatzResearch.WordTrace tailWord_2644314 prefixEnd_2644314 1357804083413272343014027 := by
  unfold tailWord_2644314
  simp only [CollatzResearch.WordTrace]
  refine ⟨24111513735527366430392999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64297369961406310481047997 24111513735527366430392999)
  ·
    refine ⟨36167270603291049645589499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24111513735527366430392999 36167270603291049645589499)
    ·
      refine ⟨54250905904936574468384249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36167270603291049645589499 54250905904936574468384249)
      ·
        refine ⟨40688179428702430851288187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54250905904936574468384249 40688179428702430851288187)
        ·
          refine ⟨61032269143053646276932281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40688179428702430851288187 61032269143053646276932281)
          ·
            refine ⟨45774201857290234707699211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61032269143053646276932281 45774201857290234707699211)
            ·
              refine ⟨68661302785935352061548817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45774201857290234707699211 68661302785935352061548817)
              ·
                refine ⟨51495977089451514046161613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68661302785935352061548817 51495977089451514046161613)
                ·
                  refine ⟨19310991408544317767310605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51495977089451514046161613 19310991408544317767310605)
                  ·
                    refine ⟨7241621778204119162741477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19310991408544317767310605 7241621778204119162741477)
                    ·
                      refine ⟨1357804083413272343014027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7241621778204119162741477 1357804083413272343014027)
                      ·
                        rfl

theorem cell23_2644314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_2644314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644314 prefixEnd_2644314 := by exact prefixLift 2644314
  have htrace : WordTrace (prefixWord ++ tailWord_2644314) baseStart_2644314 baseEnd_2644314 := by
    simpa [prefixWord, tailWord_2644314, baseEnd_2644314] using wordTrace_append hprefix tailTrace_2644314
  have hstable : (prefixWord ++ tailWord_2644314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644314).length < 2 ^ (prefixWord ++ tailWord_2644314).sum := by decide
  have hdescent : baseEnd_2644314 < baseStart_2644314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644331 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 2, 4, 2]
def baseStart_2644331 : Nat := 118140960795 + 2644331 * 2 ^ 59
def prefixEnd_2644331 : Nat := 4983230072969 + 3 ^ 40 * 2644331 * 2
def baseEnd_2644331 : Nat := 1357812812584398776501449

theorem tailTrace_2644331 : CollatzResearch.WordTrace tailWord_2644331 prefixEnd_2644331 1357812812584398776501449 := by
  unfold tailWord_2644331
  simp only [CollatzResearch.WordTrace]
  refine ⟨96446674983047877624940847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64297783322031918416627231 96446674983047877624940847)
  ·
    refine ⟨144670012474571816437411271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96446674983047877624940847 144670012474571816437411271)
    ·
      refine ⟨217005018711857724656116907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144670012474571816437411271 217005018711857724656116907)
      ·
        refine ⟨325507528067786586984175361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217005018711857724656116907 325507528067786586984175361)
        ·
          refine ⟨244130646050839940238131521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325507528067786586984175361 244130646050839940238131521)
          ·
            refine ⟨183097984538129955178598641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244130646050839940238131521 183097984538129955178598641)
            ·
              refine ⟨137323488403597466383948981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183097984538129955178598641 137323488403597466383948981)
              ·
                refine ⟨12874077037837262473495217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137323488403597466383948981 12874077037837262473495217)
                ·
                  refine ⟨9655557778377946855121413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12874077037837262473495217 9655557778377946855121413)
                  ·
                    refine ⟨1810417083445865035335265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9655557778377946855121413 1810417083445865035335265)
                    ·
                      refine ⟨1357812812584398776501449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810417083445865035335265 1357812812584398776501449)
                      ·
                        rfl

theorem cell23_2644331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 4, 2].length) (baseStart_2644331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644331 prefixEnd_2644331 := by exact prefixLift 2644331
  have htrace : WordTrace (prefixWord ++ tailWord_2644331) baseStart_2644331 baseEnd_2644331 := by
    simpa [prefixWord, tailWord_2644331, baseEnd_2644331] using wordTrace_append hprefix tailTrace_2644331
  have hstable : (prefixWord ++ tailWord_2644331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644331).length < 2 ^ (prefixWord ++ tailWord_2644331).sum := by decide
  have hdescent : baseEnd_2644331 < baseStart_2644331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644408 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 2, 3, 2]
def baseStart_2644408 : Nat := 118140960795 + 2644408 * 2 ^ 59
def prefixEnd_2644408 : Nat := 4983230072969 + 3 ^ 40 * 2644408 * 2
def baseEnd_2644408 : Nat := 1357852350594794975238595

theorem tailTrace_2644408 : CollatzResearch.WordTrace tailWord_2644408 prefixEnd_2644408 1357852350594794975238595 := by
  unfold tailWord_2644408
  simp only [CollatzResearch.WordTrace]
  refine ⟨48224741701884459887746939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64299655602512613183662585 48224741701884459887746939)
  ·
    refine ⟨72337112552826689831620409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48224741701884459887746939 72337112552826689831620409)
    ·
      refine ⟨54252834414620017373715307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72337112552826689831620409 54252834414620017373715307)
      ·
        refine ⟨81379251621930026060572961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54252834414620017373715307 81379251621930026060572961)
        ·
          refine ⟨61034438716447519545429721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81379251621930026060572961 61034438716447519545429721)
          ·
            refine ⟨45775829037335639659072291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61034438716447519545429721 45775829037335639659072291)
            ·
              refine ⟨68663743556003459488608437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45775829037335639659072291 68663743556003459488608437)
              ·
                refine ⟨6437225958375324327057041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68663743556003459488608437 6437225958375324327057041)
                ·
                  refine ⟨4827919468781493245292781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6437225958375324327057041 4827919468781493245292781)
                  ·
                    refine ⟨1810469800793059966984793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4827919468781493245292781 1810469800793059966984793)
                    ·
                      refine ⟨1357852350594794975238595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810469800793059966984793 1357852350594794975238595)
                      ·
                        rfl

theorem cell23_2644408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_2644408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644408 prefixEnd_2644408 := by exact prefixLift 2644408
  have htrace : WordTrace (prefixWord ++ tailWord_2644408) baseStart_2644408 baseEnd_2644408 := by
    simpa [prefixWord, tailWord_2644408, baseEnd_2644408] using wordTrace_append hprefix tailTrace_2644408
  have hstable : (prefixWord ++ tailWord_2644408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644408).length < 2 ^ (prefixWord ++ tailWord_2644408).sum := by decide
  have hdescent : baseEnd_2644408 < baseStart_2644408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644441 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 5]
def baseStart_2644441 : Nat := 118140960795 + 2644441 * 2 ^ 59
def prefixEnd_2644441 : Nat := 4983230072969 + 3 ^ 40 * 2644441 * 2
def baseEnd_2644441 : Nat := 1357869295456393346125943

theorem tailTrace_2644441 : CollatzResearch.WordTrace tailWord_2644441 prefixEnd_2644441 1357869295456393346125943 := by
  unfold tailWord_2644441
  simp only [CollatzResearch.WordTrace]
  refine ⟨96450687012649366411445177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64300458008432910940963451 96450687012649366411445177)
  ·
    refine ⟨72338015259487024808583883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96450687012649366411445177 72338015259487024808583883)
    ·
      refine ⟨108507022889230537212875825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72338015259487024808583883 108507022889230537212875825)
      ·
        refine ⟨81380267166922902909656869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108507022889230537212875825 81380267166922902909656869)
        ·
          refine ⟨15258800093798044295560663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81380267166922902909656869 15258800093798044295560663)
          ·
            refine ⟨22888200140697066443340995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15258800093798044295560663 22888200140697066443340995)
            ·
              refine ⟨34332300211045599665011493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22888200140697066443340995 34332300211045599665011493)
              ·
                refine ⟨6437306289571049937189655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34332300211045599665011493 6437306289571049937189655)
                ·
                  refine ⟨9655959434356574905784483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6437306289571049937189655 9655959434356574905784483)
                  ·
                    refine ⟨14483939151534862358676725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9655959434356574905784483 14483939151534862358676725)
                    ·
                      refine ⟨1357869295456393346125943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14483939151534862358676725 1357869295456393346125943)
                      ·
                        rfl

theorem cell23_2644441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_2644441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644441 prefixEnd_2644441 := by exact prefixLift 2644441
  have htrace : WordTrace (prefixWord ++ tailWord_2644441) baseStart_2644441 baseEnd_2644441 := by
    simpa [prefixWord, tailWord_2644441, baseEnd_2644441] using wordTrace_append hprefix tailTrace_2644441
  have hstable : (prefixWord ++ tailWord_2644441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644441).length < 2 ^ (prefixWord ++ tailWord_2644441).sum := by decide
  have hdescent : baseEnd_2644441 < baseStart_2644441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644448 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 2, 4]
def baseStart_2644448 : Nat := 118140960795 + 2644448 * 2 ^ 59
def prefixEnd_2644448 : Nat := 4983230072969 + 3 ^ 40 * 2644448 * 2
def baseEnd_2644448 : Nat := 452624296606991606246137

theorem tailTrace_2644448 : CollatzResearch.WordTrace tailWord_2644448 prefixEnd_2644448 452624296606991606246137 := by
  unfold tailWord_2644448
  simp only [CollatzResearch.WordTrace]
  refine ⟨48225471161812003303474999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64300628215749337737966665 48225471161812003303474999)
  ·
    refine ⟨72338206742718004955212499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48225471161812003303474999 72338206742718004955212499)
    ·
      refine ⟨108507310114077007432818749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72338206742718004955212499 108507310114077007432818749)
      ·
        refine ⟨40690241292778877787307031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108507310114077007432818749 40690241292778877787307031)
        ·
          refine ⟨61035361939168316680960547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40690241292778877787307031 61035361939168316680960547)
          ·
            refine ⟨91553042908752475021440821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61035361939168316680960547 91553042908752475021440821)
            ·
              refine ⟨8583097772695544533260077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91553042908752475021440821 8583097772695544533260077)
              ·
                refine ⟨3218661664760829199972529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8583097772695544533260077 3218661664760829199972529)
                ·
                  refine ⟨2413996248570621899979397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3218661664760829199972529 2413996248570621899979397)
                  ·
                    refine ⟨452624296606991606246137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2413996248570621899979397 452624296606991606246137)
                    ·
                      rfl

theorem cell23_2644448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2, 4].length) (baseStart_2644448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644448 prefixEnd_2644448 := by exact prefixLift 2644448
  have htrace : WordTrace (prefixWord ++ tailWord_2644448) baseStart_2644448 baseEnd_2644448 := by
    simpa [prefixWord, tailWord_2644448, baseEnd_2644448] using wordTrace_append hprefix tailTrace_2644448
  have hstable : (prefixWord ++ tailWord_2644448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644448).length < 2 ^ (prefixWord ++ tailWord_2644448).sum := by decide
  have hdescent : baseEnd_2644448 < baseStart_2644448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644455 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_2644455 : Nat := 118140960795 + 2644455 * 2 ^ 59
def prefixEnd_2644455 : Nat := 4983230072969 + 3 ^ 40 * 2644455 * 2
def baseEnd_2644455 : Nat := 1357876484185556291350879

theorem tailTrace_2644455 : CollatzResearch.WordTrace tailWord_2644455 prefixEnd_2644455 1357876484185556291350879 := by
  unfold tailWord_2644455
  simp only [CollatzResearch.WordTrace]
  refine ⟨96451197634598646802454819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64300798423065764534969879 96451197634598646802454819)
  ·
    refine ⟨144676796451897970203682229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96451197634598646802454819 144676796451897970203682229)
    ·
      refine ⟨13563449667365434706595209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144676796451897970203682229 13563449667365434706595209)
      ·
        refine ⟨10172587250524076029946407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13563449667365434706595209 10172587250524076029946407)
        ·
          refine ⟨15258880875786114044919611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10172587250524076029946407 15258880875786114044919611)
          ·
            refine ⟨22888321313679171067379417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15258880875786114044919611 22888321313679171067379417)
            ·
              refine ⟨17166240985259378300534563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22888321313679171067379417 17166240985259378300534563)
              ·
                refine ⟨25749361477889067450801845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17166240985259378300534563 25749361477889067450801845)
                ·
                  refine ⟨2414002638552100073512673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25749361477889067450801845 2414002638552100073512673)
                  ·
                    refine ⟨1810501978914075055134505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2414002638552100073512673 1810501978914075055134505)
                    ·
                      refine ⟨1357876484185556291350879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810501978914075055134505 1357876484185556291350879)
                      ·
                        rfl

theorem cell23_2644455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_2644455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644455 prefixEnd_2644455 := by exact prefixLift 2644455
  have htrace : WordTrace (prefixWord ++ tailWord_2644455) baseStart_2644455 baseEnd_2644455 := by
    simpa [prefixWord, tailWord_2644455, baseEnd_2644455] using wordTrace_append hprefix tailTrace_2644455
  have hstable : (prefixWord ++ tailWord_2644455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644455).length < 2 ^ (prefixWord ++ tailWord_2644455).sum := by decide
  have hdescent : baseEnd_2644455 < baseStart_2644455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644472 : List Nat := [2, 1, 2, 1, 1, 4, 2, 5, 1, 2, 2]
def baseStart_2644472 : Nat := 118140960795 + 2644472 * 2 ^ 59
def prefixEnd_2644472 : Nat := 4983230072969 + 3 ^ 40 * 2644472 * 2
def baseEnd_2644472 : Nat := 1357885213356682724838301

theorem tailTrace_2644472 : CollatzResearch.WordTrace tailWord_2644472 prefixEnd_2644472 1357885213356682724838301 := by
  unfold tailWord_2644472
  simp only [CollatzResearch.WordTrace]
  refine ⟨48225908837768529352911835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64301211783691372470549113 48225908837768529352911835)
  ·
    refine ⟨72338863256652794029367753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48225908837768529352911835 72338863256652794029367753)
    ·
      refine ⟨54254147442489595522025815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72338863256652794029367753 54254147442489595522025815)
      ·
        refine ⟨81381221163734393283038723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54254147442489595522025815 81381221163734393283038723)
        ·
          refine ⟨122071831745601589924558085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81381221163734393283038723 122071831745601589924558085)
          ·
            refine ⟨22888468452300298110854641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122071831745601589924558085 22888468452300298110854641)
            ·
              refine ⟨17166351339225223583140981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22888468452300298110854641 17166351339225223583140981)
              ·
                refine ⟨1609345438052364710919467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17166351339225223583140981 1609345438052364710919467)
                ·
                  refine ⟨2414018157078547066379201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609345438052364710919467 2414018157078547066379201)
                  ·
                    refine ⟨1810513617808910299784401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2414018157078547066379201 1810513617808910299784401)
                    ·
                      refine ⟨1357885213356682724838301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810513617808910299784401 1357885213356682724838301)
                      ·
                        rfl

theorem cell23_2644472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_2644472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644472 prefixEnd_2644472 := by exact prefixLift 2644472
  have htrace : WordTrace (prefixWord ++ tailWord_2644472) baseStart_2644472 baseEnd_2644472 := by
    simpa [prefixWord, tailWord_2644472, baseEnd_2644472] using wordTrace_append hprefix tailTrace_2644472
  have hstable : (prefixWord ++ tailWord_2644472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644472).length < 2 ^ (prefixWord ++ tailWord_2644472).sum := by decide
  have hdescent : baseEnd_2644472 < baseStart_2644472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644491 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 2, 7]
def baseStart_2644491 : Nat := 118140960795 + 2644491 * 2 ^ 59
def prefixEnd_2644491 : Nat := 4983230072969 + 3 ^ 40 * 2644491 * 2
def baseEnd_2644491 : Nat := 452631656496372716833571

theorem tailTrace_2644491 : CollatzResearch.WordTrace tailWord_2644491 prefixEnd_2644491 452631656496372716833571 := by
  unfold tailWord_2644491
  simp only [CollatzResearch.WordTrace]
  refine ⟨96452510662468224950765327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64301673774978816633843551 96452510662468224950765327)
  ·
    refine ⟨144678765993702337426147991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96452510662468224950765327 144678765993702337426147991)
    ·
      refine ⟨217018148990553506139221987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144678765993702337426147991 217018148990553506139221987)
      ·
        refine ⟨325527223485830259208832981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217018148990553506139221987 325527223485830259208832981)
        ·
          refine ⟨7629544300449146700207023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 325527223485830259208832981 7629544300449146700207023)
          ·
            refine ⟨11444316450673720050310535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7629544300449146700207023 11444316450673720050310535)
            ·
              refine ⟨17166474676010580075465803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11444316450673720050310535 17166474676010580075465803)
              ·
                refine ⟨25749712014015870113198705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17166474676010580075465803 25749712014015870113198705)
                ·
                  refine ⟨19312284010511902584899029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25749712014015870113198705 19312284010511902584899029)
                  ·
                    refine ⟨452631656496372716833571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19312284010511902584899029 452631656496372716833571)
                    ·
                      rfl

theorem cell23_2644491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 7].length) (baseStart_2644491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644491 prefixEnd_2644491 := by exact prefixLift 2644491
  have htrace : WordTrace (prefixWord ++ tailWord_2644491) baseStart_2644491 baseEnd_2644491 := by
    simpa [prefixWord, tailWord_2644491, baseEnd_2644491] using wordTrace_append hprefix tailTrace_2644491
  have hstable : (prefixWord ++ tailWord_2644491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644491).length < 2 ^ (prefixWord ++ tailWord_2644491).sum := by decide
  have hdescent : baseEnd_2644491 < baseStart_2644491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644511 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_2644511 : Nat := 118140960795 + 2644511 * 2 ^ 59
def prefixEnd_2644511 : Nat := 4983230072969 + 3 ^ 40 * 2644511 * 2
def baseEnd_2644511 : Nat := 1357905239102208072250621

theorem tailTrace_2644511 : CollatzResearch.WordTrace tailWord_2644511 prefixEnd_2644511 1357905239102208072250621 := by
  unfold tailWord_2644511
  simp only [CollatzResearch.WordTrace]
  refine ⟨96453240122395768366493387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64302160081597178910995591 96453240122395768366493387)
  ·
    refine ⟨144679860183593652549740081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96453240122395768366493387 144679860183593652549740081)
    ·
      refine ⟨108509895137695239412305061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144679860183593652549740081 108509895137695239412305061)
      ·
        refine ⟨20345605338317857389807199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108509895137695239412305061 20345605338317857389807199)
        ·
          refine ⟨30518408007476786084710799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20345605338317857389807199 30518408007476786084710799)
          ·
            refine ⟨45777612011215179127066199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30518408007476786084710799 45777612011215179127066199)
            ·
              refine ⟨68666418016822768690599299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45777612011215179127066199 68666418016822768690599299)
              ·
                refine ⟨102999627025234153035898949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68666418016822768690599299 102999627025234153035898949)
                ·
                  refine ⟨19312430067231403694231053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102999627025234153035898949 19312430067231403694231053)
                  ·
                    refine ⟨7242161275211776385336645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19312430067231403694231053 7242161275211776385336645)
                    ·
                      refine ⟨1357905239102208072250621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7242161275211776385336645 1357905239102208072250621)
                      ·
                        rfl

theorem cell23_2644511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_2644511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644511 prefixEnd_2644511 := by exact prefixLift 2644511
  have htrace : WordTrace (prefixWord ++ tailWord_2644511) baseStart_2644511 baseEnd_2644511 := by
    simpa [prefixWord, tailWord_2644511, baseEnd_2644511] using wordTrace_append hprefix tailTrace_2644511
  have hstable : (prefixWord ++ tailWord_2644511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644511).length < 2 ^ (prefixWord ++ tailWord_2644511).sum := by decide
  have hdescent : baseEnd_2644511 < baseStart_2644511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644515 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 3, 3, 2]
def baseStart_2644515 : Nat := 118140960795 + 2644515 * 2 ^ 59
def prefixEnd_2644515 : Nat := 4983230072969 + 3 ^ 40 * 2644515 * 2
def baseEnd_2644515 : Nat := 1357907293024826056600603

theorem tailTrace_2644515 : CollatzResearch.WordTrace tailWord_2644515 prefixEnd_2644515 1357907293024826056600603 := by
  unfold tailWord_2644515
  simp only [CollatzResearch.WordTrace]
  refine ⟨96453386014381277049638999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64302257342920851366425999 96453386014381277049638999)
  ·
    refine ⟨144680079021571915574458499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96453386014381277049638999 144680079021571915574458499)
    ·
      refine ⟨217020118532357873361687749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144680079021571915574458499 217020118532357873361687749)
      ·
        refine ⟨40691272224817101255316453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217020118532357873361687749 40691272224817101255316453)
        ·
          refine ⟨7629613542153206485371835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40691272224817101255316453 7629613542153206485371835)
          ·
            refine ⟨11444420313229809728057753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7629613542153206485371835 11444420313229809728057753)
            ·
              refine ⟨8583315234922357296043315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11444420313229809728057753 8583315234922357296043315)
              ·
                refine ⟨12874972852383535944064973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8583315234922357296043315 12874972852383535944064973)
                ·
                  refine ⟨4828114819643825979024365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12874972852383535944064973 4828114819643825979024365)
                  ·
                    refine ⟨1810543057366434742134137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4828114819643825979024365 1810543057366434742134137)
                    ·
                      refine ⟨1357907293024826056600603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810543057366434742134137 1357907293024826056600603)
                      ·
                        rfl

theorem cell23_2644515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_2644515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644515 prefixEnd_2644515 := by exact prefixLift 2644515
  have htrace : WordTrace (prefixWord ++ tailWord_2644515) baseStart_2644515 baseEnd_2644515 := by
    simpa [prefixWord, tailWord_2644515, baseEnd_2644515] using wordTrace_append hprefix tailTrace_2644515
  have hstable : (prefixWord ++ tailWord_2644515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644515).length < 2 ^ (prefixWord ++ tailWord_2644515).sum := by decide
  have hdescent : baseEnd_2644515 < baseStart_2644515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644526 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_2644526 : Nat := 118140960795 + 2644526 * 2 ^ 59
def prefixEnd_2644526 : Nat := 4983230072969 + 3 ^ 40 * 2644526 * 2
def baseEnd_2644526 : Nat := 1357912941312025513563053

theorem tailTrace_2644526 : CollatzResearch.WordTrace tailWord_2644526 prefixEnd_2644526 1357912941312025513563053 := by
  unfold tailWord_2644526
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056723402167678241036179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64302524811560950618859621 12056723402167678241036179)
  ·
    refine ⟨18085085103251517361554269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12056723402167678241036179 18085085103251517361554269)
    ·
      refine ⟨6781906913719319010582851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18085085103251517361554269 6781906913719319010582851)
      ·
        refine ⟨10172860370578978515874277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6781906913719319010582851 10172860370578978515874277)
        ·
          refine ⟨1907411319483558471726427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10172860370578978515874277 1907411319483558471726427)
          ·
            refine ⟨2861116979225337707589641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907411319483558471726427 2861116979225337707589641)
            ·
              refine ⟨2145837734419003280692231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2861116979225337707589641 2145837734419003280692231)
              ·
                refine ⟨3218756601628504921038347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145837734419003280692231 3218756601628504921038347)
                ·
                  refine ⟨4828134902442757381557521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218756601628504921038347 4828134902442757381557521)
                  ·
                    refine ⟨3621101176832068036168141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828134902442757381557521 3621101176832068036168141)
                    ·
                      refine ⟨1357912941312025513563053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3621101176832068036168141 1357912941312025513563053)
                      ·
                        rfl

theorem cell23_2644526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_2644526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644526 prefixEnd_2644526 := by exact prefixLift 2644526
  have htrace : WordTrace (prefixWord ++ tailWord_2644526) baseStart_2644526 baseEnd_2644526 := by
    simpa [prefixWord, tailWord_2644526, baseEnd_2644526] using wordTrace_append hprefix tailTrace_2644526
  have hstable : (prefixWord ++ tailWord_2644526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644526).length < 2 ^ (prefixWord ++ tailWord_2644526).sum := by decide
  have hdescent : baseEnd_2644526 < baseStart_2644526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644531 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 5]
def baseStart_2644531 : Nat := 118140960795 + 2644531 * 2 ^ 59
def prefixEnd_2644531 : Nat := 4983230072969 + 3 ^ 40 * 2644531 * 2
def baseEnd_2644531 : Nat := 1357915508715297994000529

theorem tailTrace_2644531 : CollatzResearch.WordTrace tailWord_2644531 prefixEnd_2644531 1357915508715297994000529 := by
  unfold tailWord_2644531
  simp only [CollatzResearch.WordTrace]
  refine ⟨96453969582323311782221447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64302646388215541188147631 96453969582323311782221447)
  ·
    refine ⟨144680954373484967673332171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96453969582323311782221447 144680954373484967673332171)
    ·
      refine ⟨217021431560227451509998257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144680954373484967673332171 217021431560227451509998257)
      ·
        refine ⟨162766073670170588632498693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217021431560227451509998257 162766073670170588632498693)
        ·
          refine ⟨30518638813156985368593505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162766073670170588632498693 30518638813156985368593505)
          ·
            refine ⟨22888979109867739026445129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30518638813156985368593505 22888979109867739026445129)
            ·
              refine ⟨17166734332400804269833847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22888979109867739026445129 17166734332400804269833847)
              ·
                refine ⟨25750101498601206404750771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17166734332400804269833847 25750101498601206404750771)
                ·
                  refine ⟨38625152247901809607126157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25750101498601206404750771 38625152247901809607126157)
                  ·
                    refine ⟨14484432092963178602672309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38625152247901809607126157 14484432092963178602672309)
                    ·
                      refine ⟨1357915508715297994000529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14484432092963178602672309 1357915508715297994000529)
                      ·
                        rfl

theorem cell23_2644531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_2644531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644531 prefixEnd_2644531 := by exact prefixLift 2644531
  have htrace : WordTrace (prefixWord ++ tailWord_2644531) baseStart_2644531 baseEnd_2644531 := by
    simpa [prefixWord, tailWord_2644531, baseEnd_2644531] using wordTrace_append hprefix tailTrace_2644531
  have hstable : (prefixWord ++ tailWord_2644531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644531).length < 2 ^ (prefixWord ++ tailWord_2644531).sum := by decide
  have hdescent : baseEnd_2644531 < baseStart_2644531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644558 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2644558 : Nat := 118140960795 + 2644558 * 2 ^ 59
def prefixEnd_2644558 : Nat := 4983230072969 + 3 ^ 40 * 2644558 * 2
def baseEnd_2644558 : Nat := 1357929372692969388362905

theorem tailTrace_2644558 : CollatzResearch.WordTrace tailWord_2644558 prefixEnd_2644558 1357929372692969388362905 := by
  unfold tailWord_2644558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056869294153186924181791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64303302902150330262302885 12056869294153186924181791)
  ·
    refine ⟨18085303941229780386272687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12056869294153186924181791 18085303941229780386272687)
    ·
      refine ⟨27127955911844670579409031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18085303941229780386272687 27127955911844670579409031)
      ·
        refine ⟨40691933867767005869113547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27127955911844670579409031 40691933867767005869113547)
        ·
          refine ⟨61037900801650508803670321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40691933867767005869113547 61037900801650508803670321)
          ·
            refine ⟨45778425601237881602752741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61037900801650508803670321 45778425601237881602752741)
            ·
              refine ⟨8583454800232102800516139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45778425601237881602752741 8583454800232102800516139)
              ·
                refine ⟨12875182200348154200774209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8583454800232102800516139 12875182200348154200774209)
                ·
                  refine ⟨9656386650261115650580657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12875182200348154200774209 9656386650261115650580657)
                  ·
                    refine ⟨7242289987695836737935493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9656386650261115650580657 7242289987695836737935493)
                    ·
                      refine ⟨1357929372692969388362905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7242289987695836737935493 1357929372692969388362905)
                      ·
                        rfl

theorem cell23_2644558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2644558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644558 prefixEnd_2644558 := by exact prefixLift 2644558
  have htrace : WordTrace (prefixWord ++ tailWord_2644558) baseStart_2644558 baseEnd_2644558 := by
    simpa [prefixWord, tailWord_2644558, baseEnd_2644558] using wordTrace_append hprefix tailTrace_2644558
  have hstable : (prefixWord ++ tailWord_2644558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644558).length < 2 ^ (prefixWord ++ tailWord_2644558).sum := by decide
  have hdescent : baseEnd_2644558 < baseStart_2644558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644608 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_2644608 : Nat := 118140960795 + 2644608 * 2 ^ 59
def prefixEnd_2644608 : Nat := 4983230072969 + 3 ^ 40 * 2644608 * 2
def baseEnd_2644608 : Nat := 1357955046725694192737675

theorem tailTrace_2644608 : CollatzResearch.WordTrace tailWord_2644608 prefixEnd_2644608 1357955046725694192737675 := by
  unfold tailWord_2644608
  simp only [CollatzResearch.WordTrace]
  refine ⟨48228389001522176966387239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64304518668696235955182985 48228389001522176966387239)
  ·
    refine ⟨72342583502283265449580859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48228389001522176966387239 72342583502283265449580859)
    ·
      refine ⟨108513875253424898174371289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72342583502283265449580859 108513875253424898174371289)
      ·
        refine ⟨81385406440068673630778467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108513875253424898174371289 81385406440068673630778467)
        ·
          refine ⟨122078109660103010446167701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81385406440068673630778467 122078109660103010446167701)
          ·
            refine ⟨5722411390317328614664111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122078109660103010446167701 5722411390317328614664111)
            ·
              refine ⟨8583617085475992921996167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5722411390317328614664111 8583617085475992921996167)
              ·
                refine ⟨12875425628213989382994251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8583617085475992921996167 12875425628213989382994251)
                ·
                  refine ⟨19313138442320984074491377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12875425628213989382994251 19313138442320984074491377)
                  ·
                    refine ⟨14484853831740738055868533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19313138442320984074491377 14484853831740738055868533)
                    ·
                      refine ⟨1357955046725694192737675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14484853831740738055868533 1357955046725694192737675)
                      ·
                        rfl

theorem cell23_2644608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_2644608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644608 prefixEnd_2644608 := by exact prefixLift 2644608
  have htrace : WordTrace (prefixWord ++ tailWord_2644608) baseStart_2644608 baseEnd_2644608 := by
    simpa [prefixWord, tailWord_2644608, baseEnd_2644608] using wordTrace_append hprefix tailTrace_2644608
  have hstable : (prefixWord ++ tailWord_2644608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644608).length < 2 ^ (prefixWord ++ tailWord_2644608).sum := by decide
  have hdescent : baseEnd_2644608 < baseStart_2644608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644655 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 3]
def baseStart_2644655 : Nat := 118140960795 + 2644655 * 2 ^ 59
def prefixEnd_2644655 : Nat := 4983230072969 + 3 ^ 40 * 2644655 * 2
def baseEnd_2644655 : Nat := 1357979180316455508849959

theorem tailTrace_2644655 : CollatzResearch.WordTrace tailWord_2644655 prefixEnd_2644655 1357979180316455508849959 := by
  unfold tailWord_2644655
  simp only [CollatzResearch.WordTrace]
  refine ⟨96458492233874080959735419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64305661489249387306490279 96458492233874080959735419)
  ·
    refine ⟨144687738350811121439603129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96458492233874080959735419 144687738350811121439603129)
    ·
      refine ⟨108515803763108341079702347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144687738350811121439603129 108515803763108341079702347)
      ·
        refine ⟨162773705644662511619553521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108515803763108341079702347 162773705644662511619553521)
        ·
          refine ⟨122080279233496883714665141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162773705644662511619553521 122080279233496883714665141)
          ·
            refine ⟨11445026178140332848249857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122080279233496883714665141 11445026178140332848249857)
            ·
              refine ⟨8583769633605249636187393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11445026178140332848249857 8583769633605249636187393)
              ·
                refine ⟨6437827225203937227140545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8583769633605249636187393 6437827225203937227140545)
                ·
                  refine ⟨4828370418902952920355409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6437827225203937227140545 4828370418902952920355409)
                  ·
                    refine ⟨3621277814177214690266557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828370418902952920355409 3621277814177214690266557)
                    ·
                      refine ⟨1357979180316455508849959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3621277814177214690266557 1357979180316455508849959)
                      ·
                        rfl

theorem cell23_2644655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_2644655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644655 prefixEnd_2644655 := by exact prefixLift 2644655
  have htrace : WordTrace (prefixWord ++ tailWord_2644655) baseStart_2644655 baseEnd_2644655 := by
    simpa [prefixWord, tailWord_2644655, baseEnd_2644655] using wordTrace_append hprefix tailTrace_2644655
  have hstable : (prefixWord ++ tailWord_2644655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644655).length < 2 ^ (prefixWord ++ tailWord_2644655).sum := by decide
  have hdescent : baseEnd_2644655 < baseStart_2644655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644719 : List Nat := [1, 1, 2, 1, 5, 2, 2, 4, 1, 1, 3]
def baseStart_2644719 : Nat := 118140960795 + 2644719 * 2 ^ 59
def prefixEnd_2644719 : Nat := 4983230072969 + 3 ^ 40 * 2644719 * 2
def baseEnd_2644719 : Nat := 1358012043078343258449665

theorem tailTrace_2644719 : CollatzResearch.WordTrace tailWord_2644719 prefixEnd_2644719 1358012043078343258449665 := by
  unfold tailWord_2644719
  simp only [CollatzResearch.WordTrace]
  refine ⟨96460826505642219890065211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64307217670428146593376807 96460826505642219890065211)
  ·
    refine ⟨144691239758463329835097817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96460826505642219890065211 144691239758463329835097817)
    ·
      refine ⟨108518429818847497376323363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144691239758463329835097817 108518429818847497376323363)
      ·
        refine ⟨162777644728271246064485045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108518429818847497376323363 162777644728271246064485045)
        ·
          refine ⟨15260404193275429318545473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162777644728271246064485045 15260404193275429318545473)
          ·
            refine ⟨11445303144956571988909105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15260404193275429318545473 11445303144956571988909105)
            ·
              refine ⟨8583977358717428991681829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11445303144956571988909105 8583977358717428991681829)
              ·
                refine ⟨1609495754759517935940343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8583977358717428991681829 1609495754759517935940343)
                ·
                  refine ⟨2414243632139276903910515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609495754759517935940343 2414243632139276903910515)
                  ·
                    refine ⟨3621365448208915355865773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2414243632139276903910515 3621365448208915355865773)
                    ·
                      refine ⟨1358012043078343258449665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3621365448208915355865773 1358012043078343258449665)
                      ·
                        rfl

theorem cell23_2644719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 1, 1, 3].length) (baseStart_2644719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644719 prefixEnd_2644719 := by exact prefixLift 2644719
  have htrace : WordTrace (prefixWord ++ tailWord_2644719) baseStart_2644719 baseEnd_2644719 := by
    simpa [prefixWord, tailWord_2644719, baseEnd_2644719] using wordTrace_append hprefix tailTrace_2644719
  have hstable : (prefixWord ++ tailWord_2644719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644719).length < 2 ^ (prefixWord ++ tailWord_2644719).sum := by decide
  have hdescent : baseEnd_2644719 < baseStart_2644719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644745 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 3]
def baseStart_2644745 : Nat := 118140960795 + 2644745 * 2 ^ 59
def prefixEnd_2644745 : Nat := 4983230072969 + 3 ^ 40 * 2644745 * 2
def baseEnd_2644745 : Nat := 1358025393575360156724545

theorem tailTrace_2644745 : CollatzResearch.WordTrace tailWord_2644745 prefixEnd_2644745 1358025393575360156724545 := by
  unfold tailWord_2644745
  simp only [CollatzResearch.WordTrace]
  refine ⟨96461774803548026330511689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64307849869032017553674459 96461774803548026330511689)
  ·
    refine ⟨72346331102661019747883767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96461774803548026330511689 72346331102661019747883767)
    ·
      refine ⟨108519496653991529621825651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72346331102661019747883767 108519496653991529621825651)
      ·
        refine ⟨162779244980987294432738477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108519496653991529621825651 162779244980987294432738477)
        ·
          refine ⟨61042216867870235412276929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162779244980987294432738477 61042216867870235412276929)
          ·
            refine ⟨45781662650902676559207697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61042216867870235412276929 45781662650902676559207697)
            ·
              refine ⟨34336246988177007419405773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45781662650902676559207697 34336246988177007419405773)
              ·
                refine ⟨12876092620566377782277165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34336246988177007419405773 12876092620566377782277165)
                ·
                  refine ⟨4828534732712391668353937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12876092620566377782277165 4828534732712391668353937)
                  ·
                    refine ⟨3621401049534293751265453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828534732712391668353937 3621401049534293751265453)
                    ·
                      refine ⟨1358025393575360156724545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3621401049534293751265453 1358025393575360156724545)
                      ·
                        rfl

theorem cell23_2644745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_2644745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644745 prefixEnd_2644745 := by exact prefixLift 2644745
  have htrace : WordTrace (prefixWord ++ tailWord_2644745) baseStart_2644745 baseEnd_2644745 := by
    simpa [prefixWord, tailWord_2644745, baseEnd_2644745] using wordTrace_append hprefix tailTrace_2644745
  have hstable : (prefixWord ++ tailWord_2644745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644745).length < 2 ^ (prefixWord ++ tailWord_2644745).sum := by decide
  have hdescent : baseEnd_2644745 < baseStart_2644745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644762 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_2644762 : Nat := 118140960795 + 2644762 * 2 ^ 59
def prefixEnd_2644762 : Nat := 4983230072969 + 3 ^ 40 * 2644762 * 2
def baseEnd_2644762 : Nat := 1358034122746486590211967

theorem tailTrace_2644762 : CollatzResearch.WordTrace tailWord_2644762 prefixEnd_2644762 1358034122746486590211967 := by
  unfold tailWord_2644762
  simp only [CollatzResearch.WordTrace]
  refine ⟨24115598711121609558470135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64308263229657625489253693 24115598711121609558470135)
  ·
    refine ⟨36173398066682414337705203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24115598711121609558470135 36173398066682414337705203)
    ·
      refine ⟨54260097100023621506557805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36173398066682414337705203 54260097100023621506557805)
      ·
        refine ⟨20347536412508858064959177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54260097100023621506557805 20347536412508858064959177)
        ·
          refine ⟨15260652309381643548719383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20347536412508858064959177 15260652309381643548719383)
          ·
            refine ⟨22890978464072465323079075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15260652309381643548719383 22890978464072465323079075)
            ·
              refine ⟨34336467696108697984618613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22890978464072465323079075 34336467696108697984618613)
              ·
                refine ⟨3219043846510190436057995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34336467696108697984618613 3219043846510190436057995)
                ·
                  refine ⟨4828565769765285654086993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219043846510190436057995 4828565769765285654086993)
                  ·
                    refine ⟨3621424327323964240565245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828565769765285654086993 3621424327323964240565245)
                    ·
                      refine ⟨1358034122746486590211967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3621424327323964240565245 1358034122746486590211967)
                      ·
                        rfl

theorem cell23_2644762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_2644762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644762 prefixEnd_2644762 := by exact prefixLift 2644762
  have htrace : WordTrace (prefixWord ++ tailWord_2644762) baseStart_2644762 baseEnd_2644762 := by
    simpa [prefixWord, tailWord_2644762, baseEnd_2644762] using wordTrace_append hprefix tailTrace_2644762
  have hstable : (prefixWord ++ tailWord_2644762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644762).length < 2 ^ (prefixWord ++ tailWord_2644762).sum := by decide
  have hdescent : baseEnd_2644762 < baseStart_2644762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644782 : List Nat := [4, 1, 3, 2, 1, 2, 2, 8]
def baseStart_2644782 : Nat := 118140960795 + 2644782 * 2 ^ 59
def prefixEnd_2644782 : Nat := 4983230072969 + 3 ^ 40 * 2644782 * 2
def baseEnd_2644782 : Nat := 50297940457762093035625

theorem tailTrace_2644782 : CollatzResearch.WordTrace tailWord_2644782 prefixEnd_2644782 50297940457762093035625 := by
  unfold tailWord_2644782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12057890538051747706201075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64308749536275987766405733 12057890538051747706201075)
  ·
    refine ⟨18086835807077621559301613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12057890538051747706201075 18086835807077621559301613)
    ·
      refine ⟨6782563427654108084738105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18086835807077621559301613 6782563427654108084738105)
      ·
        refine ⟨5086922570740581063553579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6782563427654108084738105 5086922570740581063553579)
        ·
          refine ⟨7630383856110871595330369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5086922570740581063553579 7630383856110871595330369)
          ·
            refine ⟨5722787892083153696497777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7630383856110871595330369 5722787892083153696497777)
            ·
              refine ⟨4292090919062365272373333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5722787892083153696497777 4292090919062365272373333)
              ·
                refine ⟨50297940457762093035625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4292090919062365272373333 50297940457762093035625)
                ·
                  rfl

theorem cell23_2644782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_2644782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644782 prefixEnd_2644782 := by exact prefixLift 2644782
  have htrace : WordTrace (prefixWord ++ tailWord_2644782) baseStart_2644782 baseEnd_2644782 := by
    simpa [prefixWord, tailWord_2644782, baseEnd_2644782] using wordTrace_append hprefix tailTrace_2644782
  have hstable : (prefixWord ++ tailWord_2644782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644782).length < 2 ^ (prefixWord ++ tailWord_2644782).sum := by decide
  have hdescent : baseEnd_2644782 < baseStart_2644782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644806 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2644806 : Nat := 118140960795 + 2644806 * 2 ^ 59
def prefixEnd_2644806 : Nat := 4983230072969 + 3 ^ 40 * 2644806 * 2
def baseEnd_2644806 : Nat := 1358056715895284418061765

theorem tailTrace_2644806 : CollatzResearch.WordTrace tailWord_2644806 prefixEnd_2644806 1358056715895284418061765 := by
  unfold tailWord_2644806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014499989260219804640071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 64309333104218022498988181 3014499989260219804640071)
  ·
    refine ⟨4521749983890329706960107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3014499989260219804640071 4521749983890329706960107)
    ·
      refine ⟨6782624975835494560440161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4521749983890329706960107 6782624975835494560440161)
      ·
        refine ⟨5086968731876620920330121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6782624975835494560440161 5086968731876620920330121)
        ·
          refine ⟨3815226548907465690247591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5086968731876620920330121 3815226548907465690247591)
          ·
            refine ⟨5722839823361198535371387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3815226548907465690247591 5722839823361198535371387)
            ·
              refine ⟨8584259735041797803057081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5722839823361198535371387 8584259735041797803057081)
              ·
                refine ⟨6438194801281348352292811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8584259735041797803057081 6438194801281348352292811)
                ·
                  refine ⟨9657292201922022528439217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6438194801281348352292811 9657292201922022528439217)
                  ·
                    refine ⟨7242969151441516896329413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9657292201922022528439217 7242969151441516896329413)
                    ·
                      refine ⟨1358056715895284418061765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7242969151441516896329413 1358056715895284418061765)
                      ·
                        rfl

theorem cell23_2644806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2644806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644806 prefixEnd_2644806 := by exact prefixLift 2644806
  have htrace : WordTrace (prefixWord ++ tailWord_2644806) baseStart_2644806 baseEnd_2644806 := by
    simpa [prefixWord, tailWord_2644806, baseEnd_2644806] using wordTrace_append hprefix tailTrace_2644806
  have hstable : (prefixWord ++ tailWord_2644806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644806).length < 2 ^ (prefixWord ++ tailWord_2644806).sum := by decide
  have hdescent : baseEnd_2644806 < baseStart_2644806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644813 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2644813 : Nat := 118140960795 + 2644813 * 2 ^ 59
def prefixEnd_2644813 : Nat := 4983230072969 + 3 ^ 40 * 2644813 * 2
def baseEnd_2644813 : Nat := 1358060310259865890674233

theorem tailTrace_2644813 : CollatzResearch.WordTrace tailWord_2644813 prefixEnd_2644813 1358060310259865890674233 := by
  unfold tailWord_2644813
  simp only [CollatzResearch.WordTrace]
  refine ⟨96464254967301673943987093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64309503311534449295991395 96464254967301673943987093)
  ·
    refine ⟨4521761951592265966124395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96464254967301673943987093 4521761951592265966124395)
    ·
      refine ⟨6782642927388398949186593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4521761951592265966124395 6782642927388398949186593)
      ·
        refine ⟨5086982195541299211889945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6782642927388398949186593 5086982195541299211889945)
        ·
          refine ⟨3815236646655974408917459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5086982195541299211889945 3815236646655974408917459)
          ·
            refine ⟨5722854969983961613376189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3815236646655974408917459 5722854969983961613376189)
            ·
              refine ⟨2146070613743985605016071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5722854969983961613376189 2146070613743985605016071)
              ·
                refine ⟨3219105920615978407524107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146070613743985605016071 3219105920615978407524107)
                ·
                  refine ⟨4828658880923967611286161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219105920615978407524107 4828658880923967611286161)
                  ·
                    refine ⟨3621494160692975708464621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4828658880923967611286161 3621494160692975708464621)
                    ·
                      refine ⟨1358060310259865890674233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3621494160692975708464621 1358060310259865890674233)
                      ·
                        rfl

theorem cell23_2644813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2644813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644813 prefixEnd_2644813 := by exact prefixLift 2644813
  have htrace : WordTrace (prefixWord ++ tailWord_2644813) baseStart_2644813 baseEnd_2644813 := by
    simpa [prefixWord, tailWord_2644813, baseEnd_2644813] using wordTrace_append hprefix tailTrace_2644813
  have hstable : (prefixWord ++ tailWord_2644813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644813).length < 2 ^ (prefixWord ++ tailWord_2644813).sum := by decide
  have hdescent : baseEnd_2644813 < baseStart_2644813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644832 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 3, 4, 2]
def baseStart_2644832 : Nat := 118140960795 + 2644832 * 2 ^ 59
def prefixEnd_2644832 : Nat := 4983230072969 + 3 ^ 40 * 2644832 * 2
def baseEnd_2644832 : Nat := 1358070066392301316336645

theorem tailTrace_2644832 : CollatzResearch.WordTrace tailWord_2644832 prefixEnd_2644832 1358070066392301316336645 := by
  unfold tailWord_2644832
  simp only [CollatzResearch.WordTrace]
  refine ⟨48232473977116420094464375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64309965302821893459285833 48232473977116420094464375)
  ·
    refine ⟨72348710965674630141696563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48232473977116420094464375 72348710965674630141696563)
    ·
      refine ⟨108523066448511945212544845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72348710965674630141696563 108523066448511945212544845)
      ·
        refine ⟨40696149918191979454704317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108523066448511945212544845 40696149918191979454704317)
        ·
          refine ⟨15261056219321992295514119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40696149918191979454704317 15261056219321992295514119)
          ·
            refine ⟨22891584328982988443271179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15261056219321992295514119 22891584328982988443271179)
            ·
              refine ⟨34337376493474482664906769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22891584328982988443271179 34337376493474482664906769)
              ·
                refine ⟨25753032370105861998680077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34337376493474482664906769 25753032370105861998680077)
                ·
                  refine ⟨9657387138789698249505029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25753032370105861998680077 9657387138789698249505029)
                  ·
                    refine ⟨1810760088523068421782193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9657387138789698249505029 1810760088523068421782193)
                    ·
                      refine ⟨1358070066392301316336645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810760088523068421782193 1358070066392301316336645)
                      ·
                        rfl

theorem cell23_2644832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_2644832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644832 prefixEnd_2644832 := by exact prefixLift 2644832
  have htrace : WordTrace (prefixWord ++ tailWord_2644832) baseStart_2644832 baseEnd_2644832 := by
    simpa [prefixWord, tailWord_2644832, baseEnd_2644832] using wordTrace_append hprefix tailTrace_2644832
  have hstable : (prefixWord ++ tailWord_2644832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644832).length < 2 ^ (prefixWord ++ tailWord_2644832).sum := by decide
  have hdescent : baseEnd_2644832 < baseStart_2644832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644849 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 1, 4, 2]
def baseStart_2644849 : Nat := 118140960795 + 2644849 * 2 ^ 59
def prefixEnd_2644849 : Nat := 4983230072969 + 3 ^ 40 * 2644849 * 2
def baseEnd_2644849 : Nat := 1358078795563427749824067

theorem tailTrace_2644849 : CollatzResearch.WordTrace tailWord_2644849 prefixEnd_2644849 1358078795563427749824067 := by
  unfold tailWord_2644849
  simp only [CollatzResearch.WordTrace]
  refine ⟨96465567995171252092297601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64310378663447501394865067 96465567995171252092297601)
  ·
    refine ⟨72349175996378439069223201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96465567995171252092297601 72349175996378439069223201)
    ·
      refine ⟨54261881997283829301917401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72349175996378439069223201 54261881997283829301917401)
      ·
        refine ⟨40696411497962871976438051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54261881997283829301917401 40696411497962871976438051)
        ·
          refine ⟨61044617246944307964657077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40696411497962871976438051 61044617246944307964657077)
          ·
            refine ⟨5722932866901028871686601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61044617246944307964657077 5722932866901028871686601)
            ·
              refine ⟨4292199650175771653764951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5722932866901028871686601 4292199650175771653764951)
              ·
                refine ⟨6438299475263657480647427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292199650175771653764951 6438299475263657480647427)
                ·
                  refine ⟨9657449212895486220971141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6438299475263657480647427 9657449212895486220971141)
                  ·
                    refine ⟨1810771727417903666432089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9657449212895486220971141 1810771727417903666432089)
                    ·
                      refine ⟨1358078795563427749824067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810771727417903666432089 1358078795563427749824067)
                      ·
                        rfl

theorem cell23_2644849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_2644849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644849 prefixEnd_2644849 := by exact prefixLift 2644849
  have htrace : WordTrace (prefixWord ++ tailWord_2644849) baseStart_2644849 baseEnd_2644849 := by
    simpa [prefixWord, tailWord_2644849, baseEnd_2644849] using wordTrace_append hprefix tailTrace_2644849
  have hstable : (prefixWord ++ tailWord_2644849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644849).length < 2 ^ (prefixWord ++ tailWord_2644849).sum := by decide
  have hdescent : baseEnd_2644849 < baseStart_2644849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644905 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_2644905 : Nat := 118140960795 + 2644905 * 2 ^ 59
def prefixEnd_2644905 : Nat := 4983230072969 + 3 ^ 40 * 2644905 * 2
def baseEnd_2644905 : Nat := 1358107550480079530723809

theorem tailTrace_2644905 : CollatzResearch.WordTrace tailWord_2644905 prefixEnd_2644905 1358107550480079530723809 := by
  unfold tailWord_2644905
  simp only [CollatzResearch.WordTrace]
  refine ⟨96467610482968373656336169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64311740321978915770890779 96467610482968373656336169)
  ·
    refine ⟨72350707862226280242252127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96467610482968373656336169 72350707862226280242252127)
    ·
      refine ⟨108526061793339420363378191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72350707862226280242252127 108526061793339420363378191)
      ·
        refine ⟨162789092690009130545067287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108526061793339420363378191 162789092690009130545067287)
        ·
          refine ⟨244183639035013695817600931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162789092690009130545067287 244183639035013695817600931)
          ·
            refine ⟨366275458552520543726401397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244183639035013695817600931 366275458552520543726401397)
            ·
              refine ⟨34338324239298800974350131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 366275458552520543726401397 34338324239298800974350131)
              ·
                refine ⟨51507486358948201461525197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34338324239298800974350131 51507486358948201461525197)
                ·
                  refine ⟨19315307384605575548071949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51507486358948201461525197 19315307384605575548071949)
                  ·
                    refine ⟨7243240269227090830526981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19315307384605575548071949 7243240269227090830526981)
                    ·
                      refine ⟨1358107550480079530723809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7243240269227090830526981 1358107550480079530723809)
                      ·
                        rfl

theorem cell23_2644905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_2644905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644905 prefixEnd_2644905 := by exact prefixLift 2644905
  have htrace : WordTrace (prefixWord ++ tailWord_2644905) baseStart_2644905 baseEnd_2644905 := by
    simpa [prefixWord, tailWord_2644905, baseEnd_2644905] using wordTrace_append hprefix tailTrace_2644905
  have hstable : (prefixWord ++ tailWord_2644905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644905).length < 2 ^ (prefixWord ++ tailWord_2644905).sum := by decide
  have hdescent : baseEnd_2644905 < baseStart_2644905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644922 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_2644922 : Nat := 118140960795 + 2644922 * 2 ^ 59
def prefixEnd_2644922 : Nat := 4983230072969 + 3 ^ 40 * 2644922 * 2
def baseEnd_2644922 : Nat := 1358116279651205964211231

theorem tailTrace_2644922 : CollatzResearch.WordTrace tailWord_2644922 prefixEnd_2644922 1358116279651205964211231 := by
  unfold tailWord_2644922
  simp only [CollatzResearch.WordTrace]
  refine ⟨24117057630976696389926255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64312153682604523706470013 24117057630976696389926255)
  ·
    refine ⟨36175586446465044584889383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24117057630976696389926255 36175586446465044584889383)
    ·
      refine ⟨54263379669697566877334075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36175586446465044584889383 54263379669697566877334075)
      ·
        refine ⟨81395069504546350316001113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54263379669697566877334075 81395069504546350316001113)
        ·
          refine ⟨61046302128409762737000835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81395069504546350316001113 61046302128409762737000835)
          ·
            refine ⟨91569453192614644105501253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61046302128409762737000835 91569453192614644105501253)
            ·
              refine ⟨17169272473615245769781485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91569453192614644105501253 17169272473615245769781485)
              ·
                refine ⟨6438477177605717163668057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17169272473615245769781485 6438477177605717163668057)
                ·
                  refine ⟨4828857883204287872751043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6438477177605717163668057 4828857883204287872751043)
                  ·
                    refine ⟨7243286824806431809126565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4828857883204287872751043 7243286824806431809126565)
                    ·
                      refine ⟨1358116279651205964211231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7243286824806431809126565 1358116279651205964211231)
                      ·
                        rfl

theorem cell23_2644922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_2644922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644922 prefixEnd_2644922 := by exact prefixLift 2644922
  have htrace : WordTrace (prefixWord ++ tailWord_2644922) baseStart_2644922 baseEnd_2644922 := by
    simpa [prefixWord, tailWord_2644922, baseEnd_2644922] using wordTrace_append hprefix tailTrace_2644922
  have hstable : (prefixWord ++ tailWord_2644922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644922).length < 2 ^ (prefixWord ++ tailWord_2644922).sum := by decide
  have hdescent : baseEnd_2644922 < baseStart_2644922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644935 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_2644935 : Nat := 118140960795 + 2644935 * 2 ^ 59
def prefixEnd_2644935 : Nat := 4983230072969 + 3 ^ 40 * 2644935 * 2
def baseEnd_2644935 : Nat := 1358122954899714413348671

theorem tailTrace_2644935 : CollatzResearch.WordTrace tailWord_2644935 prefixEnd_2644935 1358122954899714413348671 := by
  unfold tailWord_2644935
  simp only [CollatzResearch.WordTrace]
  refine ⟨96468704672859688779928259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64312469781906459186618839 96468704672859688779928259)
  ·
    refine ⟨144703057009289533169892389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96468704672859688779928259 144703057009289533169892389)
    ·
      refine ⟨27131823189241787469354823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144703057009289533169892389 27131823189241787469354823)
      ·
        refine ⟨40697734783862681204032235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27131823189241787469354823 40697734783862681204032235)
        ·
          refine ⟨61046602175794021806048353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40697734783862681204032235 61046602175794021806048353)
          ·
            refine ⟨45784951631845516354536265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61046602175794021806048353 45784951631845516354536265)
            ·
              refine ⟨34338713723884137265902199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45784951631845516354536265 34338713723884137265902199)
              ·
                refine ⟨51508070585826205898853299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34338713723884137265902199 51508070585826205898853299)
                ·
                  refine ⟨77262105878739308848279949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51508070585826205898853299 77262105878739308848279949)
                  ·
                    refine ⟨28973289704527240818104981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77262105878739308848279949 28973289704527240818104981)
                    ·
                      refine ⟨1358122954899714413348671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28973289704527240818104981 1358122954899714413348671)
                      ·
                        rfl

theorem cell23_2644935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2644935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644935 prefixEnd_2644935 := by exact prefixLift 2644935
  have htrace : WordTrace (prefixWord ++ tailWord_2644935) baseStart_2644935 baseEnd_2644935 := by
    simpa [prefixWord, tailWord_2644935, baseEnd_2644935] using wordTrace_append hprefix tailTrace_2644935
  have hstable : (prefixWord ++ tailWord_2644935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644935).length < 2 ^ (prefixWord ++ tailWord_2644935).sum := by decide
  have hdescent : baseEnd_2644935 < baseStart_2644935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2644945 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 8]
def baseStart_2644945 : Nat := 118140960795 + 2644945 * 2 ^ 59
def prefixEnd_2644945 : Nat := 4983230072969 + 3 ^ 40 * 2644945 * 2
def baseEnd_2644945 : Nat := 150903121078473263802625

theorem tailTrace_2644945 : CollatzResearch.WordTrace tailWord_2644945 prefixEnd_2644945 150903121078473263802625 := by
  unfold tailWord_2644945
  simp only [CollatzResearch.WordTrace]
  refine ⟨96469069402823460487792289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64312712935215640325194859 96469069402823460487792289)
  ·
    refine ⟨72351802052117595365844217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96469069402823460487792289 72351802052117595365844217)
    ·
      refine ⟨54263851539088196524383163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72351802052117595365844217 54263851539088196524383163)
      ·
        refine ⟨81395777308632294786574745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54263851539088196524383163 81395777308632294786574745)
        ·
          refine ⟨61046832981474221089931059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81395777308632294786574745 61046832981474221089931059)
          ·
            refine ⟨91570249472211331634896589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61046832981474221089931059 91570249472211331634896589)
            ·
              refine ⟨34338843552079249363086221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91570249472211331634896589 34338843552079249363086221)
              ·
                refine ⟨12877066332029718511157333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34338843552079249363086221 12877066332029718511157333)
                ·
                  refine ⟨150903121078473263802625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12877066332029718511157333 150903121078473263802625)
                  ·
                    rfl

theorem cell23_2644945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 8].length) (baseStart_2644945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2644945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2644945 prefixEnd_2644945 := by exact prefixLift 2644945
  have htrace : WordTrace (prefixWord ++ tailWord_2644945) baseStart_2644945 baseEnd_2644945 := by
    simpa [prefixWord, tailWord_2644945, baseEnd_2644945] using wordTrace_append hprefix tailTrace_2644945
  have hstable : (prefixWord ++ tailWord_2644945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2644945).length < 2 ^ (prefixWord ++ tailWord_2644945).sum := by decide
  have hdescent : baseEnd_2644945 < baseStart_2644945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2644945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645029 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_2645029 : Nat := 118140960795 + 2645029 * 2 ^ 59
def prefixEnd_2645029 : Nat := 4983230072969 + 3 ^ 40 * 2645029 * 2
def baseEnd_2645029 : Nat := 1358171222081237045573239

theorem tailTrace_2645029 : CollatzResearch.WordTrace tailWord_2645029 prefixEnd_2645029 1358171222081237045573239 := by
  unfold tailWord_2645029
  simp only [CollatzResearch.WordTrace]
  refine ⟨96472133134519142833850141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64314755423012761889233427 96472133134519142833850141)
  ·
    refine ⟨36177049925444678562693803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96472133134519142833850141 36177049925444678562693803)
    ·
      refine ⟨54265574888167017844040705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36177049925444678562693803 54265574888167017844040705)
      ·
        refine ⟨40699181166125263383030529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54265574888167017844040705 40699181166125263383030529)
        ·
          refine ⟨30524385874593947537272897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40699181166125263383030529 30524385874593947537272897)
          ·
            refine ⟨22893289405945460652954673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30524385874593947537272897 22893289405945460652954673)
            ·
              refine ⟨17169967054459095489716005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22893289405945460652954673 17169967054459095489716005)
              ·
                refine ⟨3219368822711080404321751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17169967054459095489716005 3219368822711080404321751)
                ·
                  refine ⟨4829053234066620606482627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219368822711080404321751 4829053234066620606482627)
                  ·
                    refine ⟨7243579851099930909723941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4829053234066620606482627 7243579851099930909723941)
                    ·
                      refine ⟨1358171222081237045573239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7243579851099930909723941 1358171222081237045573239)
                      ·
                        rfl

theorem cell23_2645029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_2645029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645029 prefixEnd_2645029 := by exact prefixLift 2645029
  have htrace : WordTrace (prefixWord ++ tailWord_2645029) baseStart_2645029 baseEnd_2645029 := by
    simpa [prefixWord, tailWord_2645029, baseEnd_2645029] using wordTrace_append hprefix tailTrace_2645029
  have hstable : (prefixWord ++ tailWord_2645029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645029).length < 2 ^ (prefixWord ++ tailWord_2645029).sum := by decide
  have hdescent : baseEnd_2645029 < baseStart_2645029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645052 : List Nat := [2, 2, 2, 2, 2, 3, 10]
def baseStart_2645052 : Nat := 118140960795 + 2645052 * 2 ^ 59
def prefixEnd_2645052 : Nat := 4983230072969 + 3 ^ 40 * 2645052 * 2
def baseEnd_2645052 : Nat := 16767691754769017970193

theorem tailTrace_2645052 : CollatzResearch.WordTrace tailWord_2645052 prefixEnd_2645052 16767691754769017970193 := by
  unfold tailWord_2645052
  simp only [CollatzResearch.WordTrace]
  refine ⟨48236486006717908880968705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64315314675623878507958273 48236486006717908880968705)
  ·
    refine ⟨36177364505038431660726529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48236486006717908880968705 36177364505038431660726529)
    ·
      refine ⟨27133023378778823745544897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36177364505038431660726529 27133023378778823745544897)
      ·
        refine ⟨20349767534084117809158673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27133023378778823745544897 20349767534084117809158673)
        ·
          refine ⟨15262325650563088356869005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20349767534084117809158673 15262325650563088356869005)
          ·
            refine ⟨5723372118961158133825877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15262325650563088356869005 5723372118961158133825877)
            ·
              refine ⟨16767691754769017970193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5723372118961158133825877 16767691754769017970193)
              ·
                rfl

theorem cell23_2645052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 10].length) (baseStart_2645052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645052 prefixEnd_2645052 := by exact prefixLift 2645052
  have htrace : WordTrace (prefixWord ++ tailWord_2645052) baseStart_2645052 baseEnd_2645052 := by
    simpa [prefixWord, tailWord_2645052, baseEnd_2645052] using wordTrace_append hprefix tailTrace_2645052
  have hstable : (prefixWord ++ tailWord_2645052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645052).length < 2 ^ (prefixWord ++ tailWord_2645052).sum := by decide
  have hdescent : baseEnd_2645052 < baseStart_2645052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645063 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_2645063 : Nat := 118140960795 + 2645063 * 2 ^ 59
def prefixEnd_2645063 : Nat := 4983230072969 + 3 ^ 40 * 2645063 * 2
def baseEnd_2645063 : Nat := 1358188680423489912548083

theorem tailTrace_2645063 : CollatzResearch.WordTrace tailWord_2645063 prefixEnd_2645063 1358188680423489912548083 := by
  unfold tailWord_2645063
  simp only [CollatzResearch.WordTrace]
  refine ⟨96473373216395966640587843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64315582144263977760391895 96473373216395966640587843)
  ·
    refine ⟨144710059824593949960881765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96473373216395966640587843 144710059824593949960881765)
    ·
      refine ⟨27133136217111365617665331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144710059824593949960881765 27133136217111365617665331)
      ·
        refine ⟨40699704325667048426497997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27133136217111365617665331 40699704325667048426497997)
        ·
          refine ⟨15262389122125143159936749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40699704325667048426497997 15262389122125143159936749)
          ·
            refine ⟨5723395920796928684976281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15262389122125143159936749 5723395920796928684976281)
            ·
              refine ⟨4292546940597696513732211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5723395920796928684976281 4292546940597696513732211)
              ·
                refine ⟨6438820410896544770598317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292546940597696513732211 6438820410896544770598317)
                ·
                  refine ⟨2414557654086204288974369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6438820410896544770598317 2414557654086204288974369)
                  ·
                    refine ⟨1810918240564653216730777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2414557654086204288974369 1810918240564653216730777)
                    ·
                      refine ⟨1358188680423489912548083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810918240564653216730777 1358188680423489912548083)
                      ·
                        rfl

theorem cell23_2645063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_2645063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645063 prefixEnd_2645063 := by exact prefixLift 2645063
  have htrace : WordTrace (prefixWord ++ tailWord_2645063) baseStart_2645063 baseEnd_2645063 := by
    simpa [prefixWord, tailWord_2645063, baseEnd_2645063] using wordTrace_append hprefix tailTrace_2645063
  have hstable : (prefixWord ++ tailWord_2645063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645063).length < 2 ^ (prefixWord ++ tailWord_2645063).sum := by decide
  have hdescent : baseEnd_2645063 < baseStart_2645063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645112 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 4, 6]
def baseStart_2645112 : Nat := 118140960795 + 2645112 * 2 ^ 59
def prefixEnd_2645112 : Nat := 4983230072969 + 3 ^ 40 * 2645112 * 2
def baseEnd_2645112 : Nat := 452737946991853406945119

theorem tailTrace_2645112 : CollatzResearch.WordTrace tailWord_2645112 prefixEnd_2645112 452737946991853406945119 := by
  unfold tailWord_2645112
  simp only [CollatzResearch.WordTrace]
  refine ⟨48237580196609224004560795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64316773595478965339414393 48237580196609224004560795)
  ·
    refine ⟨72356370294913836006841193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48237580196609224004560795 72356370294913836006841193)
    ·
      refine ⟨54267277721185377005130895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72356370294913836006841193 54267277721185377005130895)
      ·
        refine ⟨81400916581778065507696343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54267277721185377005130895 81400916581778065507696343)
        ·
          refine ⟨122101374872667098261544515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81400916581778065507696343 122101374872667098261544515)
          ·
            refine ⟨183152062309000647392316773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122101374872667098261544515 183152062309000647392316773)
            ·
              refine ⟨34341011682937621386059395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183152062309000647392316773 34341011682937621386059395)
              ·
                refine ⟨51511517524406432079089093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34341011682937621386059395 51511517524406432079089093)
                ·
                  refine ⟨9658409535826206014829205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51511517524406432079089093 9658409535826206014829205)
                  ·
                    refine ⟨452737946991853406945119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9658409535826206014829205 452737946991853406945119)
                    ·
                      rfl

theorem cell23_2645112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_2645112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645112 prefixEnd_2645112 := by exact prefixLift 2645112
  have htrace : WordTrace (prefixWord ++ tailWord_2645112) baseStart_2645112 baseEnd_2645112 := by
    simpa [prefixWord, tailWord_2645112, baseEnd_2645112] using wordTrace_append hprefix tailTrace_2645112
  have hstable : (prefixWord ++ tailWord_2645112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645112).length < 2 ^ (prefixWord ++ tailWord_2645112).sum := by decide
  have hdescent : baseEnd_2645112 < baseStart_2645112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645132 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2645132 : Nat := 118140960795 + 2645132 * 2 ^ 59
def prefixEnd_2645132 : Nat := 4983230072969 + 3 ^ 40 * 2645132 * 2
def baseEnd_2645132 : Nat := 1358224110588650142585265

theorem tailTrace_2645132 : CollatzResearch.WordTrace tailWord_2645132 prefixEnd_2645132 1358224110588650142585265 := by
  unfold tailWord_2645132
  simp only [CollatzResearch.WordTrace]
  refine ⟨48237944926572995712424825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64317259902097327616566433 48237944926572995712424825)
  ·
    refine ⟨36178458694929746784318619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48237944926572995712424825 36178458694929746784318619)
    ·
      refine ⟨54267688042394620176477929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36178458694929746784318619 54267688042394620176477929)
      ·
        refine ⟨40700766031795965132358447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54267688042394620176477929 40700766031795965132358447)
        ·
          refine ⟨61051149047693947698537671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40700766031795965132358447 61051149047693947698537671)
          ·
            refine ⟨91576723571540921547806507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61051149047693947698537671 91576723571540921547806507)
            ·
              refine ⟨137365085357311382321709761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91576723571540921547806507 137365085357311382321709761)
              ·
                refine ⟨103023814017983536741282321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137365085357311382321709761 103023814017983536741282321)
                ·
                  refine ⟨77267860513487652555961741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103023814017983536741282321 77267860513487652555961741)
                  ·
                    refine ⟨28975447692557869708485653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77267860513487652555961741 28975447692557869708485653)
                    ·
                      refine ⟨1358224110588650142585265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28975447692557869708485653 1358224110588650142585265)
                      ·
                        rfl

theorem cell23_2645132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2645132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645132 prefixEnd_2645132 := by exact prefixLift 2645132
  have htrace : WordTrace (prefixWord ++ tailWord_2645132) baseStart_2645132 baseEnd_2645132 := by
    simpa [prefixWord, tailWord_2645132, baseEnd_2645132] using wordTrace_append hprefix tailTrace_2645132
  have hstable : (prefixWord ++ tailWord_2645132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645132).length < 2 ^ (prefixWord ++ tailWord_2645132).sum := by decide
  have hdescent : baseEnd_2645132 < baseStart_2645132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645136 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 6, 2, 2]
def baseStart_2645136 : Nat := 118140960795 + 2645136 * 2 ^ 59
def prefixEnd_2645136 : Nat := 4983230072969 + 3 ^ 40 * 2645136 * 2
def baseEnd_2645136 : Nat := 1358226164511268126935247

theorem tailTrace_2645136 : CollatzResearch.WordTrace tailWord_2645136 prefixEnd_2645136 1358226164511268126935247 := by
  unfold tailWord_2645136
  simp only [CollatzResearch.WordTrace]
  refine ⟨48238017872565750053997631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64317357163421000071996841 48238017872565750053997631)
  ·
    refine ⟨72357026808848625080996447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48238017872565750053997631 72357026808848625080996447)
    ·
      refine ⟨108535540213272937621494671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72357026808848625080996447 108535540213272937621494671)
      ·
        refine ⟨162803310319909406432242007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108535540213272937621494671 162803310319909406432242007)
        ·
          refine ⟨244204965479864109648363011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162803310319909406432242007 244204965479864109648363011)
          ·
            refine ⟨366307448219796164472544517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244204965479864109648363011 366307448219796164472544517)
            ·
              refine ⟨68682646541211780838602097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 366307448219796164472544517 68682646541211780838602097)
              ·
                refine ⟨51511984905908835628951573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68682646541211780838602097 51511984905908835628951573)
                ·
                  refine ⟨2414624292464476670107105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51511984905908835628951573 2414624292464476670107105)
                  ·
                    refine ⟨1810968219348357502580329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2414624292464476670107105 1810968219348357502580329)
                    ·
                      refine ⟨1358226164511268126935247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810968219348357502580329 1358226164511268126935247)
                      ·
                        rfl

theorem cell23_2645136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 2, 2].length) (baseStart_2645136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645136 prefixEnd_2645136 := by exact prefixLift 2645136
  have htrace : WordTrace (prefixWord ++ tailWord_2645136) baseStart_2645136 baseEnd_2645136 := by
    simpa [prefixWord, tailWord_2645136, baseEnd_2645136] using wordTrace_append hprefix tailTrace_2645136
  have hstable : (prefixWord ++ tailWord_2645136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645136).length < 2 ^ (prefixWord ++ tailWord_2645136).sum := by decide
  have hdescent : baseEnd_2645136 < baseStart_2645136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645170 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_2645170 : Nat := 118140960795 + 2645170 * 2 ^ 59
def prefixEnd_2645170 : Nat := 4983230072969 + 3 ^ 40 * 2645170 * 2
def baseEnd_2645170 : Nat := 1358243622853520993910091

theorem tailTrace_2645170 : CollatzResearch.WordTrace tailWord_2645170 prefixEnd_2645170 1358243622853520993910091 := by
  unfold tailWord_2645170
  simp only [CollatzResearch.WordTrace]
  refine ⟨24119318956752080978683241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64318183884672215943155309 24119318956752080978683241)
  ·
    refine ⟨18089489217564060734012431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24119318956752080978683241 18089489217564060734012431)
    ·
      refine ⟨27134233826346091101018647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18089489217564060734012431 27134233826346091101018647)
      ·
        refine ⟨40701350739519136651527971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27134233826346091101018647 40701350739519136651527971)
        ·
          refine ⟨61052026109278704977291957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40701350739519136651527971 61052026109278704977291957)
          ·
            refine ⟨5723627447744878591621121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61052026109278704977291957 5723627447744878591621121)
            ·
              refine ⟨4292720585808658943715841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5723627447744878591621121 4292720585808658943715841)
              ·
                refine ⟨3219540439356494207786881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4292720585808658943715841 3219540439356494207786881)
                ·
                  refine ⟨2414655329517370655840161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3219540439356494207786881 2414655329517370655840161)
                  ·
                    refine ⟨1810991497138027991880121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2414655329517370655840161 1810991497138027991880121)
                    ·
                      refine ⟨1358243622853520993910091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1810991497138027991880121 1358243622853520993910091)
                      ·
                        rfl

theorem cell23_2645170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_2645170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645170 prefixEnd_2645170 := by exact prefixLift 2645170
  have htrace : WordTrace (prefixWord ++ tailWord_2645170) baseStart_2645170 baseEnd_2645170 := by
    simpa [prefixWord, tailWord_2645170, baseEnd_2645170] using wordTrace_append hprefix tailTrace_2645170
  have hstable : (prefixWord ++ tailWord_2645170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645170).length < 2 ^ (prefixWord ++ tailWord_2645170).sum := by decide
  have hdescent : baseEnd_2645170 < baseStart_2645170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645313 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 3, 5]
def baseStart_2645313 : Nat := 118140960795 + 2645313 * 2 ^ 59
def prefixEnd_2645313 : Nat := 4983230072969 + 3 ^ 40 * 2645313 * 2
def baseEnd_2645313 : Nat := 452772350195704644807311

theorem tailTrace_2645313 : CollatzResearch.WordTrace tailWord_2645313 prefixEnd_2645313 452772350195704644807311 := by
  unfold tailWord_2645313
  simp only [CollatzResearch.WordTrace]
  refine ⟨96482491465490259337188593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64321660976993506224792395 96482491465490259337188593)
  ·
    refine ⟨72361868599117694502891445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96482491465490259337188593 72361868599117694502891445)
    ·
      refine ⟨6783925181167283859646073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72361868599117694502891445 6783925181167283859646073)
      ·
        refine ⟨5087943885875462894734555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6783925181167283859646073 5087943885875462894734555)
        ·
          refine ⟨7631915828813194342101833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5087943885875462894734555 7631915828813194342101833)
          ·
            refine ⟨5723936871609895756576375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7631915828813194342101833 5723936871609895756576375)
            ·
              refine ⟨8585905307414843634864563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5723936871609895756576375 8585905307414843634864563)
              ·
                refine ⟨12878857961122265452296845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8585905307414843634864563 12878857961122265452296845)
                ·
                  refine ⟨4829571735420849544611317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12878857961122265452296845 4829571735420849544611317)
                  ·
                    refine ⟨452772350195704644807311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4829571735420849544611317 452772350195704644807311)
                    ·
                      rfl

theorem cell23_2645313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_2645313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645313 prefixEnd_2645313 := by exact prefixLift 2645313
  have htrace : WordTrace (prefixWord ++ tailWord_2645313) baseStart_2645313 baseEnd_2645313 := by
    simpa [prefixWord, tailWord_2645313, baseEnd_2645313] using wordTrace_append hprefix tailTrace_2645313
  have hstable : (prefixWord ++ tailWord_2645313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645313).length < 2 ^ (prefixWord ++ tailWord_2645313).sum := by decide
  have hdescent : baseEnd_2645313 < baseStart_2645313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645326 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_2645326 : Nat := 118140960795 + 2645326 * 2 ^ 59
def prefixEnd_2645326 : Nat := 4983230072969 + 3 ^ 40 * 2645326 * 2
def baseEnd_2645326 : Nat := 452774575278540794519791

theorem tailTrace_2645326 : CollatzResearch.WordTrace tailWord_2645326 prefixEnd_2645326 452774575278540794519791 := by
  unfold tailWord_2645326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12060370701805395319676479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64321977076295441704941221 12060370701805395319676479)
  ·
    refine ⟨18090556052708092979514719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12060370701805395319676479 18090556052708092979514719)
    ·
      refine ⟨27135834079062139469272079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18090556052708092979514719 27135834079062139469272079)
      ·
        refine ⟨40703751118593209203908119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27135834079062139469272079 40703751118593209203908119)
        ·
          refine ⟨61055626677889813805862179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40703751118593209203908119 61055626677889813805862179)
          ·
            refine ⟨91583440016834720708793269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61055626677889813805862179 91583440016834720708793269)
            ·
              refine ⟨8585947501578255066449369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91583440016834720708793269 8585947501578255066449369)
              ·
                refine ⟨6439460626183691299837027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8585947501578255066449369 6439460626183691299837027)
                ·
                  refine ⟨9659190939275536949755541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6439460626183691299837027 9659190939275536949755541)
                  ·
                    refine ⟨452774575278540794519791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9659190939275536949755541 452774575278540794519791)
                    ·
                      rfl

theorem cell23_2645326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_2645326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645326 prefixEnd_2645326 := by exact prefixLift 2645326
  have htrace : WordTrace (prefixWord ++ tailWord_2645326) baseStart_2645326 baseEnd_2645326 := by
    simpa [prefixWord, tailWord_2645326, baseEnd_2645326] using wordTrace_append hprefix tailTrace_2645326
  have hstable : (prefixWord ++ tailWord_2645326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645326).length < 2 ^ (prefixWord ++ tailWord_2645326).sum := by decide
  have hdescent : baseEnd_2645326 < baseStart_2645326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645334 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2645334 : Nat := 118140960795 + 2645334 * 2 ^ 59
def prefixEnd_2645334 : Nat := 4983230072969 + 3 ^ 40 * 2645334 * 2
def baseEnd_2645334 : Nat := 150925314853428705806593

theorem tailTrace_2645334 : CollatzResearch.WordTrace tailWord_2645334 prefixEnd_2645334 150925314853428705806593 := by
  unfold tailWord_2645334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030203587400886245231441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64322171598942786615802037 6030203587400886245231441)
  ·
    refine ⟨4522652690550664683923581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6030203587400886245231441 4522652690550664683923581)
    ·
      refine ⟨1695994758956499256471343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4522652690550664683923581 1695994758956499256471343)
      ·
        refine ⟨2543992138434748884707015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695994758956499256471343 2543992138434748884707015)
        ·
          refine ⟨3815988207652123327060523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2543992138434748884707015 3815988207652123327060523)
          ·
            refine ⟨5723982311478184990590785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3815988207652123327060523 5723982311478184990590785)
            ·
              refine ⟨4292986733608638742943089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5723982311478184990590785 4292986733608638742943089)
              ·
                refine ⟨3219740050206479057207317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4292986733608638742943089 3219740050206479057207317)
                ·
                  refine ⟨150925314853428705806593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3219740050206479057207317 150925314853428705806593)
                  ·
                    rfl

theorem cell23_2645334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2645334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645334 prefixEnd_2645334 := by exact prefixLift 2645334
  have htrace : WordTrace (prefixWord ++ tailWord_2645334) baseStart_2645334 baseEnd_2645334 := by
    simpa [prefixWord, tailWord_2645334, baseEnd_2645334] using wordTrace_append hprefix tailTrace_2645334
  have hstable : (prefixWord ++ tailWord_2645334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645334).length < 2 ^ (prefixWord ++ tailWord_2645334).sum := by decide
  have hdescent : baseEnd_2645334 < baseStart_2645334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645344 : List Nat := [2, 1, 1, 3, 4, 3, 2, 2, 1, 1, 3]
def baseStart_2645344 : Nat := 118140960795 + 2645344 * 2 ^ 59
def prefixEnd_2645344 : Nat := 4983230072969 + 3 ^ 40 * 2645344 * 2
def baseEnd_2645344 : Nat := 1358332968487403313134291

theorem tailTrace_2645344 : CollatzResearch.WordTrace tailWord_2645344 prefixEnd_2645344 1358332968487403313134291 := by
  unfold tailWord_2645344
  simp only [CollatzResearch.WordTrace]
  refine ⟨48241811064188975815783543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64322414752251967754378057 48241811064188975815783543)
  ·
    refine ⟨72362716596283463723675315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48241811064188975815783543 72362716596283463723675315)
    ·
      refine ⟨108544074894425195585512973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72362716596283463723675315 108544074894425195585512973)
      ·
        refine ⟨40704028085409448344567365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108544074894425195585512973 40704028085409448344567365)
        ·
          refine ⟨7632005266014271564606381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40704028085409448344567365 7632005266014271564606381)
          ·
            refine ⟨2862001974755351836727393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7632005266014271564606381 2862001974755351836727393)
            ·
              refine ⟨2146501481066513877545545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2862001974755351836727393 2146501481066513877545545)
              ·
                refine ⟨1609876110799885408159159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146501481066513877545545 1609876110799885408159159)
                ·
                  refine ⟨2414814166199828112238739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609876110799885408159159 2414814166199828112238739)
                  ·
                    refine ⟨3622221249299742168358109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2414814166199828112238739 3622221249299742168358109)
                    ·
                      refine ⟨1358332968487403313134291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3622221249299742168358109 1358332968487403313134291)
                      ·
                        rfl

theorem cell23_2645344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_2645344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645344 prefixEnd_2645344 := by exact prefixLift 2645344
  have htrace : WordTrace (prefixWord ++ tailWord_2645344) baseStart_2645344 baseEnd_2645344 := by
    simpa [prefixWord, tailWord_2645344, baseEnd_2645344] using wordTrace_append hprefix tailTrace_2645344
  have hstable : (prefixWord ++ tailWord_2645344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645344).length < 2 ^ (prefixWord ++ tailWord_2645344).sum := by decide
  have hdescent : baseEnd_2645344 < baseStart_2645344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645356 : List Nat := [2, 2, 1, 1, 5, 1, 3, 8]
def baseStart_2645356 : Nat := 118140960795 + 2645356 * 2 ^ 59
def prefixEnd_2645356 : Nat := 4983230072969 + 3 ^ 40 * 2645356 * 2
def baseEnd_2645356 : Nat := 50308856676120639488305

theorem tailTrace_2645356 : CollatzResearch.WordTrace tailWord_2645356 prefixEnd_2645356 50308856676120639488305 := by
  unfold tailWord_2645356
  simp only [CollatzResearch.WordTrace]
  refine ⟨48242029902167238840501961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64322706536222985120669281 48242029902167238840501961)
  ·
    refine ⟨36181522426625429130376471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48242029902167238840501961 36181522426625429130376471)
    ·
      refine ⟨54272283639938143695564707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36181522426625429130376471 54272283639938143695564707)
      ·
        refine ⟨81408425459907215543347061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54272283639938143695564707 81408425459907215543347061)
        ·
          refine ⟨7632039886866301457188787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81408425459907215543347061 7632039886866301457188787)
          ·
            refine ⟨11448059830299452185783181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7632039886866301457188787 11448059830299452185783181)
            ·
              refine ⟨4293022436362294569668693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11448059830299452185783181 4293022436362294569668693)
              ·
                refine ⟨50308856676120639488305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4293022436362294569668693 50308856676120639488305)
                ·
                  rfl

theorem cell23_2645356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 8].length) (baseStart_2645356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645356 prefixEnd_2645356 := by exact prefixLift 2645356
  have htrace : WordTrace (prefixWord ++ tailWord_2645356) baseStart_2645356 baseEnd_2645356 := by
    simpa [prefixWord, tailWord_2645356, baseEnd_2645356] using wordTrace_append hprefix tailTrace_2645356
  have hstable : (prefixWord ++ tailWord_2645356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645356).length < 2 ^ (prefixWord ++ tailWord_2645356).sum := by decide
  have hdescent : baseEnd_2645356 < baseStart_2645356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645383 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_2645383 : Nat := 118140960795 + 2645383 * 2 ^ 59
def prefixEnd_2645383 : Nat := 4983230072969 + 3 ^ 40 * 2645383 * 2
def baseEnd_2645383 : Nat := 1358352994232928660546611

theorem tailTrace_2645383 : CollatzResearch.WordTrace tailWord_2645383 prefixEnd_2645383 1358352994232928660546611 := by
  unfold tailWord_2645383
  simp only [CollatzResearch.WordTrace]
  refine ⟨96485044575236661292236803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64323363050157774194824535 96485044575236661292236803)
  ·
    refine ⟨144727566862854991938355205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96485044575236661292236803 144727566862854991938355205)
    ·
      refine ⟨27136418786785310988441601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144727566862854991938355205 27136418786785310988441601)
      ·
        refine ⟨20352314090088983241331201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27136418786785310988441601 20352314090088983241331201)
        ·
          refine ⟨15264235567566737430998401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20352314090088983241331201 15264235567566737430998401)
          ·
            refine ⟨11448176675675053073248801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15264235567566737430998401 11448176675675053073248801)
            ·
              refine ⟨8586132506756289804936601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11448176675675053073248801 8586132506756289804936601)
              ·
                refine ⟨6439599380067217353702451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8586132506756289804936601 6439599380067217353702451)
                ·
                  refine ⟨9659399070100826030553677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6439599380067217353702451 9659399070100826030553677)
                  ·
                    refine ⟨3622274651287809761457629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9659399070100826030553677 3622274651287809761457629)
                    ·
                      refine ⟨1358352994232928660546611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3622274651287809761457629 1358352994232928660546611)
                      ·
                        rfl

theorem cell23_2645383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_2645383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645383 prefixEnd_2645383 := by exact prefixLift 2645383
  have htrace : WordTrace (prefixWord ++ tailWord_2645383) baseStart_2645383 baseEnd_2645383 := by
    simpa [prefixWord, tailWord_2645383, baseEnd_2645383] using wordTrace_append hprefix tailTrace_2645383
  have hstable : (prefixWord ++ tailWord_2645383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645383).length < 2 ^ (prefixWord ++ tailWord_2645383).sum := by decide
  have hdescent : baseEnd_2645383 < baseStart_2645383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645384 : List Nat := [2, 1, 3, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_2645384 : Nat := 118140960795 + 2645384 * 2 ^ 59
def prefixEnd_2645384 : Nat := 4983230072969 + 3 ^ 40 * 2645384 * 2
def baseEnd_2645384 : Nat := 1358353507713583156634107

theorem tailTrace_2645384 : CollatzResearch.WordTrace tailWord_2645384 prefixEnd_2645384 1358353507713583156634107 := by
  unfold tailWord_2645384
  simp only [CollatzResearch.WordTrace]
  refine ⟨48242540524116519231511603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64323387365488692308682137 48242540524116519231511603)
  ·
    refine ⟨72363810786174778847267405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48242540524116519231511603 72363810786174778847267405)
    ·
      refine ⟨27136429044815542067725277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72363810786174778847267405 27136429044815542067725277)
      ·
        refine ⟨10176160891805828275396979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27136429044815542067725277 10176160891805828275396979)
        ·
          refine ⟨15264241337708742413095469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10176160891805828275396979 15264241337708742413095469)
          ·
            refine ⟨5724090501640778404910801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15264241337708742413095469 5724090501640778404910801)
            ·
              refine ⟨4293067876230583803683101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5724090501640778404910801 4293067876230583803683101)
              ·
                refine ⟨1609900453586468926381163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4293067876230583803683101 1609900453586468926381163)
                ·
                  refine ⟨2414850680379703389571745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609900453586468926381163 2414850680379703389571745)
                  ·
                    refine ⟨1811138010284777542178809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2414850680379703389571745 1811138010284777542178809)
                    ·
                      refine ⟨1358353507713583156634107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1811138010284777542178809 1358353507713583156634107)
                      ·
                        rfl

theorem cell23_2645384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_2645384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645384 prefixEnd_2645384 := by exact prefixLift 2645384
  have htrace : WordTrace (prefixWord ++ tailWord_2645384) baseStart_2645384 baseEnd_2645384 := by
    simpa [prefixWord, tailWord_2645384, baseEnd_2645384] using wordTrace_append hprefix tailTrace_2645384
  have hstable : (prefixWord ++ tailWord_2645384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645384).length < 2 ^ (prefixWord ++ tailWord_2645384).sum := by decide
  have hdescent : baseEnd_2645384 < baseStart_2645384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645394 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2645394 : Nat := 118140960795 + 2645394 * 2 ^ 59
def prefixEnd_2645394 : Nat := 4983230072969 + 3 ^ 40 * 2645394 * 2
def baseEnd_2645394 : Nat := 452786214173376039169687

theorem tailTrace_2645394 : CollatzResearch.WordTrace tailWord_2645394 prefixEnd_2645394 452786214173376039169687 := by
  unfold tailWord_2645394
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121361444549202542721809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64323630518797873447258157 24121361444549202542721809)
  ·
    refine ⟨18091021083411901907041357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24121361444549202542721809 18091021083411901907041357)
    ·
      refine ⟨6784132906279463215140509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18091021083411901907041357 6784132906279463215140509)
      ·
        refine ⟨2544049839854798705677691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6784132906279463215140509 2544049839854798705677691)
        ·
          refine ⟨3816074759782198058516537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544049839854798705677691 3816074759782198058516537)
          ·
            refine ⟨2862056069836648543887403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3816074759782198058516537 2862056069836648543887403)
            ·
              refine ⟨4293084104754972815831105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862056069836648543887403 4293084104754972815831105)
              ·
                refine ⟨3219813078566229611873329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4293084104754972815831105 3219813078566229611873329)
                ·
                  refine ⟨2414859808924672208904997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3219813078566229611873329 2414859808924672208904997)
                  ·
                    refine ⟨452786214173376039169687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2414859808924672208904997 452786214173376039169687)
                    ·
                      rfl

theorem cell23_2645394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2645394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645394 prefixEnd_2645394 := by exact prefixLift 2645394
  have htrace : WordTrace (prefixWord ++ tailWord_2645394) baseStart_2645394 baseEnd_2645394 := by
    simpa [prefixWord, tailWord_2645394, baseEnd_2645394] using wordTrace_append hprefix tailTrace_2645394
  have hstable : (prefixWord ++ tailWord_2645394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645394).length < 2 ^ (prefixWord ++ tailWord_2645394).sum := by decide
  have hdescent : baseEnd_2645394 < baseStart_2645394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645440 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 4, 2, 2]
def baseStart_2645440 : Nat := 118140960795 + 2645440 * 2 ^ 59
def prefixEnd_2645440 : Nat := 4983230072969 + 3 ^ 40 * 2645440 * 2
def baseEnd_2645440 : Nat := 1358382262630234937533849

theorem tailTrace_2645440 : CollatzResearch.WordTrace tailWord_2645440 prefixEnd_2645440 1358382262630234937533849 := by
  unfold tailWord_2645440
  simp only [CollatzResearch.WordTrace]
  refine ⟨48243561768015080013530887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64324749024020106684707849 48243561768015080013530887)
  ·
    refine ⟨72365342652022620020296331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48243561768015080013530887 72365342652022620020296331)
    ·
      refine ⟨108548013978033930030444497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72365342652022620020296331 108548013978033930030444497)
      ·
        refine ⟨81411010483525447522833373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108548013978033930030444497 81411010483525447522833373)
        ·
          refine ⟨30529128931322042821062515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81411010483525447522833373 30529128931322042821062515)
          ·
            refine ⟨45793693396983064231593773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30529128931322042821062515 45793693396983064231593773)
            ·
              refine ⟨17172635023868649086847665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45793693396983064231593773 17172635023868649086847665)
              ·
                refine ⟨12879476267901486815135749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17172635023868649086847665 12879476267901486815135749)
                ·
                  refine ⟨2414901800231528777837953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12879476267901486815135749 2414901800231528777837953)
                  ·
                    refine ⟨1811176350173646583378465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2414901800231528777837953 1811176350173646583378465)
                    ·
                      refine ⟨1358382262630234937533849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1811176350173646583378465 1358382262630234937533849)
                      ·
                        rfl

theorem cell23_2645440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_2645440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645440 prefixEnd_2645440 := by exact prefixLift 2645440
  have htrace : WordTrace (prefixWord ++ tailWord_2645440) baseStart_2645440 baseEnd_2645440 := by
    simpa [prefixWord, tailWord_2645440, baseEnd_2645440] using wordTrace_append hprefix tailTrace_2645440
  have hstable : (prefixWord ++ tailWord_2645440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645440).length < 2 ^ (prefixWord ++ tailWord_2645440).sum := by decide
  have hdescent : baseEnd_2645440 < baseStart_2645440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645463 : List Nat := [1, 1, 3, 2, 1, 1, 1, 8, 5]
def baseStart_2645463 : Nat := 118140960795 + 2645463 * 2 ^ 59
def prefixEnd_2645463 : Nat := 4983230072969 + 3 ^ 40 * 2645463 * 2
def baseEnd_2645463 : Nat := 150932674742809816394027

theorem tailTrace_2645463 : CollatzResearch.WordTrace tailWord_2645463 prefixEnd_2645463 150932674742809816394027 := by
  unfold tailWord_2645463
  simp only [CollatzResearch.WordTrace]
  refine ⟨96487962414946834955149043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64325308276631223303432695 96487962414946834955149043)
  ·
    refine ⟨144731943622420252432723565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96487962414946834955149043 144731943622420252432723565)
    ·
      refine ⟨54274478858407594662271337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144731943622420252432723565 54274478858407594662271337)
      ·
        refine ⟨40705859143805695996703503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54274478858407594662271337 40705859143805695996703503)
        ·
          refine ⟨61058788715708543995055255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40705859143805695996703503 61058788715708543995055255)
          ·
            refine ⟨91588183073562815992582883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61058788715708543995055255 91588183073562815992582883)
            ·
              refine ⟨137382274610344223988874325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91588183073562815992582883 137382274610344223988874325)
              ·
                refine ⟨1609948530589971374869621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 137382274610344223988874325 1609948530589971374869621)
                ·
                  refine ⟨150932674742809816394027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1609948530589971374869621 150932674742809816394027)
                  ·
                    rfl

theorem cell23_2645463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 5].length) (baseStart_2645463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645463 prefixEnd_2645463 := by exact prefixLift 2645463
  have htrace : WordTrace (prefixWord ++ tailWord_2645463) baseStart_2645463 baseEnd_2645463 := by
    simpa [prefixWord, tailWord_2645463, baseEnd_2645463] using wordTrace_append hprefix tailTrace_2645463
  have hstable : (prefixWord ++ tailWord_2645463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645463).length < 2 ^ (prefixWord ++ tailWord_2645463).sum := by decide
  have hdescent : baseEnd_2645463 < baseStart_2645463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645476 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_2645476 : Nat := 118140960795 + 2645476 * 2 ^ 59
def prefixEnd_2645476 : Nat := 4983230072969 + 3 ^ 40 * 2645476 * 2
def baseEnd_2645476 : Nat := 452800249311265598894561

theorem tailTrace_2645476 : CollatzResearch.WordTrace tailWord_2645476 prefixEnd_2645476 452800249311265598894561 := by
  unfold tailWord_2645476
  simp only [CollatzResearch.WordTrace]
  refine ⟨48244218281949869087686141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64325624375933158783581521 48244218281949869087686141)
  ·
    refine ⟨18091581855731200907882303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48244218281949869087686141 18091581855731200907882303)
    ·
      refine ⟨27137372783596801361823455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18091581855731200907882303 27137372783596801361823455)
      ·
        refine ⟨40706059175395202042735183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27137372783596801361823455 40706059175395202042735183)
        ·
          refine ⟨61059088763092803064102775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40706059175395202042735183 61059088763092803064102775)
          ·
            refine ⟨91588633144639204596154163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61059088763092803064102775 91588633144639204596154163)
            ·
              refine ⟨137382949716958806894231245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91588633144639204596154163 137382949716958806894231245)
              ·
                refine ⟨51518606143859552585336717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137382949716958806894231245 51518606143859552585336717)
                ·
                  refine ⟨19319477303947332219501269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51518606143859552585336717 19319477303947332219501269)
                  ·
                    refine ⟨452800249311265598894561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19319477303947332219501269 452800249311265598894561)
                    ·
                      rfl

theorem cell23_2645476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_2645476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645476 prefixEnd_2645476 := by exact prefixLift 2645476
  have htrace : WordTrace (prefixWord ++ tailWord_2645476) baseStart_2645476 baseEnd_2645476 := by
    simpa [prefixWord, tailWord_2645476, baseEnd_2645476] using wordTrace_append hprefix tailTrace_2645476
  have hstable : (prefixWord ++ tailWord_2645476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645476).length < 2 ^ (prefixWord ++ tailWord_2645476).sum := by decide
  have hdescent : baseEnd_2645476 < baseStart_2645476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645483 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 4, 5, 2]
def baseStart_2645483 : Nat := 118140960795 + 2645483 * 2 ^ 59
def prefixEnd_2645483 : Nat := 4983230072969 + 3 ^ 40 * 2645483 * 2
def baseEnd_2645483 : Nat := 1358404342298378269296151

theorem tailTrace_2645483 : CollatzResearch.WordTrace tailWord_2645483 prefixEnd_2645483 1358404342298378269296151 := by
  unfold tailWord_2645483
  simp only [CollatzResearch.WordTrace]
  refine ⟨96488691874874378370877103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64325794583249585580584735 96488691874874378370877103)
  ·
    refine ⟨144733037812311567556315655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96488691874874378370877103 144733037812311567556315655)
    ·
      refine ⟨217099556718467351334473483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144733037812311567556315655 217099556718467351334473483)
      ·
        refine ⟨325649335077701027001710225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217099556718467351334473483 325649335077701027001710225)
        ·
          refine ⟨244237001308275770251282669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325649335077701027001710225 244237001308275770251282669)
          ·
            refine ⟨91588875490603413844231001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244237001308275770251282669 91588875490603413844231001)
            ·
              refine ⟨68691656617952560383173251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91588875490603413844231001 68691656617952560383173251)
              ·
                refine ⟨103037484926928840574759877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68691656617952560383173251 103037484926928840574759877)
                ·
                  refine ⟨19319528423799157607767477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103037484926928840574759877 19319528423799157607767477)
                  ·
                    refine ⟨1811205789731171025728201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19319528423799157607767477 1811205789731171025728201)
                    ·
                      refine ⟨1358404342298378269296151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1811205789731171025728201 1358404342298378269296151)
                      ·
                        rfl

theorem cell23_2645483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 5, 2].length) (baseStart_2645483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645483 prefixEnd_2645483 := by exact prefixLift 2645483
  have htrace : WordTrace (prefixWord ++ tailWord_2645483) baseStart_2645483 baseEnd_2645483 := by
    simpa [prefixWord, tailWord_2645483, baseEnd_2645483] using wordTrace_append hprefix tailTrace_2645483
  have hstable : (prefixWord ++ tailWord_2645483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645483).length < 2 ^ (prefixWord ++ tailWord_2645483).sum := by decide
  have hdescent : baseEnd_2645483 < baseStart_2645483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645513 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_2645513 : Nat := 118140960795 + 2645513 * 2 ^ 59
def prefixEnd_2645513 : Nat := 4983230072969 + 3 ^ 40 * 2645513 * 2
def baseEnd_2645513 : Nat := 1358419746718013151921013

theorem tailTrace_2645513 : CollatzResearch.WordTrace tailWord_2645513 prefixEnd_2645513 1358419746718013151921013 := by
  unfold tailWord_2645513
  simp only [CollatzResearch.WordTrace]
  refine ⟨96489786064765693494469193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64326524043177128996312795 96489786064765693494469193)
  ·
    refine ⟨72367339548574270120851895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96489786064765693494469193 72367339548574270120851895)
    ·
      refine ⟨108551009322861405181277843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72367339548574270120851895 108551009322861405181277843)
      ·
        refine ⟨162826513984292107771916765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108551009322861405181277843 162826513984292107771916765)
        ·
          refine ⟨61059942744109540414468787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162826513984292107771916765 61059942744109540414468787)
          ·
            refine ⟨91589914116164310621703181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61059942744109540414468787 91589914116164310621703181)
            ·
              refine ⟨34346217793561616483138693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91589914116164310621703181 34346217793561616483138693)
              ·
                refine ⟨6439915836292803090588505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34346217793561616483138693 6439915836292803090588505)
                ·
                  refine ⟨4829936877219602317941379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6439915836292803090588505 4829936877219602317941379)
                  ·
                    refine ⟨7244905315829403476912069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4829936877219602317941379 7244905315829403476912069)
                    ·
                      refine ⟨1358419746718013151921013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7244905315829403476912069 1358419746718013151921013)
                      ·
                        rfl

theorem cell23_2645513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_2645513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645513 prefixEnd_2645513 := by exact prefixLift 2645513
  have htrace : WordTrace (prefixWord ++ tailWord_2645513) baseStart_2645513 baseEnd_2645513 := by
    simpa [prefixWord, tailWord_2645513, baseEnd_2645513] using wordTrace_append hprefix tailTrace_2645513
  have hstable : (prefixWord ++ tailWord_2645513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645513).length < 2 ^ (prefixWord ++ tailWord_2645513).sum := by decide
  have hdescent : baseEnd_2645513 < baseStart_2645513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645544 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2645544 : Nat := 118140960795 + 2645544 * 2 ^ 59
def prefixEnd_2645544 : Nat := 4983230072969 + 3 ^ 40 * 2645544 * 2
def baseEnd_2645544 : Nat := 452811888206100843544457

theorem tailTrace_2645544 : CollatzResearch.WordTrace tailWord_2645544 prefixEnd_2645544 452811888206100843544457 := by
  unfold tailWord_2645544
  simp only [CollatzResearch.WordTrace]
  refine ⟨48245458363826692894423843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64327277818435590525898457 48245458363826692894423843)
  ·
    refine ⟨72368187545740039341635765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48245458363826692894423843 72368187545740039341635765)
    ·
      refine ⟨6784517582413128688278353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72368187545740039341635765 6784517582413128688278353)
      ·
        refine ⟨5088388186809846516208765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6784517582413128688278353 5088388186809846516208765)
        ·
          refine ⟨1908145570053692443578287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5088388186809846516208765 1908145570053692443578287)
          ·
            refine ⟨2862218355080538665367431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908145570053692443578287 2862218355080538665367431)
            ·
              refine ⟨4293327532620807998051147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862218355080538665367431 4293327532620807998051147)
              ·
                refine ⟨6439991298931211997076721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4293327532620807998051147 6439991298931211997076721)
                ·
                  refine ⟨4829993474198408997807541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6439991298931211997076721 4829993474198408997807541)
                  ·
                    refine ⟨452811888206100843544457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4829993474198408997807541 452811888206100843544457)
                    ·
                      rfl

theorem cell23_2645544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2645544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645544 prefixEnd_2645544 := by exact prefixLift 2645544
  have htrace : WordTrace (prefixWord ++ tailWord_2645544) baseStart_2645544 baseEnd_2645544 := by
    simpa [prefixWord, tailWord_2645544, baseEnd_2645544] using wordTrace_append hprefix tailTrace_2645544
  have hstable : (prefixWord ++ tailWord_2645544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645544).length < 2 ^ (prefixWord ++ tailWord_2645544).sum := by decide
  have hdescent : baseEnd_2645544 < baseStart_2645544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645557 : List Nat := [1, 3, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_2645557 : Nat := 118140960795 + 2645557 * 2 ^ 59
def prefixEnd_2645557 : Nat := 4983230072969 + 3 ^ 40 * 2645557 * 2
def baseEnd_2645557 : Nat := 452814113288936993256937

theorem tailTrace_2645557 : CollatzResearch.WordTrace tailWord_2645557 prefixEnd_2645557 452814113288936993256937 := by
  unfold tailWord_2645557
  simp only [CollatzResearch.WordTrace]
  refine ⟨96491390876606289009070925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64327593917737526006047283 96491390876606289009070925)
  ·
    refine ⟨36184271578727358378401597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96491390876606289009070925 36184271578727358378401597)
    ·
      refine ⟨13569101842022759391900599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36184271578727358378401597 13569101842022759391900599)
      ·
        refine ⟨20353652763034139087850899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13569101842022759391900599 20353652763034139087850899)
        ·
          refine ⟨30530479144551208631776349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20353652763034139087850899 30530479144551208631776349)
          ·
            refine ⟨11448929679206703236916131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30530479144551208631776349 11448929679206703236916131)
            ·
              refine ⟨17173394518810054855374197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11448929679206703236916131 17173394518810054855374197)
              ·
                refine ⟨1610005736138442642691331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17173394518810054855374197 1610005736138442642691331)
                ·
                  refine ⟨2415008604207663964036997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610005736138442642691331 2415008604207663964036997)
                  ·
                    refine ⟨452814113288936993256937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415008604207663964036997 452814113288936993256937)
                    ·
                      rfl

theorem cell23_2645557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_2645557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645557 prefixEnd_2645557 := by exact prefixLift 2645557
  have htrace : WordTrace (prefixWord ++ tailWord_2645557) baseStart_2645557 baseEnd_2645557 := by
    simpa [prefixWord, tailWord_2645557, baseEnd_2645557] using wordTrace_append hprefix tailTrace_2645557
  have hstable : (prefixWord ++ tailWord_2645557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645557).length < 2 ^ (prefixWord ++ tailWord_2645557).sum := by decide
  have hdescent : baseEnd_2645557 < baseStart_2645557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645643 : List Nat := [1, 1, 1, 1, 4, 1, 6, 8]
def baseStart_2645643 : Nat := 118140960795 + 2645643 * 2 ^ 59
def prefixEnd_2645643 : Nat := 4983230072969 + 3 ^ 40 * 2645643 * 2
def baseEnd_2645643 : Nat := 50314314785299912714645

theorem tailTrace_2645643 : CollatzResearch.WordTrace tailWord_2645643 prefixEnd_2645643 50314314785299912714645 := by
  unfold tailWord_2645643
  simp only [CollatzResearch.WordTrace]
  refine ⟨96494527554294725696701583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64329685036196483797801055 96494527554294725696701583)
  ·
    refine ⟨144741791331442088545052375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96494527554294725696701583 144741791331442088545052375)
    ·
      refine ⟨217112686997163132817578563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144741791331442088545052375 217112686997163132817578563)
      ·
        refine ⟨325669030495744699226367845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217112686997163132817578563 325669030495744699226367845)
        ·
          refine ⟨61062943217952131104943971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 325669030495744699226367845 61062943217952131104943971)
          ·
            refine ⟨91594414826928196657415957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61062943217952131104943971 91594414826928196657415957)
            ·
              refine ⟨4293488195012259218316373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91594414826928196657415957 4293488195012259218316373)
              ·
                refine ⟨50314314785299912714645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4293488195012259218316373 50314314785299912714645)
                ·
                  rfl

theorem cell23_2645643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 8].length) (baseStart_2645643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645643 prefixEnd_2645643 := by exact prefixLift 2645643
  have htrace : WordTrace (prefixWord ++ tailWord_2645643) baseStart_2645643 baseEnd_2645643 := by
    simpa [prefixWord, tailWord_2645643, baseEnd_2645643] using wordTrace_append hprefix tailTrace_2645643
  have hstable : (prefixWord ++ tailWord_2645643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645643).length < 2 ^ (prefixWord ++ tailWord_2645643).sum := by decide
  have hdescent : baseEnd_2645643 < baseStart_2645643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645710 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2645710 : Nat := 118140960795 + 2645710 * 2 ^ 59
def prefixEnd_2645710 : Nat := 4983230072969 + 3 ^ 40 * 2645710 * 2
def baseEnd_2645710 : Nat := 1358520902406948881157607

theorem tailTrace_2645710 : CollatzResearch.WordTrace tailWord_2645710 prefixEnd_2645710 1358520902406948881157607 := by
  unfold tailWord_2645710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12062121405631499517423823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64331314163367997426260389 12062121405631499517423823)
  ·
    refine ⟨18093182108447249276135735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12062121405631499517423823 18093182108447249276135735)
    ·
      refine ⟨27139773162670873914203603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18093182108447249276135735 27139773162670873914203603)
      ·
        refine ⟨40709659744006310871305405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27139773162670873914203603 40709659744006310871305405)
        ·
          refine ⟨15266122404002366576739527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40709659744006310871305405 15266122404002366576739527)
          ·
            refine ⟨22899183606003549865109291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15266122404002366576739527 22899183606003549865109291)
            ·
              refine ⟨34348775409005324797663937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22899183606003549865109291 34348775409005324797663937)
              ·
                refine ⟨25761581556753993598247953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34348775409005324797663937 25761581556753993598247953)
                ·
                  refine ⟨19321186167565495198685965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25761581556753993598247953 19321186167565495198685965)
                  ·
                    refine ⟨7245444812837060699507237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19321186167565495198685965 7245444812837060699507237)
                    ·
                      refine ⟨1358520902406948881157607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7245444812837060699507237 1358520902406948881157607)
                      ·
                        rfl

theorem cell23_2645710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2645710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645710 prefixEnd_2645710 := by exact prefixLift 2645710
  have htrace : WordTrace (prefixWord ++ tailWord_2645710) baseStart_2645710 baseEnd_2645710 := by
    simpa [prefixWord, tailWord_2645710, baseEnd_2645710] using wordTrace_append hprefix tailTrace_2645710
  have hstable : (prefixWord ++ tailWord_2645710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645710).length < 2 ^ (prefixWord ++ tailWord_2645710).sum := by decide
  have hdescent : baseEnd_2645710 < baseStart_2645710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645714 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_2645714 : Nat := 118140960795 + 2645714 * 2 ^ 59
def prefixEnd_2645714 : Nat := 4983230072969 + 3 ^ 40 * 2645714 * 2
def baseEnd_2645714 : Nat := 1358522956329566865507589

theorem tailTrace_2645714 : CollatzResearch.WordTrace tailWord_2645714 prefixEnd_2645714 1358522956329566865507589 := by
  unfold tailWord_2645714
  simp only [CollatzResearch.WordTrace]
  refine ⟨24124279284259376205634049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64331411424691669881690797 24124279284259376205634049)
  ·
    refine ⟨18093209463194532154225537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24124279284259376205634049 18093209463194532154225537)
    ·
      refine ⟨13569907097395899115669153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18093209463194532154225537 13569907097395899115669153)
      ·
        refine ⟨10177430323046924336751865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13569907097395899115669153 10177430323046924336751865)
        ·
          refine ⟨7633072742285193252563899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10177430323046924336751865 7633072742285193252563899)
          ·
            refine ⟨11449609113427789878845849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7633072742285193252563899 11449609113427789878845849)
            ·
              refine ⟨8587206835070842409134387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11449609113427789878845849 8587206835070842409134387)
              ·
                refine ⟨12880810252606263613701581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8587206835070842409134387 12880810252606263613701581)
                ·
                  refine ⟨4830303844727348855138093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12880810252606263613701581 4830303844727348855138093)
                  ·
                    refine ⟨1811363941772755820676785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4830303844727348855138093 1811363941772755820676785)
                    ·
                      refine ⟨1358522956329566865507589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1811363941772755820676785 1358522956329566865507589)
                      ·
                        rfl

theorem cell23_2645714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_2645714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645714 prefixEnd_2645714 := by exact prefixLift 2645714
  have htrace : WordTrace (prefixWord ++ tailWord_2645714) baseStart_2645714 baseEnd_2645714 := by
    simpa [prefixWord, tailWord_2645714, baseEnd_2645714] using wordTrace_append hprefix tailTrace_2645714
  have hstable : (prefixWord ++ tailWord_2645714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645714).length < 2 ^ (prefixWord ++ tailWord_2645714).sum := by decide
  have hdescent : baseEnd_2645714 < baseStart_2645714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645725 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2645725 : Nat := 118140960795 + 2645725 * 2 ^ 59
def prefixEnd_2645725 : Nat := 4983230072969 + 3 ^ 40 * 2645725 * 2
def baseEnd_2645725 : Nat := 1358528604616766322470039

theorem tailTrace_2645725 : CollatzResearch.WordTrace tailWord_2645725 prefixEnd_2645725 1358528604616766322470039 := by
  unfold tailWord_2645725
  simp only [CollatzResearch.WordTrace]
  refine ⟨96497518339997653701186629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64331678893331769134124419 96497518339997653701186629)
  ·
    refine ⟨18093284688749560068972493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96497518339997653701186629 18093284688749560068972493)
    ·
      refine ⟨6784981758281085025864685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18093284688749560068972493 6784981758281085025864685)
      ·
        refine ⟨2544368159355406884699257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6784981758281085025864685 2544368159355406884699257)
        ·
          refine ⟨1908276119516555163524443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2544368159355406884699257 1908276119516555163524443)
          ·
            refine ⟨2862414179274832745286665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908276119516555163524443 2862414179274832745286665)
            ·
              refine ⟨2146810634456124558964999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2862414179274832745286665 2146810634456124558964999)
              ·
                refine ⟨3220215951684186838447499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146810634456124558964999 3220215951684186838447499)
                ·
                  refine ⟨4830323927526280257671249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220215951684186838447499 4830323927526280257671249)
                  ·
                    refine ⟨3622742945644710193253437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4830323927526280257671249 3622742945644710193253437)
                    ·
                      refine ⟨1358528604616766322470039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3622742945644710193253437 1358528604616766322470039)
                      ·
                        rfl

theorem cell23_2645725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2645725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645725 prefixEnd_2645725 := by exact prefixLift 2645725
  have htrace : WordTrace (prefixWord ++ tailWord_2645725) baseStart_2645725 baseEnd_2645725 := by
    simpa [prefixWord, tailWord_2645725, baseEnd_2645725] using wordTrace_append hprefix tailTrace_2645725
  have hstable : (prefixWord ++ tailWord_2645725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645725).length < 2 ^ (prefixWord ++ tailWord_2645725).sum := by decide
  have hdescent : baseEnd_2645725 < baseStart_2645725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645727 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 1, 4, 2]
def baseStart_2645727 : Nat := 118140960795 + 2645727 * 2 ^ 59
def prefixEnd_2645727 : Nat := 4983230072969 + 3 ^ 40 * 2645727 * 2
def baseEnd_2645727 : Nat := 1358529631578075314645029

theorem tailTrace_2645727 : CollatzResearch.WordTrace tailWord_2645727 prefixEnd_2645727 1358529631578075314645029 := by
  unfold tailWord_2645727
  simp only [CollatzResearch.WordTrace]
  refine ⟨96497591285990408042759435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64331727523993605361839623 96497591285990408042759435)
  ·
    refine ⟨144746386928985612064139153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96497591285990408042759435 144746386928985612064139153)
    ·
      refine ⟨108559790196739209048104365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144746386928985612064139153 108559790196739209048104365)
      ·
        refine ⟨40709921323777203393039137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108559790196739209048104365 40709921323777203393039137)
        ·
          refine ⟨30532440992832902544779353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40709921323777203393039137 30532440992832902544779353)
          ·
            refine ⟨22899330744624676908584515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30532440992832902544779353 22899330744624676908584515)
            ·
              refine ⟨34348996116937015362876773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22899330744624676908584515 34348996116937015362876773)
              ·
                refine ⟨6440436771925690380539395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34348996116937015362876773 6440436771925690380539395)
                ·
                  refine ⟨9660655157888535570809093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6440436771925690380539395 9660655157888535570809093)
                  ·
                    refine ⟨1811372842104100419526705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9660655157888535570809093 1811372842104100419526705)
                    ·
                      refine ⟨1358529631578075314645029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1811372842104100419526705 1358529631578075314645029)
                      ·
                        rfl

theorem cell23_2645727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_2645727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645727 prefixEnd_2645727 := by exact prefixLift 2645727
  have htrace : WordTrace (prefixWord ++ tailWord_2645727) baseStart_2645727 baseEnd_2645727 := by
    simpa [prefixWord, tailWord_2645727, baseEnd_2645727] using wordTrace_append hprefix tailTrace_2645727
  have hstable : (prefixWord ++ tailWord_2645727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645727).length < 2 ^ (prefixWord ++ tailWord_2645727).sum := by decide
  have hdescent : baseEnd_2645727 < baseStart_2645727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645731 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2645731 : Nat := 118140960795 + 2645731 * 2 ^ 59
def prefixEnd_2645731 : Nat := 4983230072969 + 3 ^ 40 * 2645731 * 2
def baseEnd_2645731 : Nat := 1358531685500693298995011

theorem tailTrace_2645731 : CollatzResearch.WordTrace tailWord_2645731 prefixEnd_2645731 1358531685500693298995011 := by
  unfold tailWord_2645731
  simp only [CollatzResearch.WordTrace]
  refine ⟨96497737177975916725905047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64331824785317277817270031 96497737177975916725905047)
  ·
    refine ⟨144746605766963875088857571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96497737177975916725905047 144746605766963875088857571)
    ·
      refine ⟨217119908650445812633286357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144746605766963875088857571 217119908650445812633286357)
      ·
        refine ⟨5088747858994823733592649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 217119908650445812633286357 5088747858994823733592649)
        ·
          refine ⟨3816560894246117800194487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5088747858994823733592649 3816560894246117800194487)
          ·
            refine ⟨5724841341369176700291731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816560894246117800194487 5724841341369176700291731)
            ·
              refine ⟨8587262012053765050437597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724841341369176700291731 8587262012053765050437597)
              ·
                refine ⟨3220223254520161893914099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8587262012053765050437597 3220223254520161893914099)
                ·
                  refine ⟨4830334881780242840871149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220223254520161893914099 4830334881780242840871149)
                  ·
                    refine ⟨1811375580667591065326681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4830334881780242840871149 1811375580667591065326681)
                    ·
                      refine ⟨1358531685500693298995011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1811375580667591065326681 1358531685500693298995011)
                      ·
                        rfl

theorem cell23_2645731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2645731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645731 prefixEnd_2645731 := by exact prefixLift 2645731
  have htrace : WordTrace (prefixWord ++ tailWord_2645731) baseStart_2645731 baseEnd_2645731 := by
    simpa [prefixWord, tailWord_2645731, baseEnd_2645731] using wordTrace_append hprefix tailTrace_2645731
  have hstable : (prefixWord ++ tailWord_2645731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645731).length < 2 ^ (prefixWord ++ tailWord_2645731).sum := by decide
  have hdescent : baseEnd_2645731 < baseStart_2645731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645740 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2645740 : Nat := 118140960795 + 2645740 * 2 ^ 59
def prefixEnd_2645740 : Nat := 4983230072969 + 3 ^ 40 * 2645740 * 2
def baseEnd_2645740 : Nat := 1358536306826583763782469

theorem tailTrace_2645740 : CollatzResearch.WordTrace tailWord_2645740 prefixEnd_2645740 1358536306826583763782469 := by
  unfold tailWord_2645740
  simp only [CollatzResearch.WordTrace]
  refine ⟨48249032717471655631491337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64332043623295540841988449 48249032717471655631491337)
  ·
    refine ⟨36186774538103741723618503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48249032717471655631491337 36186774538103741723618503)
    ·
      refine ⟨54280161807155612585427755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36186774538103741723618503 54280161807155612585427755)
      ·
        refine ⟨81420242710733418878141633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54280161807155612585427755 81420242710733418878141633)
        ·
          refine ⟨61065182033050064158606225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81420242710733418878141633 61065182033050064158606225)
          ·
            refine ⟨45798886524787548118954669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61065182033050064158606225 45798886524787548118954669)
            ·
              refine ⟨17174582446795330544608001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45798886524787548118954669 17174582446795330544608001)
              ·
                refine ⟨12880936835096497908456001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17174582446795330544608001 12880936835096497908456001)
                ·
                  refine ⟨9660702626322373431342001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12880936835096497908456001 9660702626322373431342001)
                  ·
                    refine ⟨7245526969741780073506501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9660702626322373431342001 7245526969741780073506501)
                    ·
                      refine ⟨1358536306826583763782469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7245526969741780073506501 1358536306826583763782469)
                      ·
                        rfl

theorem cell23_2645740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2645740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645740 prefixEnd_2645740 := by exact prefixLift 2645740
  have htrace : WordTrace (prefixWord ++ tailWord_2645740) baseStart_2645740 baseEnd_2645740 := by
    simpa [prefixWord, tailWord_2645740, baseEnd_2645740] using wordTrace_append hprefix tailTrace_2645740
  have hstable : (prefixWord ++ tailWord_2645740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645740).length < 2 ^ (prefixWord ++ tailWord_2645740).sum := by decide
  have hdescent : baseEnd_2645740 < baseStart_2645740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645744 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 2, 2, 2]
def baseStart_2645744 : Nat := 118140960795 + 2645744 * 2 ^ 59
def prefixEnd_2645744 : Nat := 4983230072969 + 3 ^ 40 * 2645744 * 2
def baseEnd_2645744 : Nat := 1358538360749201748132451

theorem tailTrace_2645744 : CollatzResearch.WordTrace tailWord_2645744 prefixEnd_2645744 1358538360749201748132451 := by
  unfold tailWord_2645744
  simp only [CollatzResearch.WordTrace]
  refine ⟨48249105663464409973064143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64332140884619213297418857 48249105663464409973064143)
  ·
    refine ⟨72373658495196614959596215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48249105663464409973064143 72373658495196614959596215)
    ·
      refine ⟨108560487742794922439394323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72373658495196614959596215 108560487742794922439394323)
      ·
        refine ⟨162840731614192383659091485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108560487742794922439394323 162840731614192383659091485)
        ·
          refine ⟨61065274355322143872159307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162840731614192383659091485 61065274355322143872159307)
          ·
            refine ⟨91597911532983215808238961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61065274355322143872159307 91597911532983215808238961)
            ·
              refine ⟨68698433649737411856179221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91597911532983215808238961 68698433649737411856179221)
              ·
                refine ⟨3220239077331441180758401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68698433649737411856179221 3220239077331441180758401)
                ·
                  refine ⟨2415179307998580885568801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3220239077331441180758401 2415179307998580885568801)
                  ·
                    refine ⟨1811384480998935664176601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2415179307998580885568801 1811384480998935664176601)
                    ·
                      refine ⟨1358538360749201748132451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1811384480998935664176601 1358538360749201748132451)
                      ·
                        rfl

theorem cell23_2645744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 2, 2].length) (baseStart_2645744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645744 prefixEnd_2645744 := by exact prefixLift 2645744
  have htrace : WordTrace (prefixWord ++ tailWord_2645744) baseStart_2645744 baseEnd_2645744 := by
    simpa [prefixWord, tailWord_2645744, baseEnd_2645744] using wordTrace_append hprefix tailTrace_2645744
  have hstable : (prefixWord ++ tailWord_2645744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645744).length < 2 ^ (prefixWord ++ tailWord_2645744).sum := by decide
  have hdescent : baseEnd_2645744 < baseStart_2645744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645797 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_2645797 : Nat := 118140960795 + 2645797 * 2 ^ 59
def prefixEnd_2645797 : Nat := 4983230072969 + 3 ^ 40 * 2645797 * 2
def baseEnd_2645797 : Nat := 452855191741296680256569

theorem tailTrace_2645797 : CollatzResearch.WordTrace tailWord_2645797 prefixEnd_2645797 452855191741296680256569 := by
  unfold tailWord_2645797
  simp only [CollatzResearch.WordTrace]
  refine ⟨96500144395736809997807645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64333429597157873331871763 96500144395736809997807645)
  ·
    refine ⟨36187554148401303749177867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96500144395736809997807645 36187554148401303749177867)
    ·
      refine ⟨54281331222601955623766801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36187554148401303749177867 54281331222601955623766801)
      ·
        refine ⟨40710998416951466717825101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54281331222601955623766801 40710998416951466717825101)
        ·
          refine ⟨15266624406356800019184413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40710998416951466717825101 15266624406356800019184413)
          ·
            refine ⟨5724984152383800007194155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15266624406356800019184413 5724984152383800007194155)
            ·
              refine ⟨8587476228575700010791233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724984152383800007194155 8587476228575700010791233)
              ·
                refine ⟨6440607171431775008093425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8587476228575700010791233 6440607171431775008093425)
                ·
                  refine ⟨4830455378573831256070069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6440607171431775008093425 4830455378573831256070069)
                  ·
                    refine ⟨452855191741296680256569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4830455378573831256070069 452855191741296680256569)
                    ·
                      rfl

theorem cell23_2645797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_2645797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645797 prefixEnd_2645797 := by exact prefixLift 2645797
  have htrace : WordTrace (prefixWord ++ tailWord_2645797) baseStart_2645797 baseEnd_2645797 := by
    simpa [prefixWord, tailWord_2645797, baseEnd_2645797] using wordTrace_append hprefix tailTrace_2645797
  have hstable : (prefixWord ++ tailWord_2645797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645797).length < 2 ^ (prefixWord ++ tailWord_2645797).sum := by decide
  have hdescent : baseEnd_2645797 < baseStart_2645797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645857 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 6]
def baseStart_2645857 : Nat := 118140960795 + 2645857 * 2 ^ 59
def prefixEnd_2645857 : Nat := 4983230072969 + 3 ^ 40 * 2645857 * 2
def baseEnd_2645857 : Nat := 150955153784795534002159

theorem tailTrace_2645857 : CollatzResearch.WordTrace tailWord_2645857 prefixEnd_2645857 150955153784795534002159 := by
  unfold tailWord_2645857
  simp only [CollatzResearch.WordTrace]
  refine ⟨96502332775519440244991825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64334888517012960163327883 96502332775519440244991825)
  ·
    refine ⟨72376749581639580183743869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96502332775519440244991825 72376749581639580183743869)
    ·
      refine ⟨27141281093114842568903951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72376749581639580183743869 27141281093114842568903951)
      ·
        refine ⟨40711921639672263853355927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27141281093114842568903951 40711921639672263853355927)
        ·
          refine ⟨61067882459508395780033891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40711921639672263853355927 61067882459508395780033891)
          ·
            refine ⟨91601823689262593670050837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61067882459508395780033891 91601823689262593670050837)
            ·
              refine ⟨4293835485434184078283633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91601823689262593670050837 4293835485434184078283633)
              ·
                refine ⟨3220376614075638058712725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4293835485434184078283633 3220376614075638058712725)
                ·
                  refine ⟨150955153784795534002159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3220376614075638058712725 150955153784795534002159)
                  ·
                    rfl

theorem cell23_2645857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 6].length) (baseStart_2645857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645857 prefixEnd_2645857 := by exact prefixLift 2645857
  have htrace : WordTrace (prefixWord ++ tailWord_2645857) baseStart_2645857 baseEnd_2645857 := by
    simpa [prefixWord, tailWord_2645857, baseEnd_2645857] using wordTrace_append hprefix tailTrace_2645857
  have hstable : (prefixWord ++ tailWord_2645857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645857).length < 2 ^ (prefixWord ++ tailWord_2645857).sum := by decide
  have hdescent : baseEnd_2645857 < baseStart_2645857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645880 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2645880 : Nat := 118140960795 + 2645880 * 2 ^ 59
def prefixEnd_2645880 : Nat := 4983230072969 + 3 ^ 40 * 2645880 * 2
def baseEnd_2645880 : Nat := 1358608194118213216031825

theorem tailTrace_2645880 : CollatzResearch.WordTrace tailWord_2645880 prefixEnd_2645880 1358608194118213216031825 := by
  unfold tailWord_2645880
  simp only [CollatzResearch.WordTrace]
  refine ⟨48251585827218057586539547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64335447769624076782052729 48251585827218057586539547)
  ·
    refine ⟨72377378740827086379809321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48251585827218057586539547 72377378740827086379809321)
    ·
      refine ⟨54283034055620314784856991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72377378740827086379809321 54283034055620314784856991)
      ·
        refine ⟨81424551083430472177285487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54283034055620314784856991 81424551083430472177285487)
        ·
          refine ⟨122136826625145708265928231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81424551083430472177285487 122136826625145708265928231)
          ·
            refine ⟨183205239937718562398892347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122136826625145708265928231 183205239937718562398892347)
            ·
              refine ⟨274807859906577843598338521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183205239937718562398892347 274807859906577843598338521)
              ·
                refine ⟨206105894929933382698753891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274807859906577843598338521 206105894929933382698753891)
                ·
                  refine ⟨309158842394900074048130837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206105894929933382698753891 309158842394900074048130837)
                  ·
                    refine ⟨14491820737260940971006133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 309158842394900074048130837 14491820737260940971006133)
                    ·
                      refine ⟨1358608194118213216031825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14491820737260940971006133 1358608194118213216031825)
                      ·
                        rfl

theorem cell23_2645880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2645880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645880 prefixEnd_2645880 := by exact prefixLift 2645880
  have htrace : WordTrace (prefixWord ++ tailWord_2645880) baseStart_2645880 baseEnd_2645880 := by
    simpa [prefixWord, tailWord_2645880, baseEnd_2645880] using wordTrace_append hprefix tailTrace_2645880
  have hstable : (prefixWord ++ tailWord_2645880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645880).length < 2 ^ (prefixWord ++ tailWord_2645880).sum := by decide
  have hdescent : baseEnd_2645880 < baseStart_2645880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645887 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 1, 5]
def baseStart_2645887 : Nat := 118140960795 + 2645887 * 2 ^ 59
def prefixEnd_2645887 : Nat := 4983230072969 + 3 ^ 40 * 2645887 * 2
def baseEnd_2645887 : Nat := 452870596160931562881431

theorem tailTrace_2645887 : CollatzResearch.WordTrace tailWord_2645887 prefixEnd_2645887 452870596160931562881431 := by
  unfold tailWord_2645887
  simp only [CollatzResearch.WordTrace]
  refine ⟨96503426965410755368583915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64335617976940503579055943 96503426965410755368583915)
  ·
    refine ⟨144755140448116133052875873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96503426965410755368583915 144755140448116133052875873)
    ·
      refine ⟨108566355336087099789656905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144755140448116133052875873 108566355336087099789656905)
      ·
        refine ⟨81424766502065324842242679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108566355336087099789656905 81424766502065324842242679)
        ·
          refine ⟨122137149753097987263364019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81424766502065324842242679 122137149753097987263364019)
          ·
            refine ⟨183205724629646980895046029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122137149753097987263364019 183205724629646980895046029)
            ·
              refine ⟨68702146736117617835642261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183205724629646980895046029 68702146736117617835642261)
              ·
                refine ⟨3220413128255513336045731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68702146736117617835642261 3220413128255513336045731)
                ·
                  refine ⟨4830619692383270004068597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220413128255513336045731 4830619692383270004068597)
                  ·
                    refine ⟨452870596160931562881431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4830619692383270004068597 452870596160931562881431)
                    ·
                      rfl

theorem cell23_2645887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_2645887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645887 prefixEnd_2645887 := by exact prefixLift 2645887
  have htrace : WordTrace (prefixWord ++ tailWord_2645887) baseStart_2645887 baseEnd_2645887 := by
    simpa [prefixWord, tailWord_2645887, baseEnd_2645887] using wordTrace_append hprefix tailTrace_2645887
  have hstable : (prefixWord ++ tailWord_2645887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645887).length < 2 ^ (prefixWord ++ tailWord_2645887).sum := by decide
  have hdescent : baseEnd_2645887 < baseStart_2645887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645941 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2645941 : Nat := 118140960795 + 2645941 * 2 ^ 59
def prefixEnd_2645941 : Nat := 4983230072969 + 3 ^ 40 * 2645941 * 2
def baseEnd_2645941 : Nat := 1358639516438137477369045

theorem tailTrace_2645941 : CollatzResearch.WordTrace tailWord_2645941 prefixEnd_2645941 1358639516438137477369045 := by
  unfold tailWord_2645941
  simp only [CollatzResearch.WordTrace]
  refine ⟨96505396507215122591049677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64336931004810081727366451 96505396507215122591049677)
  ·
    refine ⟨36189523690205670971643629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96505396507215122591049677 36189523690205670971643629)
    ·
      refine ⟨13571071383827126614366361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36189523690205670971643629 13571071383827126614366361)
      ·
        refine ⟨10178303537870344960774771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13571071383827126614366361 10178303537870344960774771)
        ·
          refine ⟨15267455306805517441162157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10178303537870344960774771 15267455306805517441162157)
          ·
            refine ⟨5725295740052069040435809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15267455306805517441162157 5725295740052069040435809)
            ·
              refine ⟨4293971805039051780326857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5725295740052069040435809 4293971805039051780326857)
              ·
                refine ⟨3220478853779288835245143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4293971805039051780326857 3220478853779288835245143)
                ·
                  refine ⟨4830718280668933252867715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220478853779288835245143 4830718280668933252867715)
                  ·
                    refine ⟨7246077421003399879301573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4830718280668933252867715 7246077421003399879301573)
                    ·
                      refine ⟨1358639516438137477369045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7246077421003399879301573 1358639516438137477369045)
                      ·
                        rfl

theorem cell23_2645941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2645941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645941 prefixEnd_2645941 := by exact prefixLift 2645941
  have htrace : WordTrace (prefixWord ++ tailWord_2645941) baseStart_2645941 baseEnd_2645941 := by
    simpa [prefixWord, tailWord_2645941, baseEnd_2645941] using wordTrace_append hprefix tailTrace_2645941
  have hstable : (prefixWord ++ tailWord_2645941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645941).length < 2 ^ (prefixWord ++ tailWord_2645941).sum := by decide
  have hdescent : baseEnd_2645941 < baseStart_2645941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2645975 : List Nat := [1, 1, 3, 2, 1, 1, 7, 2, 1, 2, 2]
def baseStart_2645975 : Nat := 118140960795 + 2645975 * 2 ^ 59
def prefixEnd_2645975 : Nat := 4983230072969 + 3 ^ 40 * 2645975 * 2
def baseEnd_2645975 : Nat := 1358656974780390344343889

theorem tailTrace_2645975 : CollatzResearch.WordTrace tailWord_2645975 prefixEnd_2645975 1358656974780390344343889 := by
  unfold tailWord_2645975
  simp only [CollatzResearch.WordTrace]
  refine ⟨96506636589091946397787379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64337757726061297598524919 96506636589091946397787379)
  ·
    refine ⟨144759954883637919596681069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96506636589091946397787379 144759954883637919596681069)
    ·
      refine ⟨54284983081364219848755401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144759954883637919596681069 54284983081364219848755401)
      ·
        refine ⟨40713737311023164886566551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54284983081364219848755401 40713737311023164886566551)
        ·
          refine ⟨61070605966534747329849827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40713737311023164886566551 61070605966534747329849827)
          ·
            refine ⟨91605908949802120994774741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61070605966534747329849827 91605908949802120994774741)
            ·
              refine ⟨2147013491010987210815033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 91605908949802120994774741 2147013491010987210815033)
              ·
                refine ⟨1610260118258240408111275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147013491010987210815033 1610260118258240408111275)
                ·
                  refine ⟨2415390177387360612166913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610260118258240408111275 2415390177387360612166913)
                  ·
                    refine ⟨1811542633040520459125185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2415390177387360612166913 1811542633040520459125185)
                    ·
                      refine ⟨1358656974780390344343889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1811542633040520459125185 1358656974780390344343889)
                      ·
                        rfl

theorem cell23_2645975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_2645975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2645975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2645975 prefixEnd_2645975 := by exact prefixLift 2645975
  have htrace : WordTrace (prefixWord ++ tailWord_2645975) baseStart_2645975 baseEnd_2645975 := by
    simpa [prefixWord, tailWord_2645975, baseEnd_2645975] using wordTrace_append hprefix tailTrace_2645975
  have hstable : (prefixWord ++ tailWord_2645975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2645975).length < 2 ^ (prefixWord ++ tailWord_2645975).sum := by decide
  have hdescent : baseEnd_2645975 < baseStart_2645975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2645975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646044 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2646044 : Nat := 118140960795 + 2646044 * 2 ^ 59
def prefixEnd_2646044 : Nat := 4983230072969 + 3 ^ 40 * 2646044 * 2
def baseEnd_2646044 : Nat := 1358692404945550574381071

theorem tailTrace_2646044 : CollatzResearch.WordTrace tailWord_2646044 prefixEnd_2646044 1358692404945550574381071 := by
  unfold tailWord_2646044
  simp only [CollatzResearch.WordTrace]
  refine ⟨48254576612920985591024593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64339435483894647454699457 48254576612920985591024593)
  ·
    refine ⟨36190932459690739193268445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48254576612920985591024593 36190932459690739193268445)
    ·
      refine ⟨13571599672384027197475667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36190932459690739193268445 13571599672384027197475667)
      ·
        refine ⟨20357399508576040796213501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13571599672384027197475667 20357399508576040796213501)
        ·
          refine ⟨7634024815716015298580063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20357399508576040796213501 7634024815716015298580063)
          ·
            refine ⟨11451037223574022947870095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634024815716015298580063 11451037223574022947870095)
            ·
              refine ⟨17176555835361034421805143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11451037223574022947870095 17176555835361034421805143)
              ·
                refine ⟨25764833753041551632707715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17176555835361034421805143 25764833753041551632707715)
                ·
                  refine ⟨38647250629562327449061573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25764833753041551632707715 38647250629562327449061573)
                  ·
                    refine ⟨7246359493042936396699045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38647250629562327449061573 7246359493042936396699045)
                    ·
                      refine ⟨1358692404945550574381071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7246359493042936396699045 1358692404945550574381071)
                      ·
                        rfl

theorem cell23_2646044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2646044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646044 prefixEnd_2646044 := by exact prefixLift 2646044
  have htrace : WordTrace (prefixWord ++ tailWord_2646044) baseStart_2646044 baseEnd_2646044 := by
    simpa [prefixWord, tailWord_2646044, baseEnd_2646044] using wordTrace_append hprefix tailTrace_2646044
  have hstable : (prefixWord ++ tailWord_2646044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646044).length < 2 ^ (prefixWord ++ tailWord_2646044).sum := by decide
  have hdescent : baseEnd_2646044 < baseStart_2646044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646081 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2646081 : Nat := 118140960795 + 2646081 * 2 ^ 59
def prefixEnd_2646081 : Nat := 4983230072969 + 3 ^ 40 * 2646081 * 2
def baseEnd_2646081 : Nat := 1358711403729766929618401

theorem tailTrace_2646081 : CollatzResearch.WordTrace tailWord_2646081 prefixEnd_2646081 1358711403729766929618401 := by
  unfold tailWord_2646081
  simp only [CollatzResearch.WordTrace]
  refine ⟨96510502726707926501146097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64340335151138617667430731 96510502726707926501146097)
  ·
    refine ⟨72382877045030944875859573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96510502726707926501146097 72382877045030944875859573)
    ·
      refine ⟨6785894722971651082111835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72382877045030944875859573 6785894722971651082111835)
      ·
        refine ⟨10178842084457476623167753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6785894722971651082111835 10178842084457476623167753)
        ·
          refine ⟨7634131563343107467375815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10178842084457476623167753 7634131563343107467375815)
          ·
            refine ⟨11451197345014661201063723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634131563343107467375815 11451197345014661201063723)
            ·
              refine ⟨17176796017521991801595585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11451197345014661201063723 17176796017521991801595585)
              ·
                refine ⟨12882597013141493851196689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17176796017521991801595585 12882597013141493851196689)
                ·
                  refine ⟨9661947759856120388397517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12882597013141493851196689 9661947759856120388397517)
                  ·
                    refine ⟨3623230409946045145649069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9661947759856120388397517 3623230409946045145649069)
                    ·
                      refine ⟨1358711403729766929618401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3623230409946045145649069 1358711403729766929618401)
                      ·
                        rfl

theorem cell23_2646081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2646081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646081 prefixEnd_2646081 := by exact prefixLift 2646081
  have htrace : WordTrace (prefixWord ++ tailWord_2646081) baseStart_2646081 baseEnd_2646081 := by
    simpa [prefixWord, tailWord_2646081, baseEnd_2646081] using wordTrace_append hprefix tailTrace_2646081
  have hstable : (prefixWord ++ tailWord_2646081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646081).length < 2 ^ (prefixWord ++ tailWord_2646081).sum := by decide
  have hdescent : baseEnd_2646081 < baseStart_2646081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646104 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2646104 : Nat := 118140960795 + 2646104 * 2 ^ 59
def prefixEnd_2646104 : Nat := 4983230072969 + 3 ^ 40 * 2646104 * 2
def baseEnd_2646104 : Nat := 1358723213784820339630795

theorem tailTrace_2646104 : CollatzResearch.WordTrace tailWord_2646104 prefixEnd_2646104 1358723213784820339630795 := by
  unfold tailWord_2646104
  simp only [CollatzResearch.WordTrace]
  refine ⟨48255670802812300714616683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64340894403749734286155577 48255670802812300714616683)
  ·
    refine ⟨72383506204218451071925025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48255670802812300714616683 72383506204218451071925025)
    ·
      refine ⟨54287629653163838303943769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72383506204218451071925025 54287629653163838303943769)
      ·
        refine ⟨40715722239872878727957827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54287629653163838303943769 40715722239872878727957827)
        ·
          refine ⟨61073583359809318091936741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40715722239872878727957827 61073583359809318091936741)
          ·
            refine ⟨11451296879964247142238139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61073583359809318091936741 11451296879964247142238139)
            ·
              refine ⟨17176945319946370713357209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11451296879964247142238139 17176945319946370713357209)
              ·
                refine ⟨12882708989959778035017907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17176945319946370713357209 12882708989959778035017907)
                ·
                  refine ⟨19324063484939667052526861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12882708989959778035017907 19324063484939667052526861)
                  ·
                    refine ⟨7246523806852375144697573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19324063484939667052526861 7246523806852375144697573)
                    ·
                      refine ⟨1358723213784820339630795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7246523806852375144697573 1358723213784820339630795)
                      ·
                        rfl

theorem cell23_2646104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2646104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646104 prefixEnd_2646104 := by exact prefixLift 2646104
  have htrace : WordTrace (prefixWord ++ tailWord_2646104) baseStart_2646104 baseEnd_2646104 := by
    simpa [prefixWord, tailWord_2646104, baseEnd_2646104] using wordTrace_append hprefix tailTrace_2646104
  have hstable : (prefixWord ++ tailWord_2646104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646104).length < 2 ^ (prefixWord ++ tailWord_2646104).sum := by decide
  have hdescent : baseEnd_2646104 < baseStart_2646104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646141 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_2646141 : Nat := 118140960795 + 2646141 * 2 ^ 59
def prefixEnd_2646141 : Nat := 4983230072969 + 3 ^ 40 * 2646141 * 2
def baseEnd_2646141 : Nat := 1358742212569036694868125

theorem tailTrace_2646141 : CollatzResearch.WordTrace tailWord_2646141 prefixEnd_2646141 1358742212569036694868125 := by
  unfold tailWord_2646141
  simp only [CollatzResearch.WordTrace]
  refine ⟨96512691106490556748330277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64341794070993704498886851 96512691106490556748330277)
  ·
    refine ⟨18096129582466979390311927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96512691106490556748330277 18096129582466979390311927)
    ·
      refine ⟨27144194373700469085467891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18096129582466979390311927 27144194373700469085467891)
      ·
        refine ⟨40716291560550703628201837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27144194373700469085467891 40716291560550703628201837)
        ·
          refine ⟨15268609335206513860575689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40716291560550703628201837 15268609335206513860575689)
          ·
            refine ⟨11451457001404885395431767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15268609335206513860575689 11451457001404885395431767)
            ·
              refine ⟨17177185502107328093147651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11451457001404885395431767 17177185502107328093147651)
              ·
                refine ⟨25765778253160992139721477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17177185502107328093147651 25765778253160992139721477)
                ·
                  refine ⟨4831083422467686026197777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25765778253160992139721477 4831083422467686026197777)
                  ·
                    refine ⟨3623312566850764519648333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4831083422467686026197777 3623312566850764519648333)
                    ·
                      refine ⟨1358742212569036694868125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3623312566850764519648333 1358742212569036694868125)
                      ·
                        rfl

theorem cell23_2646141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_2646141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646141 prefixEnd_2646141 := by exact prefixLift 2646141
  have htrace : WordTrace (prefixWord ++ tailWord_2646141) baseStart_2646141 baseEnd_2646141 := by
    simpa [prefixWord, tailWord_2646141, baseEnd_2646141] using wordTrace_append hprefix tailTrace_2646141
  have hstable : (prefixWord ++ tailWord_2646141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646141).length < 2 ^ (prefixWord ++ tailWord_2646141).sum := by decide
  have hdescent : baseEnd_2646141 < baseStart_2646141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646144 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 6]
def baseStart_2646144 : Nat := 118140960795 + 2646144 * 2 ^ 59
def prefixEnd_2646144 : Nat := 4983230072969 + 3 ^ 40 * 2646144 * 2
def baseEnd_2646144 : Nat := 150971528112333353681179

theorem tailTrace_2646144 : CollatzResearch.WordTrace tailWord_2646144 prefixEnd_2646144 150971528112333353681179 := by
  unfold tailWord_2646144
  simp only [CollatzResearch.WordTrace]
  refine ⟨48256400262739844130344743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64341867016986458840459657 48256400262739844130344743)
  ·
    refine ⟨72384600394109766195517115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48256400262739844130344743 72384600394109766195517115)
    ·
      refine ⟨108576900591164649293275673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72384600394109766195517115 108576900591164649293275673)
      ·
        refine ⟨81432675443373486969956755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108576900591164649293275673 81432675443373486969956755)
        ·
          refine ⟨122149013165060230454935133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81432675443373486969956755 122149013165060230454935133)
          ·
            refine ⟨45805879936897586420600675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122149013165060230454935133 45805879936897586420600675)
            ·
              refine ⟨68708819905346379630901013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45805879936897586420600675 68708819905346379630901013)
              ·
                refine ⟨3220725933063111545198485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68708819905346379630901013 3220725933063111545198485)
                ·
                  refine ⟨150971528112333353681179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3220725933063111545198485 150971528112333353681179)
                  ·
                    rfl

theorem cell23_2646144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 6].length) (baseStart_2646144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646144 prefixEnd_2646144 := by exact prefixLift 2646144
  have htrace : WordTrace (prefixWord ++ tailWord_2646144) baseStart_2646144 baseEnd_2646144 := by
    simpa [prefixWord, tailWord_2646144, baseEnd_2646144] using wordTrace_append hprefix tailTrace_2646144
  have hstable : (prefixWord ++ tailWord_2646144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646144).length < 2 ^ (prefixWord ++ tailWord_2646144).sum := by decide
  have hdescent : baseEnd_2646144 < baseStart_2646144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646234 : List Nat := [3, 1, 1, 2, 2, 1, 2, 11]
def baseStart_2646234 : Nat := 118140960795 + 2646234 * 2 ^ 59
def prefixEnd_2646234 : Nat := 4983230072969 + 3 ^ 40 * 2646234 * 2
def baseEnd_2646234 : Nat := 50325554306292771518711

theorem tailTrace_2646234 : CollatzResearch.WordTrace tailWord_2646234 prefixEnd_2646234 50325554306292771518711 := by
  unfold tailWord_2646234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24129020773788408407866439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64344055396769089087643837 24129020773788408407866439)
  ·
    refine ⟨36193531160682612611799659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24129020773788408407866439 36193531160682612611799659)
    ·
      refine ⟨54290296741023918917699489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36193531160682612611799659 54290296741023918917699489)
      ·
        refine ⟨40717722555767939188274617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54290296741023918917699489 40717722555767939188274617)
        ·
          refine ⟨30538291916825954391205963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40717722555767939188274617 30538291916825954391205963)
          ·
            refine ⟨45807437875238931586808945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30538291916825954391205963 45807437875238931586808945)
            ·
              refine ⟨34355578406429198690106709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45807437875238931586808945 34355578406429198690106709)
              ·
                refine ⟨50325554306292771518711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 34355578406429198690106709 50325554306292771518711)
                ·
                  rfl

theorem cell23_2646234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 11].length) (baseStart_2646234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646234 prefixEnd_2646234 := by exact prefixLift 2646234
  have htrace : WordTrace (prefixWord ++ tailWord_2646234) baseStart_2646234 baseEnd_2646234 := by
    simpa [prefixWord, tailWord_2646234, baseEnd_2646234] using wordTrace_append hprefix tailTrace_2646234
  have hstable : (prefixWord ++ tailWord_2646234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646234).length < 2 ^ (prefixWord ++ tailWord_2646234).sum := by decide
  have hdescent : baseEnd_2646234 < baseStart_2646234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646241 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2646241 : Nat := 118140960795 + 2646241 * 2 ^ 59
def prefixEnd_2646241 : Nat := 4983230072969 + 3 ^ 40 * 2646241 * 2
def baseEnd_2646241 : Nat := 1358793560634486303617665

theorem tailTrace_2646241 : CollatzResearch.WordTrace tailWord_2646241 prefixEnd_2646241 1358793560634486303617665 := by
  unfold tailWord_2646241
  simp only [CollatzResearch.WordTrace]
  refine ⟨96516338406128273826970577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64344225604085515884647051 96516338406128273826970577)
  ·
    refine ⟨72387253804596205370227933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96516338406128273826970577 72387253804596205370227933)
    ·
      refine ⟨27145220176723577013835475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72387253804596205370227933 27145220176723577013835475)
      ·
        refine ⟨40717830265085365520753213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27145220176723577013835475 40717830265085365520753213)
        ·
          refine ⟨15269186349407012070282455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40717830265085365520753213 15269186349407012070282455)
          ·
            refine ⟨22903779524110518105423683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15269186349407012070282455 22903779524110518105423683)
            ·
              refine ⟨34355669286165777158135525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22903779524110518105423683 34355669286165777158135525)
              ·
                refine ⟨6441687991156083217150411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34355669286165777158135525 6441687991156083217150411)
                ·
                  refine ⟨9662531986734124825725617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6441687991156083217150411 9662531986734124825725617)
                  ·
                    refine ⟨7246898990050593619294213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9662531986734124825725617 7246898990050593619294213)
                    ·
                      refine ⟨1358793560634486303617665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7246898990050593619294213 1358793560634486303617665)
                      ·
                        rfl

theorem cell23_2646241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2646241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646241 prefixEnd_2646241 := by exact prefixLift 2646241
  have htrace : WordTrace (prefixWord ++ tailWord_2646241) baseStart_2646241 baseEnd_2646241 := by
    simpa [prefixWord, tailWord_2646241, baseEnd_2646241] using wordTrace_append hprefix tailTrace_2646241
  have hstable : (prefixWord ++ tailWord_2646241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646241).length < 2 ^ (prefixWord ++ tailWord_2646241).sum := by decide
  have hdescent : baseEnd_2646241 < baseStart_2646241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646245 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 1, 1, 4]
def baseStart_2646245 : Nat := 118140960795 + 2646245 * 2 ^ 59
def prefixEnd_2646245 : Nat := 4983230072969 + 3 ^ 40 * 2646245 * 2
def baseEnd_2646245 : Nat := 1358795614557104287967647

theorem tailTrace_2646245 : CollatzResearch.WordTrace tailWord_2646245 prefixEnd_2646245 1358795614557104287967647 := by
  unfold tailWord_2646245
  simp only [CollatzResearch.WordTrace]
  refine ⟨96516484298113782510116189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64344322865409188340077459 96516484298113782510116189)
  ·
    refine ⟨36193681611792668441293571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96516484298113782510116189 36193681611792668441293571)
    ·
      refine ⟨54290522417689002661940357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36193681611792668441293571 54290522417689002661940357)
      ·
        refine ⟨10179472953316687999113817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54290522417689002661940357 10179472953316687999113817)
        ·
          refine ⟨7634604714987515999335363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10179472953316687999113817 7634604714987515999335363)
          ·
            refine ⟨11451907072481273999003045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634604714987515999335363 11451907072481273999003045)
            ·
              refine ⟨2147232576090238874813071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11451907072481273999003045 2147232576090238874813071)
              ·
                refine ⟨3220848864135358312219607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2147232576090238874813071 3220848864135358312219607)
                ·
                  refine ⟨4831273296203037468329411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220848864135358312219607 4831273296203037468329411)
                  ·
                    refine ⟨7246909944304556202494117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4831273296203037468329411 7246909944304556202494117)
                    ·
                      refine ⟨1358795614557104287967647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7246909944304556202494117 1358795614557104287967647)
                      ·
                        rfl

theorem cell23_2646245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_2646245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646245 prefixEnd_2646245 := by exact prefixLift 2646245
  have htrace : WordTrace (prefixWord ++ tailWord_2646245) baseStart_2646245 baseEnd_2646245 := by
    simpa [prefixWord, tailWord_2646245, baseEnd_2646245] using wordTrace_append hprefix tailTrace_2646245
  have hstable : (prefixWord ++ tailWord_2646245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646245).length < 2 ^ (prefixWord ++ tailWord_2646245).sum := by decide
  have hdescent : baseEnd_2646245 < baseStart_2646245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646255 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 2, 4]
def baseStart_2646255 : Nat := 118140960795 + 2646255 * 2 ^ 59
def prefixEnd_2646255 : Nat := 4983230072969 + 3 ^ 40 * 2646255 * 2
def baseEnd_2646255 : Nat := 452933583121216416280867

theorem tailTrace_2646255 : CollatzResearch.WordTrace tailWord_2646255 prefixEnd_2646255 452933583121216416280867 := by
  unfold tailWord_2646255
  simp only [CollatzResearch.WordTrace]
  refine ⟨96516849028077554217980219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64344566018718369478653479 96516849028077554217980219)
  ·
    refine ⟨144775273542116331326970329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96516849028077554217980219 144775273542116331326970329)
    ·
      refine ⟨108581455156587248495227747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144775273542116331326970329 108581455156587248495227747)
      ·
        refine ⟨162872182734880872742841621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108581455156587248495227747 162872182734880872742841621)
        ·
          refine ⟨7634633565697540909820701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 162872182734880872742841621 7634633565697540909820701)
          ·
            refine ⟨2862987587136577841182763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7634633565697540909820701 2862987587136577841182763)
            ·
              refine ⟨4294481380704866761774145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862987587136577841182763 4294481380704866761774145)
              ·
                refine ⟨3220861035528650071330609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4294481380704866761774145 3220861035528650071330609)
                ·
                  refine ⟨2415645776646487553497957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3220861035528650071330609 2415645776646487553497957)
                  ·
                    refine ⟨452933583121216416280867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415645776646487553497957 452933583121216416280867)
                    ·
                      rfl

theorem cell23_2646255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 4].length) (baseStart_2646255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646255 prefixEnd_2646255 := by exact prefixLift 2646255
  have htrace : WordTrace (prefixWord ++ tailWord_2646255) baseStart_2646255 baseEnd_2646255 := by
    simpa [prefixWord, tailWord_2646255, baseEnd_2646255] using wordTrace_append hprefix tailTrace_2646255
  have hstable : (prefixWord ++ tailWord_2646255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646255).length < 2 ^ (prefixWord ++ tailWord_2646255).sum := by decide
  have hdescent : baseEnd_2646255 < baseStart_2646255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646264 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 1, 9]
def baseStart_2646264 : Nat := 118140960795 + 2646264 * 2 ^ 59
def prefixEnd_2646264 : Nat := 4983230072969 + 3 ^ 40 * 2646264 * 2
def baseEnd_2646264 : Nat := 452935123563179904543353

theorem tailTrace_2646264 : CollatzResearch.WordTrace tailWord_2646264 prefixEnd_2646264 452935123563179904543353 := by
  unfold tailWord_2646264
  simp only [CollatzResearch.WordTrace]
  refine ⟨48258588642522474377528923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64344784856696632503371897 48258588642522474377528923)
  ·
    refine ⟨72387882963783711566293385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48258588642522474377528923 72387882963783711566293385)
    ·
      refine ⟨54290912222837783674720039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72387882963783711566293385 54290912222837783674720039)
      ·
        refine ⟨81436368334256675512080059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54290912222837783674720039 81436368334256675512080059)
        ·
          refine ⟨122154552501385013268120089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81436368334256675512080059 122154552501385013268120089)
          ·
            refine ⟨91615914376038759951090067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122154552501385013268120089 91615914376038759951090067)
            ·
              refine ⟨137423871564058139926635101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91615914376038759951090067 137423871564058139926635101)
              ·
                refine ⟨51533951836521802472488163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137423871564058139926635101 51533951836521802472488163)
                ·
                  refine ⟨77300927754782703708732245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51533951836521802472488163 77300927754782703708732245)
                  ·
                    refine ⟨452935123563179904543353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 77300927754782703708732245 452935123563179904543353)
                    ·
                      rfl

theorem cell23_2646264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_2646264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646264 prefixEnd_2646264 := by exact prefixLift 2646264
  have htrace : WordTrace (prefixWord ++ tailWord_2646264) baseStart_2646264 baseEnd_2646264 := by
    simpa [prefixWord, tailWord_2646264, baseEnd_2646264] using wordTrace_append hprefix tailTrace_2646264
  have hstable : (prefixWord ++ tailWord_2646264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646264).length < 2 ^ (prefixWord ++ tailWord_2646264).sum := by decide
  have hdescent : baseEnd_2646264 < baseStart_2646264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646305 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_2646305 : Nat := 118140960795 + 2646305 * 2 ^ 59
def prefixEnd_2646305 : Nat := 4983230072969 + 3 ^ 40 * 2646305 * 2
def baseEnd_2646305 : Nat := 1358826423396374053217371

theorem tailTrace_2646305 : CollatzResearch.WordTrace tailWord_2646305 prefixEnd_2646305 1358826423396374053217371 := by
  unfold tailWord_2646305
  simp only [CollatzResearch.WordTrace]
  refine ⟨96518672677896412757300369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64345781785264275171533579 96518672677896412757300369)
  ·
    refine ⟨72389004508422309567975277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96518672677896412757300369 72389004508422309567975277)
    ·
      refine ⟨27145876690658366087990729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72389004508422309567975277 27145876690658366087990729)
      ·
        refine ⟨20359407517993774565993047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27145876690658366087990729 20359407517993774565993047)
        ·
          refine ⟨30539111276990661848989571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20359407517993774565993047 30539111276990661848989571)
          ·
            refine ⟨45808666915485992773484357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30539111276990661848989571 45808666915485992773484357)
            ·
              refine ⟨8589125046653623645028317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45808666915485992773484357 8589125046653623645028317)
              ·
                refine ⟨3220921892495108866885619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8589125046653623645028317 3220921892495108866885619)
                ·
                  refine ⟨4831382838742663300328429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3220921892495108866885619 4831382838742663300328429)
                  ·
                    refine ⟨1811768564528498737623161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4831382838742663300328429 1811768564528498737623161)
                    ·
                      refine ⟨1358826423396374053217371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1811768564528498737623161 1358826423396374053217371)
                      ·
                        rfl

theorem cell23_2646305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_2646305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646305 prefixEnd_2646305 := by exact prefixLift 2646305
  have htrace : WordTrace (prefixWord ++ tailWord_2646305) baseStart_2646305 baseEnd_2646305 := by
    simpa [prefixWord, tailWord_2646305, baseEnd_2646305] using wordTrace_append hprefix tailTrace_2646305
  have hstable : (prefixWord ++ tailWord_2646305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646305).length < 2 ^ (prefixWord ++ tailWord_2646305).sum := by decide
  have hdescent : baseEnd_2646305 < baseStart_2646305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646329 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2646329 : Nat := 118140960795 + 2646329 * 2 ^ 59
def prefixEnd_2646329 : Nat := 4983230072969 + 3 ^ 40 * 2646329 * 2
def baseEnd_2646329 : Nat := 1358838746932081959317261

theorem tailTrace_2646329 : CollatzResearch.WordTrace tailWord_2646329 prefixEnd_2646329 1358838746932081959317261 := by
  unfold tailWord_2646329
  simp only [CollatzResearch.WordTrace]
  refine ⟨96519548029809464856174041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64346365353206309904116027 96519548029809464856174041)
  ·
    refine ⟨72389661022357098642130531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96519548029809464856174041 72389661022357098642130531)
    ·
      refine ⟨108584491533535647963195797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72389661022357098642130531 108584491533535647963195797)
      ·
        refine ⟨5089898040634483498274803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108584491533535647963195797 5089898040634483498274803)
        ·
          refine ⟨7634847060951725247412205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5089898040634483498274803 7634847060951725247412205)
          ·
            refine ⟨2863067647856896967779577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7634847060951725247412205 2863067647856896967779577)
            ·
              refine ⟨2147300735892672725834683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863067647856896967779577 2147300735892672725834683)
              ·
                refine ⟨3220951103839009088752025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2147300735892672725834683 3220951103839009088752025)
                ·
                  refine ⟨2415713327879256816564019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3220951103839009088752025 2415713327879256816564019)
                  ·
                    refine ⟨3623569991818885224846029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2415713327879256816564019 3623569991818885224846029)
                    ·
                      refine ⟨1358838746932081959317261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3623569991818885224846029 1358838746932081959317261)
                      ·
                        rfl

theorem cell23_2646329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2646329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646329 prefixEnd_2646329 := by exact prefixLift 2646329
  have htrace : WordTrace (prefixWord ++ tailWord_2646329) baseStart_2646329 baseEnd_2646329 := by
    simpa [prefixWord, tailWord_2646329, baseEnd_2646329] using wordTrace_append hprefix tailTrace_2646329
  have hstable : (prefixWord ++ tailWord_2646329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646329).length < 2 ^ (prefixWord ++ tailWord_2646329).sum := by decide
  have hdescent : baseEnd_2646329 < baseStart_2646329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646351 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 3]
def baseStart_2646351 : Nat := 118140960795 + 2646351 * 2 ^ 59
def prefixEnd_2646351 : Nat := 4983230072969 + 3 ^ 40 * 2646351 * 2
def baseEnd_2646351 : Nat := 1358850043506480873242159

theorem tailTrace_2646351 : CollatzResearch.WordTrace tailWord_2646351 prefixEnd_2646351 1358850043506480873242159 := by
  unfold tailWord_2646351
  simp only [CollatzResearch.WordTrace]
  refine ⟨96520350435729762613474907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64346900290486508408983271 96520350435729762613474907)
  ·
    refine ⟨144780525653594643920212361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96520350435729762613474907 144780525653594643920212361)
    ·
      refine ⟨108585394240195982940159271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144780525653594643920212361 108585394240195982940159271)
      ·
        refine ⟨162878091360293974410238907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108585394240195982940159271 162878091360293974410238907)
        ·
          refine ⟨244317137040440961615358361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162878091360293974410238907 244317137040440961615358361)
          ·
            refine ⟨183237852780330721211518771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244317137040440961615358361 183237852780330721211518771)
            ·
              refine ⟨274856779170496081817278157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183237852780330721211518771 274856779170496081817278157)
              ·
                refine ⟨103071292188936030681479309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274856779170496081817278157 103071292188936030681479309)
                ·
                  refine ⟨38651734570851011505554741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103071292188936030681479309 38651734570851011505554741)
                  ·
                    refine ⟨3623600116017282328645757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38651734570851011505554741 3623600116017282328645757)
                    ·
                      refine ⟨1358850043506480873242159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3623600116017282328645757 1358850043506480873242159)
                      ·
                        rfl

theorem cell23_2646351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_2646351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646351 prefixEnd_2646351 := by exact prefixLift 2646351
  have htrace : WordTrace (prefixWord ++ tailWord_2646351) baseStart_2646351 baseEnd_2646351 := by
    simpa [prefixWord, tailWord_2646351, baseEnd_2646351] using wordTrace_append hprefix tailTrace_2646351
  have hstable : (prefixWord ++ tailWord_2646351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646351).length < 2 ^ (prefixWord ++ tailWord_2646351).sum := by decide
  have hdescent : baseEnd_2646351 < baseStart_2646351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646375 : List Nat := [1, 1, 5, 1, 3, 2, 1, 4, 5]
def baseStart_2646375 : Nat := 118140960795 + 2646375 * 2 ^ 59
def prefixEnd_2646375 : Nat := 4983230072969 + 3 ^ 40 * 2646375 * 2
def baseEnd_2646375 : Nat := 150984707449132086593561

theorem tailTrace_2646375 : CollatzResearch.WordTrace tailWord_2646375 prefixEnd_2646375 150984707449132086593561 := by
  unfold tailWord_2646375
  simp only [CollatzResearch.WordTrace]
  refine ⟨96521225787642814712348579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64347483858428543141565719 96521225787642814712348579)
  ·
    refine ⟨144781838681464222068522869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96521225787642814712348579 144781838681464222068522869)
    ·
      refine ⟨13573297376387270818924019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144781838681464222068522869 13573297376387270818924019)
      ·
        refine ⟨20359946064580906228386029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13573297376387270818924019 20359946064580906228386029)
        ·
          refine ⟨7634979774217839835644761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20359946064580906228386029 7634979774217839835644761)
          ·
            refine ⟨5726234830663379876733571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7634979774217839835644761 5726234830663379876733571)
            ·
              refine ⟨8589352245995069815100357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5726234830663379876733571 8589352245995069815100357)
              ·
                refine ⟨1610503546124075590331317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8589352245995069815100357 1610503546124075590331317)
                ·
                  refine ⟨150984707449132086593561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1610503546124075590331317 150984707449132086593561)
                  ·
                    rfl

theorem cell23_2646375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 5].length) (baseStart_2646375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646375 prefixEnd_2646375 := by exact prefixLift 2646375
  have htrace : WordTrace (prefixWord ++ tailWord_2646375) baseStart_2646375 baseEnd_2646375 := by
    simpa [prefixWord, tailWord_2646375, baseEnd_2646375] using wordTrace_append hprefix tailTrace_2646375
  have hstable : (prefixWord ++ tailWord_2646375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646375).length < 2 ^ (prefixWord ++ tailWord_2646375).sum := by decide
  have hdescent : baseEnd_2646375 < baseStart_2646375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646408 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2646408 : Nat := 118140960795 + 2646408 * 2 ^ 59
def prefixEnd_2646408 : Nat := 4983230072969 + 3 ^ 40 * 2646408 * 2
def baseEnd_2646408 : Nat := 1358879311903787150229397

theorem tailTrace_2646408 : CollatzResearch.WordTrace tailWord_2646408 prefixEnd_2646408 1358879311903787150229397 := by
  unfold tailWord_2646408
  simp only [CollatzResearch.WordTrace]
  refine ⟨48261214698261630674149939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64348286264348840898866585 48261214698261630674149939)
  ·
    refine ⟨72391822047392446011224909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48261214698261630674149939 72391822047392446011224909)
    ·
      refine ⟨27146933267772167254209341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72391822047392446011224909 27146933267772167254209341)
      ·
        refine ⟨10180099975414562720328503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27146933267772167254209341 10180099975414562720328503)
        ·
          refine ⟨15270149963121844080492755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10180099975414562720328503 15270149963121844080492755)
          ·
            refine ⟨22905224944682766120739133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15270149963121844080492755 22905224944682766120739133)
            ·
              refine ⟨8589459354256037295277175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22905224944682766120739133 8589459354256037295277175)
              ·
                refine ⟨12884189031384055942915763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8589459354256037295277175 12884189031384055942915763)
                ·
                  refine ⟨19326283547076083914373645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12884189031384055942915763 19326283547076083914373645)
                  ·
                    refine ⟨7247356330153531467890117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19326283547076083914373645 7247356330153531467890117)
                    ·
                      refine ⟨1358879311903787150229397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7247356330153531467890117 1358879311903787150229397)
                      ·
                        rfl

theorem cell23_2646408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2646408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646408 prefixEnd_2646408 := by exact prefixLift 2646408
  have htrace : WordTrace (prefixWord ++ tailWord_2646408) baseStart_2646408 baseEnd_2646408 := by
    simpa [prefixWord, tailWord_2646408, baseEnd_2646408] using wordTrace_append hprefix tailTrace_2646408
  have hstable : (prefixWord ++ tailWord_2646408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646408).length < 2 ^ (prefixWord ++ tailWord_2646408).sum := by decide
  have hdescent : baseEnd_2646408 < baseStart_2646408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646435 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 3, 4]
def baseStart_2646435 : Nat := 118140960795 + 2646435 * 2 ^ 59
def prefixEnd_2646435 : Nat := 4983230072969 + 3 ^ 40 * 2646435 * 2
def baseEnd_2646435 : Nat := 452964391960486181530591

theorem tailTrace_2646435 : CollatzResearch.WordTrace tailWord_2646435 prefixEnd_2646435 452964391960486181530591 := by
  unfold tailWord_2646435
  simp only [CollatzResearch.WordTrace]
  refine ⟨96523414167425444959532759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64348942778283629973021839 96523414167425444959532759)
  ·
    refine ⟨144785121251138167439299139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96523414167425444959532759 144785121251138167439299139)
    ·
      refine ⟨217177681876707251158948709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144785121251138167439299139 217177681876707251158948709)
      ·
        refine ⟨40720815351882609592302883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217177681876707251158948709 40720815351882609592302883)
        ·
          refine ⟨61081223027823914388454325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40720815351882609592302883 61081223027823914388454325)
          ·
            refine ⟨5726364658858491973917593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61081223027823914388454325 5726364658858491973917593)
            ·
              refine ⟨4294773494143868980438195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5726364658858491973917593 4294773494143868980438195)
              ·
                refine ⟨6442160241215803470657293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294773494143868980438195 6442160241215803470657293)
                ·
                  refine ⟨2415810090455926301496485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6442160241215803470657293 2415810090455926301496485)
                  ·
                    refine ⟨452964391960486181530591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415810090455926301496485 452964391960486181530591)
                    ·
                      rfl

theorem cell23_2646435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 4].length) (baseStart_2646435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646435 prefixEnd_2646435 := by exact prefixLift 2646435
  have htrace : WordTrace (prefixWord ++ tailWord_2646435) baseStart_2646435 baseEnd_2646435 := by
    simpa [prefixWord, tailWord_2646435, baseEnd_2646435] using wordTrace_append hprefix tailTrace_2646435
  have hstable : (prefixWord ++ tailWord_2646435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646435).length < 2 ^ (prefixWord ++ tailWord_2646435).sum := by decide
  have hdescent : baseEnd_2646435 < baseStart_2646435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646478 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_2646478 : Nat := 118140960795 + 2646478 * 2 ^ 59
def prefixEnd_2646478 : Nat := 4983230072969 + 3 ^ 40 * 2646478 * 2
def baseEnd_2646478 : Nat := 452971751849867292118025

theorem tailTrace_2646478 : CollatzResearch.WordTrace tailWord_2646478 prefixEnd_2646478 452971751849867292118025 := by
  unfold tailWord_2646478
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065622813283707912918511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64349988337513108868898725 12065622813283707912918511)
  ·
    refine ⟨18098434219925561869377767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12065622813283707912918511 18098434219925561869377767)
    ·
      refine ⟨27147651329888342804066651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18098434219925561869377767 27147651329888342804066651)
      ·
        refine ⟨40721476994832514206099977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27147651329888342804066651 40721476994832514206099977)
        ·
          refine ⟨30541107746124385654574983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40721476994832514206099977 30541107746124385654574983)
          ·
            refine ⟨45811661619186578481862475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30541107746124385654574983 45811661619186578481862475)
            ·
              refine ⟨68717492428779867722793713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45811661619186578481862475 68717492428779867722793713)
              ·
                refine ⟨51538119321584900792095285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68717492428779867722793713 51538119321584900792095285)
                ·
                  refine ⟨4831698686398584449258933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51538119321584900792095285 4831698686398584449258933)
                  ·
                    refine ⟨452971751849867292118025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4831698686398584449258933 452971751849867292118025)
                    ·
                      rfl

theorem cell23_2646478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_2646478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646478 prefixEnd_2646478 := by exact prefixLift 2646478
  have htrace : WordTrace (prefixWord ++ tailWord_2646478) baseStart_2646478 baseEnd_2646478 := by
    simpa [prefixWord, tailWord_2646478, baseEnd_2646478] using wordTrace_append hprefix tailTrace_2646478
  have hstable : (prefixWord ++ tailWord_2646478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646478).length < 2 ^ (prefixWord ++ tailWord_2646478).sum := by decide
  have hdescent : baseEnd_2646478 < baseStart_2646478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646486 : List Nat := [5, 2, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2646486 : Nat := 118140960795 + 2646486 * 2 ^ 59
def prefixEnd_2646486 : Nat := 4983230072969 + 3 ^ 40 * 2646486 * 2
def baseEnd_2646486 : Nat := 452973121131612615018013

theorem tailTrace_2646486 : CollatzResearch.WordTrace tailWord_2646486 prefixEnd_2646486 452973121131612615018013 := by
  unfold tailWord_2646486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6032829643140042541852457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64350182860160453779759541 6032829643140042541852457)
  ·
    refine ⟨4524622232355031906389343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6032829643140042541852457 4524622232355031906389343)
    ·
      refine ⟨6786933348532547859584015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4524622232355031906389343 6786933348532547859584015)
      ·
        refine ⟨10180400022798821789376023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6786933348532547859584015 10180400022798821789376023)
        ·
          refine ⟨15270600034198232684064035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10180400022798821789376023 15270600034198232684064035)
          ·
            refine ⟨22905900051297349026096053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15270600034198232684064035 22905900051297349026096053)
            ·
              refine ⟨2147428129809126471196505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22905900051297349026096053 2147428129809126471196505)
              ·
                refine ⟨1610571097356844853397379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147428129809126471196505 1610571097356844853397379)
                ·
                  refine ⟨2415856646035267280096069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610571097356844853397379 2415856646035267280096069)
                  ·
                    refine ⟨452973121131612615018013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415856646035267280096069 452973121131612615018013)
                    ·
                      rfl

theorem cell23_2646486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2646486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646486 prefixEnd_2646486 := by exact prefixLift 2646486
  have htrace : WordTrace (prefixWord ++ tailWord_2646486) baseStart_2646486 baseEnd_2646486 := by
    simpa [prefixWord, tailWord_2646486, baseEnd_2646486] using wordTrace_append hprefix tailTrace_2646486
  have hstable : (prefixWord ++ tailWord_2646486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646486).length < 2 ^ (prefixWord ++ tailWord_2646486).sum := by decide
  have hdescent : baseEnd_2646486 < baseStart_2646486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646499 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 6]
def baseStart_2646499 : Nat := 118140960795 + 2646499 * 2 ^ 59
def prefixEnd_2646499 : Nat := 4983230072969 + 3 ^ 40 * 2646499 * 2
def baseEnd_2646499 : Nat := 150991782071482921576831

theorem tailTrace_2646499 : CollatzResearch.WordTrace tailWord_2646499 prefixEnd_2646499 150991782071482921576831 := by
  unfold tailWord_2646499
  simp only [CollatzResearch.WordTrace]
  refine ⟨96525748439193583889862551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64350498959462389259908367 96525748439193583889862551)
  ·
    refine ⟨144788622658790375834793827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96525748439193583889862551 144788622658790375834793827)
    ·
      refine ⟨217182933988185563752190741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144788622658790375834793827 217182933988185563752190741)
      ·
        refine ⟨10180450030696198300883941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 217182933988185563752190741 10180450030696198300883941)
        ·
          refine ⟨1908834380755537181415739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10180450030696198300883941 1908834380755537181415739)
          ·
            refine ⟨2863251571133305772123609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908834380755537181415739 2863251571133305772123609)
            ·
              refine ⟨2147438678349979329092707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863251571133305772123609 2147438678349979329092707)
              ·
                refine ⟨3221158017524968993639061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2147438678349979329092707 3221158017524968993639061)
                ·
                  refine ⟨150991782071482921576831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3221158017524968993639061 150991782071482921576831)
                  ·
                    rfl

theorem cell23_2646499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 6].length) (baseStart_2646499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646499 prefixEnd_2646499 := by exact prefixLift 2646499
  have htrace : WordTrace (prefixWord ++ tailWord_2646499) baseStart_2646499 baseEnd_2646499 := by
    simpa [prefixWord, tailWord_2646499, baseEnd_2646499] using wordTrace_append hprefix tailTrace_2646499
  have hstable : (prefixWord ++ tailWord_2646499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646499).length < 2 ^ (prefixWord ++ tailWord_2646499).sum := by decide
  have hdescent : baseEnd_2646499 < baseStart_2646499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646508 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_2646508 : Nat := 118140960795 + 2646508 * 2 ^ 59
def prefixEnd_2646508 : Nat := 4983230072969 + 3 ^ 40 * 2646508 * 2
def baseEnd_2646508 : Nat := 452976886656412252992979

theorem tailTrace_2646508 : CollatzResearch.WordTrace tailWord_2646508 prefixEnd_2646508 452976886656412252992979 := by
  unfold tailWord_2646508
  simp only [CollatzResearch.WordTrace]
  refine ⟨48263038348080489213470089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64350717797440652284626785 48263038348080489213470089)
  ·
    refine ⟨36197278761060366910102567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48263038348080489213470089 36197278761060366910102567)
    ·
      refine ⟨54295918141590550365153851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36197278761060366910102567 54295918141590550365153851)
      ·
        refine ⟨81443877212385825547730777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54295918141590550365153851 81443877212385825547730777)
        ·
          refine ⟨61082907909289369160798083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81443877212385825547730777 61082907909289369160798083)
          ·
            refine ⟨91624361863934053741197125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61082907909289369160798083 91624361863934053741197125)
            ·
              refine ⟨17179567849487635076474461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91624361863934053741197125 17179567849487635076474461)
              ·
                refine ⟨6442337943557863153677923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17179567849487635076474461 6442337943557863153677923)
                ·
                  refine ⟨9663506915336794730516885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6442337943557863153677923 9663506915336794730516885)
                  ·
                    refine ⟨452976886656412252992979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9663506915336794730516885 452976886656412252992979)
                    ·
                      rfl

theorem cell23_2646508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_2646508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646508 prefixEnd_2646508 := by exact prefixLift 2646508
  have htrace : WordTrace (prefixWord ++ tailWord_2646508) baseStart_2646508 baseEnd_2646508 := by
    simpa [prefixWord, tailWord_2646508, baseEnd_2646508] using wordTrace_append hprefix tailTrace_2646508
  have hstable : (prefixWord ++ tailWord_2646508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646508).length < 2 ^ (prefixWord ++ tailWord_2646508).sum := by decide
  have hdescent : baseEnd_2646508 < baseStart_2646508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646542 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_2646542 : Nat := 118140960795 + 2646542 * 2 ^ 59
def prefixEnd_2646542 : Nat := 4983230072969 + 3 ^ 40 * 2646542 * 2
def baseEnd_2646542 : Nat := 452982706103829875317927

theorem tailTrace_2646542 : CollatzResearch.WordTrace tailWord_2646542 prefixEnd_2646542 452982706103829875317927 := by
  unfold tailWord_2646542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065914597254725279209735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64351544518691868155785253 12065914597254725279209735)
  ·
    refine ⟨18098871895882087918814603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12065914597254725279209735 18098871895882087918814603)
    ·
      refine ⟨27148307843823131878221905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18098871895882087918814603 27148307843823131878221905)
      ·
        refine ⟨20361230882867348908666429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27148307843823131878221905 20361230882867348908666429)
        ·
          refine ⟨7635461581075255840749911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20361230882867348908666429 7635461581075255840749911)
          ·
            refine ⟨11453192371612883761124867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7635461581075255840749911 11453192371612883761124867)
            ·
              refine ⟨17179788557419325641687301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11453192371612883761124867 17179788557419325641687301)
              ·
                refine ⟨3221210354516123557816369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17179788557419325641687301 3221210354516123557816369)
                ·
                  refine ⟨2415907765887092668362277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3221210354516123557816369 2415907765887092668362277)
                  ·
                    refine ⟨452982706103829875317927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415907765887092668362277 452982706103829875317927)
                    ·
                      rfl

theorem cell23_2646542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_2646542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646542 prefixEnd_2646542 := by exact prefixLift 2646542
  have htrace : WordTrace (prefixWord ++ tailWord_2646542) baseStart_2646542 baseEnd_2646542 := by
    simpa [prefixWord, tailWord_2646542, baseEnd_2646542] using wordTrace_append hprefix tailTrace_2646542
  have hstable : (prefixWord ++ tailWord_2646542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646542).length < 2 ^ (prefixWord ++ tailWord_2646542).sum := by decide
  have hdescent : baseEnd_2646542 < baseStart_2646542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646565 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_2646565 : Nat := 118140960795 + 2646565 * 2 ^ 59
def prefixEnd_2646565 : Nat := 4983230072969 + 3 ^ 40 * 2646565 * 2
def baseEnd_2646565 : Nat := 1358959928366543035966175

theorem tailTrace_2646565 : CollatzResearch.WordTrace tailWord_2646565 prefixEnd_2646565 1358959928366543035966175 := by
  unfold tailWord_2646565
  simp only [CollatzResearch.WordTrace]
  refine ⟨96528155656954477161765149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64352103771302984774510099 96528155656954477161765149)
  ·
    refine ⟨36198058371357928935661931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96528155656954477161765149 36198058371357928935661931)
    ·
      refine ⟨54297087557036893403492897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36198058371357928935661931 54297087557036893403492897)
      ·
        refine ⟨40722815667777670052619673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54297087557036893403492897 40722815667777670052619673)
        ·
          refine ⟨30542111750833252539464755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40722815667777670052619673 30542111750833252539464755)
          ·
            refine ⟨45813167626249878809197133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30542111750833252539464755 45813167626249878809197133)
            ·
              refine ⟨17179937859843704553448925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45813167626249878809197133 17179937859843704553448925)
              ·
                refine ⟨6442476697441389207543347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17179937859843704553448925 6442476697441389207543347)
                ·
                  refine ⟨9663715046162083811315021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6442476697441389207543347 9663715046162083811315021)
                  ·
                    refine ⟨3623893142310781429243133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9663715046162083811315021 3623893142310781429243133)
                    ·
                      refine ⟨1358959928366543035966175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3623893142310781429243133 1358959928366543035966175)
                      ·
                        rfl

theorem cell23_2646565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_2646565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646565 prefixEnd_2646565 := by exact prefixLift 2646565
  have htrace : WordTrace (prefixWord ++ tailWord_2646565) baseStart_2646565 baseEnd_2646565 := by
    simpa [prefixWord, tailWord_2646565, baseEnd_2646565] using wordTrace_append hprefix tailTrace_2646565
  have hstable : (prefixWord ++ tailWord_2646565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646565).length < 2 ^ (prefixWord ++ tailWord_2646565).sum := by decide
  have hdescent : baseEnd_2646565 < baseStart_2646565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646599 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_2646599 : Nat := 118140960795 + 2646599 * 2 ^ 59
def prefixEnd_2646599 : Nat := 4983230072969 + 3 ^ 40 * 2646599 * 2
def baseEnd_2646599 : Nat := 1358977386708795902941019

theorem tailTrace_2646599 : CollatzResearch.WordTrace tailWord_2646599 prefixEnd_2646599 1358977386708795902941019 := by
  unfold tailWord_2646599
  simp only [CollatzResearch.WordTrace]
  refine ⟨96529395738831300968502851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64352930492554200645668567 96529395738831300968502851)
  ·
    refine ⟨144794093608246951452754277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96529395738831300968502851 144794093608246951452754277)
    ·
      refine ⟨27148892551546303397391427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144794093608246951452754277 27148892551546303397391427)
      ·
        refine ⟨40723338827319455096087141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27148892551546303397391427 40723338827319455096087141)
        ·
          refine ⟨7635626030122397830516339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40723338827319455096087141 7635626030122397830516339)
          ·
            refine ⟨11453439045183596745774509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7635626030122397830516339 11453439045183596745774509)
            ·
              refine ⟨4295039641943848779665441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11453439045183596745774509 4295039641943848779665441)
              ·
                refine ⟨3221279731457886584749081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4295039641943848779665441 3221279731457886584749081)
                ·
                  refine ⟨2415959798593414938561811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3221279731457886584749081 2415959798593414938561811)
                  ·
                    refine ⟨3623939697890122407842717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2415959798593414938561811 3623939697890122407842717)
                    ·
                      refine ⟨1358977386708795902941019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3623939697890122407842717 1358977386708795902941019)
                      ·
                        rfl

theorem cell23_2646599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_2646599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646599 prefixEnd_2646599 := by exact prefixLift 2646599
  have htrace : WordTrace (prefixWord ++ tailWord_2646599) baseStart_2646599 baseEnd_2646599 := by
    simpa [prefixWord, tailWord_2646599, baseEnd_2646599] using wordTrace_append hprefix tailTrace_2646599
  have hstable : (prefixWord ++ tailWord_2646599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646599).length < 2 ^ (prefixWord ++ tailWord_2646599).sum := by decide
  have hdescent : baseEnd_2646599 < baseStart_2646599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646608 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_2646608 : Nat := 118140960795 + 2646608 * 2 ^ 59
def prefixEnd_2646608 : Nat := 4983230072969 + 3 ^ 40 * 2646608 * 2
def baseEnd_2646608 : Nat := 1358982008034686367728477

theorem tailTrace_2646608 : CollatzResearch.WordTrace tailWord_2646608 prefixEnd_2646608 1358982008034686367728477 := by
  unfold tailWord_2646608
  simp only [CollatzResearch.WordTrace]
  refine ⟨48264861997899347752790239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64353149330532463670386985 48264861997899347752790239)
  ·
    refine ⟨72397292996849021629185359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48264861997899347752790239 72397292996849021629185359)
    ·
      refine ⟨108595939495273532443778039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72397292996849021629185359 108595939495273532443778039)
      ·
        refine ⟨162893909242910298665667059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108595939495273532443778039 162893909242910298665667059)
        ·
          refine ⟨244340863864365447998500589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162893909242910298665667059 244340863864365447998500589)
          ·
            refine ⟨91627823949137042999437721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244340863864365447998500589 91627823949137042999437721)
            ·
              refine ⟨68720867961852782249578291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91627823949137042999437721 68720867961852782249578291)
              ·
                refine ⟨103081301942779173374367437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68720867961852782249578291 103081301942779173374367437)
                ·
                  refine ⟨38655488228542190015387789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103081301942779173374367437 38655488228542190015387789)
                  ·
                    refine ⟨14495808085703321255770421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38655488228542190015387789 14495808085703321255770421)
                    ·
                      refine ⟨1358982008034686367728477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14495808085703321255770421 1358982008034686367728477)
                      ·
                        rfl

theorem cell23_2646608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_2646608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646608 prefixEnd_2646608 := by exact prefixLift 2646608
  have htrace : WordTrace (prefixWord ++ tailWord_2646608) baseStart_2646608 baseEnd_2646608 := by
    simpa [prefixWord, tailWord_2646608, baseEnd_2646608] using wordTrace_append hprefix tailTrace_2646608
  have hstable : (prefixWord ++ tailWord_2646608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646608).length < 2 ^ (prefixWord ++ tailWord_2646608).sum := by decide
  have hdescent : baseEnd_2646608 < baseStart_2646608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646642 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2646642 : Nat := 118140960795 + 2646642 * 2 ^ 59
def prefixEnd_2646642 : Nat := 4983230072969 + 3 ^ 40 * 2646642 * 2
def baseEnd_2646642 : Nat := 1358999466376939234703321

theorem tailTrace_2646642 : CollatzResearch.WordTrace tailWord_2646642 prefixEnd_2646642 1358999466376939234703321 := by
  unfold tailWord_2646642
  simp only [CollatzResearch.WordTrace]
  refine ⟨24132741019418879828079545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64353976051783679541545453 24132741019418879828079545)
  ·
    refine ⟨18099555764564159871059659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24132741019418879828079545 18099555764564159871059659)
    ·
      refine ⟨27149333646846239806589489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18099555764564159871059659 27149333646846239806589489)
      ·
        refine ⟨20362000235134679854942117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27149333646846239806589489 20362000235134679854942117)
        ·
          refine ⟨3817875044087752472801647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20362000235134679854942117 3817875044087752472801647)
          ·
            refine ⟨5726812566131628709202471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817875044087752472801647 5726812566131628709202471)
            ·
              refine ⟨8590218849197443063803707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5726812566131628709202471 8590218849197443063803707)
              ·
                refine ⟨12885328273796164595705561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8590218849197443063803707 12885328273796164595705561)
                ·
                  refine ⟨9663996205347123446779171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12885328273796164595705561 9663996205347123446779171)
                  ·
                    refine ⟨14495994308020685170168757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9663996205347123446779171 14495994308020685170168757)
                    ·
                      refine ⟨1358999466376939234703321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14495994308020685170168757 1358999466376939234703321)
                      ·
                        rfl

theorem cell23_2646642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2646642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646642 prefixEnd_2646642 := by exact prefixLift 2646642
  have htrace : WordTrace (prefixWord ++ tailWord_2646642) baseStart_2646642 baseEnd_2646642 := by
    simpa [prefixWord, tailWord_2646642, baseEnd_2646642] using wordTrace_append hprefix tailTrace_2646642
  have hstable : (prefixWord ++ tailWord_2646642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646642).length < 2 ^ (prefixWord ++ tailWord_2646642).sum := by decide
  have hdescent : baseEnd_2646642 < baseStart_2646642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646655 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 3]
def baseStart_2646655 : Nat := 118140960795 + 2646655 * 2 ^ 59
def prefixEnd_2646655 : Nat := 4983230072969 + 3 ^ 40 * 2646655 * 2
def baseEnd_2646655 : Nat := 1359006141625447683840761

theorem tailTrace_2646655 : CollatzResearch.WordTrace tailWord_2646655 prefixEnd_2646655 1359006141625447683840761 := by
  unfold tailWord_2646655
  simp only [CollatzResearch.WordTrace]
  refine ⟨96531438226628422532541419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64354292151085615021694279 96531438226628422532541419)
  ·
    refine ⟨144797157339942633798812129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96531438226628422532541419 144797157339942633798812129)
    ·
      refine ⟨108597868004956975349109097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144797157339942633798812129 108597868004956975349109097)
      ·
        refine ⟨81448401003717731511831823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108597868004956975349109097 81448401003717731511831823)
        ·
          refine ⟨122172601505576597267747735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81448401003717731511831823 122172601505576597267747735)
          ·
            refine ⟨183258902258364895901621603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122172601505576597267747735 183258902258364895901621603)
            ·
              refine ⟨274888353387547343852432405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183258902258364895901621603 274888353387547343852432405)
              ·
                refine ⟨12885391565041281743082769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 274888353387547343852432405 12885391565041281743082769)
                ·
                  refine ⟨9664043673780961307312077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12885391565041281743082769 9664043673780961307312077)
                  ·
                    refine ⟨3624016377667860490242029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9664043673780961307312077 3624016377667860490242029)
                    ·
                      refine ⟨1359006141625447683840761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3624016377667860490242029 1359006141625447683840761)
                      ·
                        rfl

theorem cell23_2646655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_2646655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646655 prefixEnd_2646655 := by exact prefixLift 2646655
  have htrace : WordTrace (prefixWord ++ tailWord_2646655) baseStart_2646655 baseEnd_2646655 := by
    simpa [prefixWord, tailWord_2646655, baseEnd_2646655] using wordTrace_append hprefix tailTrace_2646655
  have hstable : (prefixWord ++ tailWord_2646655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646655).length < 2 ^ (prefixWord ++ tailWord_2646655).sum := by decide
  have hdescent : baseEnd_2646655 < baseStart_2646655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646692 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_2646692 : Nat := 118140960795 + 2646692 * 2 ^ 59
def prefixEnd_2646692 : Nat := 4983230072969 + 3 ^ 40 * 2646692 * 2
def baseEnd_2646692 : Nat := 453008380136554679692697

theorem tailTrace_2646692 : CollatzResearch.WordTrace tailWord_2646692 prefixEnd_2646692 453008380136554679692697 := by
  unfold tailWord_2646692
  simp only [CollatzResearch.WordTrace]
  refine ⟨48266393863747188925819165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64355191818329585234425553 48266393863747188925819165)
  ·
    refine ⟨18099897698905195847182187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48266393863747188925819165 18099897698905195847182187)
    ·
      refine ⟨27149846548357793770773281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18099897698905195847182187 27149846548357793770773281)
      ·
        refine ⟨20362384911268345328079961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27149846548357793770773281 20362384911268345328079961)
        ·
          refine ⟨15271788683451258996059971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20362384911268345328079961 15271788683451258996059971)
          ·
            refine ⟨22907683025176888494089957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15271788683451258996059971 22907683025176888494089957)
            ·
              refine ⟨4295190567220666592641867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22907683025176888494089957 4295190567220666592641867)
              ·
                refine ⟨6442785850830999888962801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4295190567220666592641867 6442785850830999888962801)
                ·
                  refine ⟨4832089388123249916722101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6442785850830999888962801 4832089388123249916722101)
                  ·
                    refine ⟨453008380136554679692697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4832089388123249916722101 453008380136554679692697)
                    ·
                      rfl

theorem cell23_2646692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_2646692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646692 prefixEnd_2646692 := by exact prefixLift 2646692
  have htrace : WordTrace (prefixWord ++ tailWord_2646692) baseStart_2646692 baseEnd_2646692 := by
    simpa [prefixWord, tailWord_2646692, baseEnd_2646692] using wordTrace_append hprefix tailTrace_2646692
  have hstable : (prefixWord ++ tailWord_2646692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646692).length < 2 ^ (prefixWord ++ tailWord_2646692).sum := by decide
  have hdescent : baseEnd_2646692 < baseStart_2646692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646715 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 3]
def baseStart_2646715 : Nat := 118140960795 + 2646715 * 2 ^ 59
def prefixEnd_2646715 : Nat := 4983230072969 + 3 ^ 40 * 2646715 * 2
def baseEnd_2646715 : Nat := 1359036950464717449090485

theorem tailTrace_2646715 : CollatzResearch.WordTrace tailWord_2646715 prefixEnd_2646715 1359036950464717449090485 := by
  unfold tailWord_2646715
  simp only [CollatzResearch.WordTrace]
  refine ⟨96533626606411052779725599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64355751070940701853150399 96533626606411052779725599)
  ·
    refine ⟨144800439909616579169588399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96533626606411052779725599 144800439909616579169588399)
    ·
      refine ⟨217200659864424868754382599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144800439909616579169588399 217200659864424868754382599)
      ·
        refine ⟨325800989796637303131573899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217200659864424868754382599 325800989796637303131573899)
        ·
          refine ⟨488701484694955954697360849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325800989796637303131573899 488701484694955954697360849)
          ·
            refine ⟨366526113521216966023020637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488701484694955954697360849 366526113521216966023020637)
            ·
              refine ⟨137447292570456362258632739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366526113521216966023020637 137447292570456362258632739)
              ·
                refine ⟨206170938855684543387949109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137447292570456362258632739 206170938855684543387949109)
                ·
                  refine ⟨19328525517720425942620229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206170938855684543387949109 19328525517720425942620229)
                  ·
                    refine ⟨3624098534572579864241293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19328525517720425942620229 3624098534572579864241293)
                    ·
                      refine ⟨1359036950464717449090485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3624098534572579864241293 1359036950464717449090485)
                      ·
                        rfl

theorem cell23_2646715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 3].length) (baseStart_2646715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646715 prefixEnd_2646715 := by exact prefixLift 2646715
  have htrace : WordTrace (prefixWord ++ tailWord_2646715) baseStart_2646715 baseEnd_2646715 := by
    simpa [prefixWord, tailWord_2646715, baseEnd_2646715] using wordTrace_append hprefix tailTrace_2646715
  have hstable : (prefixWord ++ tailWord_2646715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646715).length < 2 ^ (prefixWord ++ tailWord_2646715).sum := by decide
  have hdescent : baseEnd_2646715 < baseStart_2646715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646756 : List Nat := [2, 3, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_2646756 : Nat := 118140960795 + 2646756 * 2 ^ 59
def prefixEnd_2646756 : Nat := 4983230072969 + 3 ^ 40 * 2646756 * 2
def baseEnd_2646756 : Nat := 453019334390517262892599

theorem tailTrace_2646756 : CollatzResearch.WordTrace tailWord_2646756 prefixEnd_2646756 453019334390517262892599 := by
  unfold tailWord_2646756
  simp only [CollatzResearch.WordTrace]
  refine ⟨48267560999631258390984061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64356747999508344521312081 48267560999631258390984061)
  ·
    refine ⟨18100335374861721896619023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48267560999631258390984061 18100335374861721896619023)
    ·
      refine ⟨27150503062292582844928535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18100335374861721896619023 27150503062292582844928535)
      ·
        refine ⟨40725754593438874267392803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27150503062292582844928535 40725754593438874267392803)
        ·
          refine ⟨61088631890158311401089205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40725754593438874267392803 61088631890158311401089205)
          ·
            refine ⟨5727059239702341693852113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61088631890158311401089205 5727059239702341693852113)
            ·
              refine ⟨4295294429776756270389085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5727059239702341693852113 4295294429776756270389085)
              ·
                refine ⟨1610735411166283601395907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4295294429776756270389085 1610735411166283601395907)
                ·
                  refine ⟨2416103116749425402093861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610735411166283601395907 2416103116749425402093861)
                  ·
                    refine ⟨453019334390517262892599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2416103116749425402093861 453019334390517262892599)
                    ·
                      rfl

theorem cell23_2646756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_2646756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646756 prefixEnd_2646756 := by exact prefixLift 2646756
  have htrace : WordTrace (prefixWord ++ tailWord_2646756) baseStart_2646756 baseEnd_2646756 := by
    simpa [prefixWord, tailWord_2646756, baseEnd_2646756] using wordTrace_append hprefix tailTrace_2646756
  have hstable : (prefixWord ++ tailWord_2646756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646756).length < 2 ^ (prefixWord ++ tailWord_2646756).sum := by decide
  have hdescent : baseEnd_2646756 < baseStart_2646756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646786 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2646786 : Nat := 118140960795 + 2646786 * 2 ^ 59
def prefixEnd_2646786 : Nat := 4983230072969 + 3 ^ 40 * 2646786 * 2
def baseEnd_2646786 : Nat := 151008156399020741255851

theorem tailTrace_2646786 : CollatzResearch.WordTrace tailWord_2646786 prefixEnd_2646786 151008156399020741255851 := by
  unfold tailWord_2646786
  simp only [CollatzResearch.WordTrace]
  refine ⟨24134054047288457976390053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64357477459435887937040141 24134054047288457976390053)
  ·
    refine ⟨4525135133866585870573135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24134054047288457976390053 4525135133866585870573135)
    ·
      refine ⟨6787702700799878805859703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4525135133866585870573135 6787702700799878805859703)
      ·
        refine ⟨10181554051199818208789555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6787702700799878805859703 10181554051199818208789555)
        ·
          refine ⟨15272331076799727313184333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10181554051199818208789555 15272331076799727313184333)
          ·
            refine ⟨5727124153799897742444125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15272331076799727313184333 5727124153799897742444125)
            ·
              refine ⟨2147671557674961653416547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5727124153799897742444125 2147671557674961653416547)
              ·
                refine ⟨3221507336512442480124821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2147671557674961653416547 3221507336512442480124821)
                ·
                  refine ⟨151008156399020741255851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3221507336512442480124821 151008156399020741255851)
                  ·
                    rfl

theorem cell23_2646786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2646786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646786 prefixEnd_2646786 := by exact prefixLift 2646786
  have htrace : WordTrace (prefixWord ++ tailWord_2646786) baseStart_2646786 baseEnd_2646786 := by
    simpa [prefixWord, tailWord_2646786, baseEnd_2646786] using wordTrace_append hprefix tailTrace_2646786
  have hstable : (prefixWord ++ tailWord_2646786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646786).length < 2 ^ (prefixWord ++ tailWord_2646786).sum := by decide
  have hdescent : baseEnd_2646786 < baseStart_2646786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646869 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_2646869 : Nat := 118140960795 + 2646869 * 2 ^ 59
def prefixEnd_2646869 : Nat := 4983230072969 + 3 ^ 40 * 2646869 * 2
def baseEnd_2646869 : Nat := 1359116026485509846564777

theorem tailTrace_2646869 : CollatzResearch.WordTrace tailWord_2646869 prefixEnd_2646869 1359116026485509846564777 := by
  unfold tailWord_2646869
  simp only [CollatzResearch.WordTrace]
  refine ⟨96539243447853137080831661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64359495631902091387221107 96539243447853137080831661)
  ·
    refine ⟨36202216292944926405311873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96539243447853137080831661 36202216292944926405311873)
    ·
      refine ⟨27151662219708694803983905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36202216292944926405311873 27151662219708694803983905)
      ·
        refine ⟨20363746664781521102987929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27151662219708694803983905 20363746664781521102987929)
        ·
          refine ⟨15272809998586140827240947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20363746664781521102987929 15272809998586140827240947)
          ·
            refine ⟨22909214997879211240861421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15272809998586140827240947 22909214997879211240861421)
            ·
              refine ⟨8590955624204704215323033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22909214997879211240861421 8590955624204704215323033)
              ·
                refine ⟨6443216718153528161492275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8590955624204704215323033 6443216718153528161492275)
                ·
                  refine ⟨9664825077230292242238413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6443216718153528161492275 9664825077230292242238413)
                  ·
                    refine ⟨3624309403961359590839405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9664825077230292242238413 3624309403961359590839405)
                    ·
                      refine ⟨1359116026485509846564777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3624309403961359590839405 1359116026485509846564777)
                      ·
                        rfl

theorem cell23_2646869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_2646869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646869 prefixEnd_2646869 := by exact prefixLift 2646869
  have htrace : WordTrace (prefixWord ++ tailWord_2646869) baseStart_2646869 baseEnd_2646869 := by
    simpa [prefixWord, tailWord_2646869, baseEnd_2646869] using wordTrace_append hprefix tailTrace_2646869
  have hstable : (prefixWord ++ tailWord_2646869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646869).length < 2 ^ (prefixWord ++ tailWord_2646869).sum := by decide
  have hdescent : baseEnd_2646869 < baseStart_2646869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646887 : List Nat := [1, 1, 5, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_2646887 : Nat := 118140960795 + 2646887 * 2 ^ 59
def prefixEnd_2646887 : Nat := 4983230072969 + 3 ^ 40 * 2646887 * 2
def baseEnd_2646887 : Nat := 1359125269137290776139695

theorem tailTrace_2646887 : CollatzResearch.WordTrace tailWord_2646887 prefixEnd_2646887 1359125269137290776139695 := by
  unfold tailWord_2646887
  simp only [CollatzResearch.WordTrace]
  refine ⟨96539899961787926154986915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64359933307858617436657943 96539899961787926154986915)
  ·
    refine ⟨144809849942681889232480373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96539899961787926154986915 144809849942681889232480373)
    ·
      refine ⟨13575923432126427115545035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144809849942681889232480373 13575923432126427115545035)
      ·
        refine ⟨20363885148189640673317553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13575923432126427115545035 20363885148189640673317553)
        ·
          refine ⟨15272913861142230504988165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20363885148189640673317553 15272913861142230504988165)
          ·
            refine ⟨2863671348964168219685281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15272913861142230504988165 2863671348964168219685281)
            ·
              refine ⟨2147753511723126164763961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863671348964168219685281 2147753511723126164763961)
              ·
                refine ⟨1610815133792344623572971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147753511723126164763961 1610815133792344623572971)
                ·
                  refine ⟨2416222700688516935359457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610815133792344623572971 2416222700688516935359457)
                  ·
                    refine ⟨1812167025516387701519593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2416222700688516935359457 1812167025516387701519593)
                    ·
                      refine ⟨1359125269137290776139695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812167025516387701519593 1359125269137290776139695)
                      ·
                        rfl

theorem cell23_2646887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_2646887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646887 prefixEnd_2646887 := by exact prefixLift 2646887
  have htrace : WordTrace (prefixWord ++ tailWord_2646887) baseStart_2646887 baseEnd_2646887 := by
    simpa [prefixWord, tailWord_2646887, baseEnd_2646887] using wordTrace_append hprefix tailTrace_2646887
  have hstable : (prefixWord ++ tailWord_2646887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646887).length < 2 ^ (prefixWord ++ tailWord_2646887).sum := by decide
  have hdescent : baseEnd_2646887 < baseStart_2646887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646892 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2646892 : Nat := 118140960795 + 2646892 * 2 ^ 59
def prefixEnd_2646892 : Nat := 4983230072969 + 3 ^ 40 * 2646892 * 2
def baseEnd_2646892 : Nat := 1359127836540563256577171

theorem tailTrace_2646892 : CollatzResearch.WordTrace tailWord_2646892 prefixEnd_2646892 1359127836540563256577171 := by
  unfold tailWord_2646892
  simp only [CollatzResearch.WordTrace]
  refine ⟨48270041163384906004459465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64360054884513208005945953 48270041163384906004459465)
  ·
    refine ⟨36202530872538679503344599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48270041163384906004459465 36202530872538679503344599)
    ·
      refine ⟨54303796308808019255016899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36202530872538679503344599 54303796308808019255016899)
      ·
        refine ⟨81455694463212028882525349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54303796308808019255016899 81455694463212028882525349)
        ·
          refine ⟨15272942711852255415473503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81455694463212028882525349 15272942711852255415473503)
          ·
            refine ⟨22909414067778383123210255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15272942711852255415473503 22909414067778383123210255)
            ·
              refine ⟨34364121101667574684815383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22909414067778383123210255 34364121101667574684815383)
              ·
                refine ⟨51546181652501362027223075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34364121101667574684815383 51546181652501362027223075)
                ·
                  refine ⟨77319272478752043040834613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51546181652501362027223075 77319272478752043040834613)
                  ·
                    refine ⟨7248681794883004035078245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77319272478752043040834613 7248681794883004035078245)
                    ·
                      refine ⟨1359127836540563256577171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7248681794883004035078245 1359127836540563256577171)
                      ·
                        rfl

theorem cell23_2646892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2646892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646892 prefixEnd_2646892 := by exact prefixLift 2646892
  have htrace : WordTrace (prefixWord ++ tailWord_2646892) baseStart_2646892 baseEnd_2646892 := by
    simpa [prefixWord, tailWord_2646892, baseEnd_2646892] using wordTrace_append hprefix tailTrace_2646892
  have hstable : (prefixWord ++ tailWord_2646892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646892).length < 2 ^ (prefixWord ++ tailWord_2646892).sum := by decide
  have hdescent : baseEnd_2646892 < baseStart_2646892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646912 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_2646912 : Nat := 118140960795 + 2646912 * 2 ^ 59
def prefixEnd_2646912 : Nat := 4983230072969 + 3 ^ 40 * 2646912 * 2
def baseEnd_2646912 : Nat := 1359138106153653178327079

theorem tailTrace_2646912 : CollatzResearch.WordTrace tailWord_2646912 prefixEnd_2646912 1359138106153653178327079 := by
  unfold tailWord_2646912
  simp only [CollatzResearch.WordTrace]
  refine ⟨48270405893348677712323495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64360541191131570283097993 48270405893348677712323495)
  ·
    refine ⟨72405608840023016568485243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48270405893348677712323495 72405608840023016568485243)
    ·
      refine ⟨108608413260034524852727865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72405608840023016568485243 108608413260034524852727865)
      ·
        refine ⟨81456309945025893639545899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108608413260034524852727865 81456309945025893639545899)
        ·
          refine ⟨122184464917538840459318849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81456309945025893639545899 122184464917538840459318849)
          ·
            refine ⟨91638348688154130344489137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122184464917538840459318849 91638348688154130344489137)
            ·
              refine ⟨68728761516115597758366853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91638348688154130344489137 68728761516115597758366853)
              ·
                refine ⟨12886642784271674579693785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68728761516115597758366853 12886642784271674579693785)
                ·
                  refine ⟨9664982088203755934770339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12886642784271674579693785 9664982088203755934770339)
                  ·
                    refine ⟨14497473132305633902155509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9664982088203755934770339 14497473132305633902155509)
                    ·
                      refine ⟨1359138106153653178327079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14497473132305633902155509 1359138106153653178327079)
                      ·
                        rfl

theorem cell23_2646912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_2646912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646912 prefixEnd_2646912 := by exact prefixLift 2646912
  have htrace : WordTrace (prefixWord ++ tailWord_2646912) baseStart_2646912 baseEnd_2646912 := by
    simpa [prefixWord, tailWord_2646912, baseEnd_2646912] using wordTrace_append hprefix tailTrace_2646912
  have hstable : (prefixWord ++ tailWord_2646912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646912).length < 2 ^ (prefixWord ++ tailWord_2646912).sum := by decide
  have hdescent : baseEnd_2646912 < baseStart_2646912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646930 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2646930 : Nat := 118140960795 + 2646930 * 2 ^ 59
def prefixEnd_2646930 : Nat := 4983230072969 + 3 ^ 40 * 2646930 * 2
def baseEnd_2646930 : Nat := 1359147348805434107901997

theorem tailTrace_2646930 : CollatzResearch.WordTrace tailWord_2646930 prefixEnd_2646930 1359147348805434107901997 := by
  unfold tailWord_2646930
  simp only [CollatzResearch.WordTrace]
  refine ⟨24135367075158036124700561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64360978867088096332534829 24135367075158036124700561)
  ·
    refine ⟨18101525306368527093525421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24135367075158036124700561 18101525306368527093525421)
    ·
      refine ⟨6788071989888197660072033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18101525306368527093525421 6788071989888197660072033)
      ·
        refine ⟨5091053992416148245054025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6788071989888197660072033 5091053992416148245054025)
        ·
          refine ⟨3818290494312111183790519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5091053992416148245054025 3818290494312111183790519)
          ·
            refine ⟨5727435741468166775685779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818290494312111183790519 5727435741468166775685779)
            ·
              refine ⟨8591153612202250163528669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727435741468166775685779 8591153612202250163528669)
              ·
                refine ⟨3221682604575843811323251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8591153612202250163528669 3221682604575843811323251)
                ·
                  refine ⟨4832523906863765716984877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221682604575843811323251 4832523906863765716984877)
                  ·
                    refine ⟨1812196465073912143869329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4832523906863765716984877 1812196465073912143869329)
                    ·
                      refine ⟨1359147348805434107901997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812196465073912143869329 1359147348805434107901997)
                      ·
                        rfl

theorem cell23_2646930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2646930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646930 prefixEnd_2646930 := by exact prefixLift 2646930
  have htrace : WordTrace (prefixWord ++ tailWord_2646930) baseStart_2646930 baseEnd_2646930 := by
    simpa [prefixWord, tailWord_2646930, baseEnd_2646930] using wordTrace_append hprefix tailTrace_2646930
  have hstable : (prefixWord ++ tailWord_2646930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646930).length < 2 ^ (prefixWord ++ tailWord_2646930).sum := by decide
  have hdescent : baseEnd_2646930 < baseStart_2646930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646943 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 4, 2, 2]
def baseStart_2646943 : Nat := 118140960795 + 2646943 * 2 ^ 59
def prefixEnd_2646943 : Nat := 4983230072969 + 3 ^ 40 * 2646943 * 2
def baseEnd_2646943 : Nat := 1359154024053942557039437

theorem tailTrace_2646943 : CollatzResearch.WordTrace tailWord_2646943 prefixEnd_2646943 1359154024053942557039437 := by
  unfold tailWord_2646943
  simp only [CollatzResearch.WordTrace]
  refine ⟨96541942449585047719025483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64361294966390031812683655 96541942449585047719025483)
  ·
    refine ⟨144812913674377571578538225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96541942449585047719025483 144812913674377571578538225)
    ·
      refine ⟨108609685255783178683903669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144812913674377571578538225 108609685255783178683903669)
      ·
        refine ⟨10182157992729673001615969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108609685255783178683903669 10182157992729673001615969)
        ·
          refine ⟨7636618494547254751211977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10182157992729673001615969 7636618494547254751211977)
          ·
            refine ⟨5727463870910441063408983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7636618494547254751211977 5727463870910441063408983)
            ·
              refine ⟨8591195806365661595113475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727463870910441063408983 8591195806365661595113475)
              ·
                refine ⟨12886793709548492392670213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8591195806365661595113475 12886793709548492392670213)
                ·
                  refine ⟨2416273820540342323625665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12886793709548492392670213 2416273820540342323625665)
                  ·
                    refine ⟨1812205365405256742719249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2416273820540342323625665 1812205365405256742719249)
                    ·
                      refine ⟨1359154024053942557039437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812205365405256742719249 1359154024053942557039437)
                      ·
                        rfl

theorem cell23_2646943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_2646943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646943 prefixEnd_2646943 := by exact prefixLift 2646943
  have htrace : WordTrace (prefixWord ++ tailWord_2646943) baseStart_2646943 baseEnd_2646943 := by
    simpa [prefixWord, tailWord_2646943, baseEnd_2646943] using wordTrace_append hprefix tailTrace_2646943
  have hstable : (prefixWord ++ tailWord_2646943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646943).length < 2 ^ (prefixWord ++ tailWord_2646943).sum := by decide
  have hdescent : baseEnd_2646943 < baseStart_2646943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2646996 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_2646996 : Nat := 118140960795 + 2646996 * 2 ^ 59
def prefixEnd_2646996 : Nat := 4983230072969 + 3 ^ 40 * 2646996 * 2
def baseEnd_2646996 : Nat := 453060412842876949892231

theorem tailTrace_2646996 : CollatzResearch.WordTrace tailWord_2646996 prefixEnd_2646996 453060412842876949892231 := by
  unfold tailWord_2646996
  simp only [CollatzResearch.WordTrace]
  refine ⟨48271937759196518885352421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64362583678928691847136561 48271937759196518885352421)
  ·
    refine ⟨9050988329849347291003579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48271937759196518885352421 9050988329849347291003579)
    ·
      refine ⟨13576482494774020936505369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9050988329849347291003579 13576482494774020936505369)
      ·
        refine ⟨10182361871080515702379027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13576482494774020936505369 10182361871080515702379027)
        ·
          refine ⟨15273542806620773553568541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10182361871080515702379027 15273542806620773553568541)
          ·
            refine ⟨5727578552482790082588203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15273542806620773553568541 5727578552482790082588203)
            ·
              refine ⟨8591367828724185123882305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727578552482790082588203 8591367828724185123882305)
              ·
                refine ⟨6443525871543138842911729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8591367828724185123882305 6443525871543138842911729)
                ·
                  refine ⟨4832644403657354132183797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443525871543138842911729 4832644403657354132183797)
                  ·
                    refine ⟨453060412842876949892231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4832644403657354132183797 453060412842876949892231)
                    ·
                      rfl

theorem cell23_2646996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_2646996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2646996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2646996 prefixEnd_2646996 := by exact prefixLift 2646996
  have htrace : WordTrace (prefixWord ++ tailWord_2646996) baseStart_2646996 baseEnd_2646996 := by
    simpa [prefixWord, tailWord_2646996, baseEnd_2646996] using wordTrace_append hprefix tailTrace_2646996
  have hstable : (prefixWord ++ tailWord_2646996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2646996).length < 2 ^ (prefixWord ++ tailWord_2646996).sum := by decide
  have hdescent : baseEnd_2646996 < baseStart_2646996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2646996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647016 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_2647016 : Nat := 118140960795 + 2647016 * 2 ^ 59
def prefixEnd_2647016 : Nat := 4983230072969 + 3 ^ 40 * 2647016 * 2
def baseEnd_2647016 : Nat := 1359191508141720771426601

theorem tailTrace_2647016 : CollatzResearch.WordTrace tailWord_2647016 prefixEnd_2647016 1359191508141720771426601 := by
  unfold tailWord_2647016
  simp only [CollatzResearch.WordTrace]
  refine ⟨48272302489160290593216451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64363069985547054124288601 48272302489160290593216451)
  ·
    refine ⟨72408453733740435889824677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48272302489160290593216451 72408453733740435889824677)
    ·
      refine ⟨13576585075076331729342127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72408453733740435889824677 13576585075076331729342127)
      ·
        refine ⟨20364877612614497594013191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13576585075076331729342127 20364877612614497594013191)
        ·
          refine ⟨30547316418921746391019787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20364877612614497594013191 30547316418921746391019787)
          ·
            refine ⟨45820974628382619586529681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30547316418921746391019787 45820974628382619586529681)
            ·
              refine ⟨34365730971286964689897261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45820974628382619586529681 34365730971286964689897261)
              ·
                refine ⟨12887149114232611758711473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34365730971286964689897261 12887149114232611758711473)
                ·
                  refine ⟨9665361835674458819033605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12887149114232611758711473 9665361835674458819033605)
                  ·
                    refine ⟨1812255344188961028568801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9665361835674458819033605 1812255344188961028568801)
                    ·
                      refine ⟨1359191508141720771426601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812255344188961028568801 1359191508141720771426601)
                      ·
                        rfl

theorem cell23_2647016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_2647016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647016 prefixEnd_2647016 := by exact prefixLift 2647016
  have htrace : WordTrace (prefixWord ++ tailWord_2647016) baseStart_2647016 baseEnd_2647016 := by
    simpa [prefixWord, tailWord_2647016, baseEnd_2647016] using wordTrace_append hprefix tailTrace_2647016
  have hstable : (prefixWord ++ tailWord_2647016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647016).length < 2 ^ (prefixWord ++ tailWord_2647016).sum := by decide
  have hdescent : baseEnd_2647016 < baseStart_2647016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647036 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_2647036 : Nat := 118140960795 + 2647036 * 2 ^ 59
def prefixEnd_2647036 : Nat := 4983230072969 + 3 ^ 40 * 2647036 * 2
def baseEnd_2647036 : Nat := 1359201777754810693176509

theorem tailTrace_2647036 : CollatzResearch.WordTrace tailWord_2647036 prefixEnd_2647036 1359201777754810693176509 := by
  unfold tailWord_2647036
  simp only [CollatzResearch.WordTrace]
  refine ⟨48272667219124062301080481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64363556292165416401440641 48272667219124062301080481)
  ·
    refine ⟨36204500414343046725810361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48272667219124062301080481 36204500414343046725810361)
    ·
      refine ⟨27153375310757285044357771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36204500414343046725810361 27153375310757285044357771)
      ·
        refine ⟨40730062966135927566536657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27153375310757285044357771 40730062966135927566536657)
        ·
          refine ⟨30547547224601945674902493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40730062966135927566536657 30547547224601945674902493)
          ·
            refine ⟨11455330209225729628088435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30547547224601945674902493 11455330209225729628088435)
            ·
              refine ⟨17182995313838594442132653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11455330209225729628088435 17182995313838594442132653)
              ·
                refine ⟨6443623242689472915799745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17182995313838594442132653 6443623242689472915799745)
                ·
                  refine ⟨4832717432017104686849809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443623242689472915799745 4832717432017104686849809)
                  ·
                    refine ⟨3624538074012828515137357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4832717432017104686849809 3624538074012828515137357)
                    ·
                      refine ⟨1359201777754810693176509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3624538074012828515137357 1359201777754810693176509)
                      ·
                        rfl

theorem cell23_2647036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_2647036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647036 prefixEnd_2647036 := by exact prefixLift 2647036
  have htrace : WordTrace (prefixWord ++ tailWord_2647036) baseStart_2647036 baseEnd_2647036 := by
    simpa [prefixWord, tailWord_2647036, baseEnd_2647036] using wordTrace_append hprefix tailTrace_2647036
  have hstable : (prefixWord ++ tailWord_2647036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647036).length < 2 ^ (prefixWord ++ tailWord_2647036).sum := by decide
  have hdescent : baseEnd_2647036 < baseStart_2647036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647086 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2647086 : Nat := 118140960795 + 2647086 * 2 ^ 59
def prefixEnd_2647086 : Nat := 4983230072969 + 3 ^ 40 * 2647086 * 2
def baseEnd_2647086 : Nat := 453075817262511832517093

theorem tailTrace_2647086 : CollatzResearch.WordTrace tailWord_2647086 prefixEnd_2647086 453075817262511832517093 := by
  unfold tailWord_2647086
  simp only [CollatzResearch.WordTrace]
  refine ⟨12068394761008372892685139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64364772058711322094320741 12068394761008372892685139)
  ·
    refine ⟨18102592141512559339027709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12068394761008372892685139 18102592141512559339027709)
    ·
      refine ⟨6788472053067209752135391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18102592141512559339027709 6788472053067209752135391)
      ·
        refine ⟨10182708079600814628203087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6788472053067209752135391 10182708079600814628203087)
        ·
          refine ⟨15274062119401221942304631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10182708079600814628203087 15274062119401221942304631)
          ·
            refine ⟨22911093179101832913456947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15274062119401221942304631 22911093179101832913456947)
            ·
              refine ⟨34366639768652749370185421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22911093179101832913456947 34366639768652749370185421)
              ·
                refine ⟨12887489913244781013819533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34366639768652749370185421 12887489913244781013819533)
                ·
                  refine ⟨4832808717466792880182325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12887489913244781013819533 4832808717466792880182325)
                  ·
                    refine ⟨453075817262511832517093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4832808717466792880182325 453075817262511832517093)
                    ·
                      rfl

theorem cell23_2647086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2647086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647086 prefixEnd_2647086 := by exact prefixLift 2647086
  have htrace : WordTrace (prefixWord ++ tailWord_2647086) baseStart_2647086 baseEnd_2647086 := by
    simpa [prefixWord, tailWord_2647086, baseEnd_2647086] using wordTrace_append hprefix tailTrace_2647086
  have hstable : (prefixWord ++ tailWord_2647086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647086).length < 2 ^ (prefixWord ++ tailWord_2647086).sum := by decide
  have hdescent : baseEnd_2647086 < baseStart_2647086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647100 : List Nat := [2, 2, 2, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_2647100 : Nat := 118140960795 + 2647100 * 2 ^ 59
def prefixEnd_2647100 : Nat := 4983230072969 + 3 ^ 40 * 2647100 * 2
def baseEnd_2647100 : Nat := 1359234640516698442776215

theorem tailTrace_2647100 : CollatzResearch.WordTrace tailWord_2647100 prefixEnd_2647100 1359234640516698442776215 := by
  unfold tailWord_2647100
  simp only [CollatzResearch.WordTrace]
  refine ⟨48273834355008131766245377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64365112473344175688327169 48273834355008131766245377)
  ·
    refine ⟨36205375766256098824684033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48273834355008131766245377 36205375766256098824684033)
    ·
      refine ⟨27154031824692074118513025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36205375766256098824684033 27154031824692074118513025)
      ·
        refine ⟨20365523868519055588884769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27154031824692074118513025 20365523868519055588884769)
        ·
          refine ⟨15274142901389291691663577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20365523868519055588884769 15274142901389291691663577)
          ·
            refine ⟨11455607176041968768747683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15274142901389291691663577 11455607176041968768747683)
            ·
              refine ⟨17183410764062953153121525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11455607176041968768747683 17183410764062953153121525)
              ·
                refine ⟨1610944759130901858105143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17183410764062953153121525 1610944759130901858105143)
                ·
                  refine ⟨2416417138696352787157715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610944759130901858105143 2416417138696352787157715)
                  ·
                    refine ⟨3624625708044529180736573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2416417138696352787157715 3624625708044529180736573)
                    ·
                      refine ⟨1359234640516698442776215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3624625708044529180736573 1359234640516698442776215)
                      ·
                        rfl

theorem cell23_2647100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_2647100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647100 prefixEnd_2647100 := by exact prefixLift 2647100
  have htrace : WordTrace (prefixWord ++ tailWord_2647100) baseStart_2647100 baseEnd_2647100 := by
    simpa [prefixWord, tailWord_2647100, baseEnd_2647100] using wordTrace_append hprefix tailTrace_2647100
  have hstable : (prefixWord ++ tailWord_2647100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647100).length < 2 ^ (prefixWord ++ tailWord_2647100).sum := by decide
  have hdescent : baseEnd_2647100 < baseStart_2647100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647117 : List Nat := [1, 6, 1, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_2647117 : Nat := 118140960795 + 2647117 * 2 ^ 59
def prefixEnd_2647117 : Nat := 4983230072969 + 3 ^ 40 * 2647117 * 2
def baseEnd_2647117 : Nat := 1359243369687824876263637

theorem tailTrace_2647117 : CollatzResearch.WordTrace tailWord_2647117 prefixEnd_2647117 1359243369687824876263637 := by
  unfold tailWord_2647117
  simp only [CollatzResearch.WordTrace]
  refine ⟨96548288750954675435859605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64365525833969783623906403 96548288750954675435859605)
  ·
    refine ⟨4525701035201000411055919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96548288750954675435859605 4525701035201000411055919)
    ·
      refine ⟨6788551552801500616583879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4525701035201000411055919 6788551552801500616583879)
      ·
        refine ⟨10182827329202250924875819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6788551552801500616583879 10182827329202250924875819)
        ·
          refine ⟨15274240993803376387313729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10182827329202250924875819 15274240993803376387313729)
          ·
            refine ⟨11455680745352532290485297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15274240993803376387313729 11455680745352532290485297)
            ·
              refine ⟨8591760559014399217863973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11455680745352532290485297 8591760559014399217863973)
              ·
                refine ⟨1610955104815199853349495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8591760559014399217863973 1610955104815199853349495)
                ·
                  refine ⟨2416432657222799780024243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610955104815199853349495 2416432657222799780024243)
                  ·
                    refine ⟨3624648985834199670036365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2416432657222799780024243 3624648985834199670036365)
                    ·
                      refine ⟨1359243369687824876263637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3624648985834199670036365 1359243369687824876263637)
                      ·
                        rfl

theorem cell23_2647117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_2647117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647117 prefixEnd_2647117 := by exact prefixLift 2647117
  have htrace : WordTrace (prefixWord ++ tailWord_2647117) baseStart_2647117 baseEnd_2647117 := by
    simpa [prefixWord, tailWord_2647117, baseEnd_2647117] using wordTrace_append hprefix tailTrace_2647117
  have hstable : (prefixWord ++ tailWord_2647117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647117).length < 2 ^ (prefixWord ++ tailWord_2647117).sum := by decide
  have hdescent : baseEnd_2647117 < baseStart_2647117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647123 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 3, 2, 2]
def baseStart_2647123 : Nat := 118140960795 + 2647123 * 2 ^ 59
def prefixEnd_2647123 : Nat := 4983230072969 + 3 ^ 40 * 2647123 * 2
def baseEnd_2647123 : Nat := 1359246450571751852788609

theorem tailTrace_2647123 : CollatzResearch.WordTrace tailWord_2647123 prefixEnd_2647123 1359246450571751852788609 := by
  unfold tailWord_2647123
  simp only [CollatzResearch.WordTrace]
  refine ⟨96548507588932938460578023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64365671725955292307052015 96548507588932938460578023)
  ·
    refine ⟨144822761383399407690867035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96548507588932938460578023 144822761383399407690867035)
    ·
      refine ⟨217234142075099111536300553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144822761383399407690867035 217234142075099111536300553)
      ·
        refine ⟨162925606556324333652225415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217234142075099111536300553 162925606556324333652225415)
        ·
          refine ⟨244388409834486500478338123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162925606556324333652225415 244388409834486500478338123)
          ·
            refine ⟨366582614751729750717507185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244388409834486500478338123 366582614751729750717507185)
            ·
              refine ⟨274936961063797313038130389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366582614751729750717507185 274936961063797313038130389)
              ·
                refine ⟨6443835024932749524331181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 274936961063797313038130389 6443835024932749524331181)
                ·
                  refine ⟨2416438134349781071624193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6443835024932749524331181 2416438134349781071624193)
                  ·
                    refine ⟨1812328600762335803718145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2416438134349781071624193 1812328600762335803718145)
                    ·
                      refine ⟨1359246450571751852788609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812328600762335803718145 1359246450571751852788609)
                      ·
                        rfl

theorem cell23_2647123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 2, 2].length) (baseStart_2647123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647123 prefixEnd_2647123 := by exact prefixLift 2647123
  have htrace : WordTrace (prefixWord ++ tailWord_2647123) baseStart_2647123 baseEnd_2647123 := by
    simpa [prefixWord, tailWord_2647123, baseEnd_2647123] using wordTrace_append hprefix tailTrace_2647123
  have hstable : (prefixWord ++ tailWord_2647123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647123).length < 2 ^ (prefixWord ++ tailWord_2647123).sum := by decide
  have hdescent : baseEnd_2647123 < baseStart_2647123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647143 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_2647143 : Nat := 118140960795 + 2647143 * 2 ^ 59
def prefixEnd_2647143 : Nat := 4983230072969 + 3 ^ 40 * 2647143 * 2
def baseEnd_2647143 : Nat := 1359256720184841774538517

theorem tailTrace_2647143 : CollatzResearch.WordTrace tailWord_2647143 prefixEnd_2647143 1359256720184841774538517 := by
  unfold tailWord_2647143
  simp only [CollatzResearch.WordTrace]
  refine ⟨96549237048860481876306083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64366158032573654584204055 96549237048860481876306083)
  ·
    refine ⟨144823855573290722814459125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96549237048860481876306083 144823855573290722814459125)
    ·
      refine ⟨13577236459996005263855543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144823855573290722814459125 13577236459996005263855543)
      ·
        refine ⟨20365854689994007895783315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13577236459996005263855543 20365854689994007895783315)
        ·
          refine ⟨30548782034991011843674973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20365854689994007895783315 30548782034991011843674973)
          ·
            refine ⟨11455793263121629441378115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30548782034991011843674973 11455793263121629441378115)
            ·
              refine ⟨17183689894682444162067173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11455793263121629441378115 17183689894682444162067173)
              ·
                refine ⟨3221941855252958280387595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17183689894682444162067173 3221941855252958280387595)
                ·
                  refine ⟨4832912782879437420581393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221941855252958280387595 4832912782879437420581393)
                  ·
                    refine ⟨3624684587159578065436045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4832912782879437420581393 3624684587159578065436045)
                    ·
                      refine ⟨1359256720184841774538517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3624684587159578065436045 1359256720184841774538517)
                      ·
                        rfl

theorem cell23_2647143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_2647143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647143 prefixEnd_2647143 := by exact prefixLift 2647143
  have htrace : WordTrace (prefixWord ++ tailWord_2647143) baseStart_2647143 baseEnd_2647143 := by
    simpa [prefixWord, tailWord_2647143, baseEnd_2647143] using wordTrace_append hprefix tailTrace_2647143
  have hstable : (prefixWord ++ tailWord_2647143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647143).length < 2 ^ (prefixWord ++ tailWord_2647143).sum := by decide
  have hdescent : baseEnd_2647143 < baseStart_2647143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647146 : List Nat := [3, 1, 3, 2, 2, 2, 1, 9]
def baseStart_2647146 : Nat := 118140960795 + 2647146 * 2 ^ 59
def prefixEnd_2647146 : Nat := 4983230072969 + 3 ^ 40 * 2647146 * 2
def baseEnd_2647146 : Nat := 50342898541733528251889

theorem tailTrace_2647146 : CollatzResearch.WordTrace tailWord_2647146 prefixEnd_2647146 50342898541733528251889 := by
  unfold tailWord_2647146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24137336616962403347166323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64366230978566408925776861 24137336616962403347166323)
  ·
    refine ⟨36206004925443605020749485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24137336616962403347166323 36206004925443605020749485)
    ·
      refine ⟨13577251847041351882781057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36206004925443605020749485 13577251847041351882781057)
      ·
        refine ⟨10182938885281013912085793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13577251847041351882781057 10182938885281013912085793)
        ·
          refine ⟨7637204163960760434064345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10182938885281013912085793 7637204163960760434064345)
          ·
            refine ⟨5727903122970570325548259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7637204163960760434064345 5727903122970570325548259)
            ·
              refine ⟨8591854684455855488322389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727903122970570325548259 8591854684455855488322389)
              ·
                refine ⟨50342898541733528251889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8591854684455855488322389 50342898541733528251889)
                ·
                  rfl

theorem cell23_2647146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 9].length) (baseStart_2647146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647146 prefixEnd_2647146 := by exact prefixLift 2647146
  have htrace : WordTrace (prefixWord ++ tailWord_2647146) baseStart_2647146 baseEnd_2647146 := by
    simpa [prefixWord, tailWord_2647146, baseEnd_2647146] using wordTrace_append hprefix tailTrace_2647146
  have hstable : (prefixWord ++ tailWord_2647146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647146).length < 2 ^ (prefixWord ++ tailWord_2647146).sum := by decide
  have hdescent : baseEnd_2647146 < baseStart_2647146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647226 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_2647226 : Nat := 118140960795 + 2647226 * 2 ^ 59
def prefixEnd_2647226 : Nat := 4983230072969 + 3 ^ 40 * 2647226 * 2
def baseEnd_2647226 : Nat := 1359299339079164949800635

theorem tailTrace_2647226 : CollatzResearch.WordTrace tailWord_2647226 prefixEnd_2647226 1359299339079164949800635 := by
  unfold tailWord_2647226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24138066076889946762894383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64368176205039858034385021 24138066076889946762894383)
  ·
    refine ⟨36207099115334920144341575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24138066076889946762894383 36207099115334920144341575)
    ·
      refine ⟨54310648673002380216512363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36207099115334920144341575 54310648673002380216512363)
      ·
        refine ⟨81465973009503570324768545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54310648673002380216512363 81465973009503570324768545)
        ·
          refine ⟨61099479757127677743576409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81465973009503570324768545 61099479757127677743576409)
          ·
            refine ⟨45824609817845758307682307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61099479757127677743576409 45824609817845758307682307)
            ·
              refine ⟨68736914726768637461523461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45824609817845758307682307 68736914726768637461523461)
              ·
                refine ⟨12888171511269119524035649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68736914726768637461523461 12888171511269119524035649)
                ·
                  refine ⟨9666128633451839643026737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12888171511269119524035649 9666128633451839643026737)
                  ·
                    refine ⟨7249596475088879732270053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9666128633451839643026737 7249596475088879732270053)
                    ·
                      refine ⟨1359299339079164949800635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7249596475088879732270053 1359299339079164949800635)
                      ·
                        rfl

theorem cell23_2647226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_2647226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647226 prefixEnd_2647226 := by exact prefixLift 2647226
  have htrace : WordTrace (prefixWord ++ tailWord_2647226) baseStart_2647226 baseEnd_2647226 := by
    simpa [prefixWord, tailWord_2647226, baseEnd_2647226] using wordTrace_append hprefix tailTrace_2647226
  have hstable : (prefixWord ++ tailWord_2647226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647226).length < 2 ^ (prefixWord ++ tailWord_2647226).sum := by decide
  have hdescent : baseEnd_2647226 < baseStart_2647226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647253 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 7]
def baseStart_2647253 : Nat := 118140960795 + 2647253 * 2 ^ 59
def prefixEnd_2647253 : Nat := 4983230072969 + 3 ^ 40 * 2647253 * 2
def baseEnd_2647253 : Nat := 151034800339648482684779

theorem tailTrace_2647253 : CollatzResearch.WordTrace tailWord_2647253 prefixEnd_2647253 151034800339648482684779 := by
  unfold tailWord_2647253
  simp only [CollatzResearch.WordTrace]
  refine ⟨96553249078461970662810413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64368832718974647108540275 96553249078461970662810413)
  ·
    refine ⟨36207468404423238998553905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96553249078461970662810413 36207468404423238998553905)
    ·
      refine ⟨27155601303317429248915429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36207468404423238998553905 27155601303317429248915429)
      ·
        refine ⟨5091675244372017984171643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27155601303317429248915429 5091675244372017984171643)
        ·
          refine ⟨7637512866558026976257465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091675244372017984171643 7637512866558026976257465)
          ·
            refine ⟨5728134649918520232193099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7637512866558026976257465 5728134649918520232193099)
            ·
              refine ⟨8592201974877780348289649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5728134649918520232193099 8592201974877780348289649)
              ·
                refine ⟨6444151481158335261217237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8592201974877780348289649 6444151481158335261217237)
                ·
                  refine ⟨151034800339648482684779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6444151481158335261217237 151034800339648482684779)
                  ·
                    rfl

theorem cell23_2647253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_2647253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647253 prefixEnd_2647253 := by exact prefixLift 2647253
  have htrace : WordTrace (prefixWord ++ tailWord_2647253) baseStart_2647253 baseEnd_2647253 := by
    simpa [prefixWord, tailWord_2647253, baseEnd_2647253] using wordTrace_append hprefix tailTrace_2647253
  have hstable : (prefixWord ++ tailWord_2647253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647253).length < 2 ^ (prefixWord ++ tailWord_2647253).sum := by decide
  have hdescent : baseEnd_2647253 < baseStart_2647253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647313 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 3, 4]
def baseStart_2647313 : Nat := 118140960795 + 2647313 * 2 ^ 59
def prefixEnd_2647313 : Nat := 4983230072969 + 3 ^ 40 * 2647313 * 2
def baseEnd_2647313 : Nat := 453114670632035369804245

theorem tailTrace_2647313 : CollatzResearch.WordTrace tailWord_2647313 prefixEnd_2647313 453114670632035369804245 := by
  unfold tailWord_2647313
  simp only [CollatzResearch.WordTrace]
  refine ⟨96555437458244600909994593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64370291638829733939996395 96555437458244600909994593)
  ·
    refine ⟨72416578093683450682495945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96555437458244600909994593 72416578093683450682495945)
    ·
      refine ⟨54312433570262588011871959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72416578093683450682495945 54312433570262588011871959)
      ·
        refine ⟨81468650355393882017807939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54312433570262588011871959 81468650355393882017807939)
        ·
          refine ⟨122202975533090823026711909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81468650355393882017807939 122202975533090823026711909)
          ·
            refine ⟨22913057912454529317508483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122202975533090823026711909 22913057912454529317508483)
            ·
              refine ⟨34369586868681793976262725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22913057912454529317508483 34369586868681793976262725)
              ·
                refine ⟨6444297537877836370549261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34369586868681793976262725 6444297537877836370549261)
                ·
                  refine ⟨2416611576704188638955973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6444297537877836370549261 2416611576704188638955973)
                  ·
                    refine ⟨453114670632035369804245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2416611576704188638955973 453114670632035369804245)
                    ·
                      rfl

theorem cell23_2647313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_2647313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647313 prefixEnd_2647313 := by exact prefixLift 2647313
  have htrace : WordTrace (prefixWord ++ tailWord_2647313) baseStart_2647313 baseEnd_2647313 := by
    simpa [prefixWord, tailWord_2647313, baseEnd_2647313] using wordTrace_append hprefix tailTrace_2647313
  have hstable : (prefixWord ++ tailWord_2647313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647313).length < 2 ^ (prefixWord ++ tailWord_2647313).sum := by decide
  have hdescent : baseEnd_2647313 < baseStart_2647313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647323 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 3]
def baseStart_2647323 : Nat := 118140960795 + 2647323 * 2 ^ 59
def prefixEnd_2647323 : Nat := 4983230072969 + 3 ^ 40 * 2647323 * 2
def baseEnd_2647323 : Nat := 1359349146702651070287689

theorem tailTrace_2647323 : CollatzResearch.WordTrace tailWord_2647323 prefixEnd_2647323 1359349146702651070287689 := by
  unfold tailWord_2647323
  simp only [CollatzResearch.WordTrace]
  refine ⟨96555802188208372617858623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64370534792138915078572415 96555802188208372617858623)
  ·
    refine ⟨144833703282312558926787935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96555802188208372617858623 144833703282312558926787935)
    ·
      refine ⟨217250554923468838390181903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144833703282312558926787935 217250554923468838390181903)
      ·
        refine ⟨325875832385203257585272855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217250554923468838390181903 325875832385203257585272855)
        ·
          refine ⟨488813748577804886377909283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325875832385203257585272855 488813748577804886377909283)
          ·
            refine ⟨733220622866707329566863925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488813748577804886377909283 733220622866707329566863925)
            ·
              refine ⟨68739433393753812146893493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 733220622866707329566863925 68739433393753812146893493)
              ·
                refine ⟨6444321880664419888771265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68739433393753812146893493 6444321880664419888771265)
                ·
                  refine ⟨4833241410498314916578449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6444321880664419888771265 4833241410498314916578449)
                  ·
                    refine ⟨3624931057873736187433837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4833241410498314916578449 3624931057873736187433837)
                    ·
                      refine ⟨1359349146702651070287689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3624931057873736187433837 1359349146702651070287689)
                      ·
                        rfl

theorem cell23_2647323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 3].length) (baseStart_2647323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647323 prefixEnd_2647323 := by exact prefixLift 2647323
  have htrace : WordTrace (prefixWord ++ tailWord_2647323) baseStart_2647323 baseEnd_2647323 := by
    simpa [prefixWord, tailWord_2647323, baseEnd_2647323] using wordTrace_append hprefix tailTrace_2647323
  have hstable : (prefixWord ++ tailWord_2647323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647323).length < 2 ^ (prefixWord ++ tailWord_2647323).sum := by decide
  have hdescent : baseEnd_2647323 < baseStart_2647323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647370 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_2647370 : Nat := 118140960795 + 2647370 * 2 ^ 59
def prefixEnd_2647370 : Nat := 4983230072969 + 3 ^ 40 * 2647370 * 2
def baseEnd_2647370 : Nat := 1359373280293412386399973

theorem tailTrace_2647370 : CollatzResearch.WordTrace tailWord_2647370 prefixEnd_2647370 1359373280293412386399973 := by
  unfold tailWord_2647370
  simp only [CollatzResearch.WordTrace]
  refine ⟨24139379104759524911204891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64371677612692066429879709 24139379104759524911204891)
  ·
    refine ⟨36209068657139287366807337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24139379104759524911204891 36209068657139287366807337)
    ·
      refine ⟨27156801492854465525105503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36209068657139287366807337 27156801492854465525105503)
      ·
        refine ⟨40735202239281698287658255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27156801492854465525105503 40735202239281698287658255)
        ·
          refine ⟨61102803358922547431487383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40735202239281698287658255 61102803358922547431487383)
          ·
            refine ⟨91654205038383821147231075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61102803358922547431487383 91654205038383821147231075)
            ·
              refine ⟨137481307557575731720846613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91654205038383821147231075 137481307557575731720846613)
              ·
                refine ⟨6444436291761362424414685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137481307557575731720846613 6444436291761362424414685)
                ·
                  refine ⟨2416663609410510909155507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6444436291761362424414685 2416663609410510909155507)
                  ·
                    refine ⟨3624995414115766363733261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2416663609410510909155507 3624995414115766363733261)
                    ·
                      refine ⟨1359373280293412386399973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3624995414115766363733261 1359373280293412386399973)
                      ·
                        rfl

theorem cell23_2647370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_2647370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647370 prefixEnd_2647370 := by exact prefixLift 2647370
  have htrace : WordTrace (prefixWord ++ tailWord_2647370) baseStart_2647370 baseEnd_2647370 := by
    simpa [prefixWord, tailWord_2647370, baseEnd_2647370] using wordTrace_append hprefix tailTrace_2647370
  have hstable : (prefixWord ++ tailWord_2647370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647370).length < 2 ^ (prefixWord ++ tailWord_2647370).sum := by decide
  have hdescent : baseEnd_2647370 < baseStart_2647370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647404 : List Nat := [2, 2, 1, 1, 5, 2, 1, 4, 1, 1, 3]
def baseStart_2647404 : Nat := 118140960795 + 2647404 * 2 ^ 59
def prefixEnd_2647404 : Nat := 4983230072969 + 3 ^ 40 * 2647404 * 2
def baseEnd_2647404 : Nat := 1359390738635665253374817

theorem tailTrace_2647404 : CollatzResearch.WordTrace tailWord_2647404 prefixEnd_2647404 1359390738635665253374817 := by
  unfold tailWord_2647404
  simp only [CollatzResearch.WordTrace]
  refine ⟨48279378250457461725778633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64372504333943282301038177 48279378250457461725778633)
  ·
    refine ⟨36209533687843096294333975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48279378250457461725778633 36209533687843096294333975)
    ·
      refine ⟨54314300531764644441500963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36209533687843096294333975 54314300531764644441500963)
      ·
        refine ⟨81471450797646966662251445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54314300531764644441500963 81471450797646966662251445)
        ·
          refine ⟨7637948512279403124586073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81471450797646966662251445 7637948512279403124586073)
          ·
            refine ⟨5728461384209552343439555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7637948512279403124586073 5728461384209552343439555)
            ·
              refine ⟨8592692076314328515159333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5728461384209552343439555 8592692076314328515159333)
              ·
                refine ⟨1611129764308936596592375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8592692076314328515159333 1611129764308936596592375)
                ·
                  refine ⟨2416694646463404894888563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611129764308936596592375 2416694646463404894888563)
                  ·
                    refine ⟨3625041969695107342332845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2416694646463404894888563 3625041969695107342332845)
                    ·
                      refine ⟨1359390738635665253374817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3625041969695107342332845 1359390738635665253374817)
                      ·
                        rfl

theorem cell23_2647404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_2647404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647404 prefixEnd_2647404 := by exact prefixLift 2647404
  have htrace : WordTrace (prefixWord ++ tailWord_2647404) baseStart_2647404 baseEnd_2647404 := by
    simpa [prefixWord, tailWord_2647404, baseEnd_2647404] using wordTrace_append hprefix tailTrace_2647404
  have hstable : (prefixWord ++ tailWord_2647404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647404).length < 2 ^ (prefixWord ++ tailWord_2647404).sum := by decide
  have hdescent : baseEnd_2647404 < baseStart_2647404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647420 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_2647420 : Nat := 118140960795 + 2647420 * 2 ^ 59
def prefixEnd_2647420 : Nat := 4983230072969 + 3 ^ 40 * 2647420 * 2
def baseEnd_2647420 : Nat := 453132984775379063591581

theorem tailTrace_2647420 : CollatzResearch.WordTrace tailWord_2647420 prefixEnd_2647420 453132984775379063591581 := by
  unfold tailWord_2647420
  simp only [CollatzResearch.WordTrace]
  refine ⟨48279670034428479092069857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64372893379237972122759809 48279670034428479092069857)
  ·
    refine ⟨36209752525821359319052393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48279670034428479092069857 36209752525821359319052393)
    ·
      refine ⟨27157314394366019489289295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36209752525821359319052393 27157314394366019489289295)
      ·
        refine ⟨40735971591549029233933943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27157314394366019489289295 40735971591549029233933943)
        ·
          refine ⟨61103957387323543850900915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40735971591549029233933943 61103957387323543850900915)
          ·
            refine ⟨91655936080985315776351373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61103957387323543850900915 91655936080985315776351373)
            ·
              refine ⟨34370976030369493416131765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91655936080985315776351373 34370976030369493416131765)
              ·
                refine ⟨3222279002847140007762353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34370976030369493416131765 3222279002847140007762353)
                ·
                  refine ⟨2416709252135355005821765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3222279002847140007762353 2416709252135355005821765)
                  ·
                    refine ⟨453132984775379063591581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2416709252135355005821765 453132984775379063591581)
                    ·
                      rfl

theorem cell23_2647420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_2647420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647420 prefixEnd_2647420 := by exact prefixLift 2647420
  have htrace : WordTrace (prefixWord ++ tailWord_2647420) baseStart_2647420 baseEnd_2647420 := by
    simpa [prefixWord, tailWord_2647420, baseEnd_2647420] using wordTrace_append hprefix tailTrace_2647420
  have hstable : (prefixWord ++ tailWord_2647420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647420).length < 2 ^ (prefixWord ++ tailWord_2647420).sum := by decide
  have hdescent : baseEnd_2647420 < baseStart_2647420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647427 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 5, 2, 2]
def baseStart_2647427 : Nat := 118140960795 + 2647427 * 2 ^ 59
def prefixEnd_2647427 : Nat := 4983230072969 + 3 ^ 40 * 2647427 * 2
def baseEnd_2647427 : Nat := 1359402548690718663387211

theorem tailTrace_2647427 : CollatzResearch.WordTrace tailWord_2647427 prefixEnd_2647427 1359402548690718663387211 := by
  unfold tailWord_2647427
  simp only [CollatzResearch.WordTrace]
  refine ⟨96559595379831598379644535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64373063586554398919763023 96559595379831598379644535)
  ·
    refine ⟨144839393069747397569466803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96559595379831598379644535 144839393069747397569466803)
    ·
      refine ⟨217259089604621096354200205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144839393069747397569466803 217259089604621096354200205)
      ·
        refine ⟨81472158601732911132825077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217259089604621096354200205 81472158601732911132825077)
        ·
          refine ⟨7638014868912460418702351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81472158601732911132825077 7638014868912460418702351)
          ·
            refine ⟨11457022303368690628053527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7638014868912460418702351 11457022303368690628053527)
            ·
              refine ⟨17185533455053035942080291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11457022303368690628053527 17185533455053035942080291)
              ·
                refine ⟨25778300182579553913120437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17185533455053035942080291 25778300182579553913120437)
                ·
                  refine ⟨2416715642116833179355041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25778300182579553913120437 2416715642116833179355041)
                  ·
                    refine ⟨1812536731587624884516281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2416715642116833179355041 1812536731587624884516281)
                    ·
                      refine ⟨1359402548690718663387211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812536731587624884516281 1359402548690718663387211)
                      ·
                        rfl

theorem cell23_2647427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_2647427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647427 prefixEnd_2647427 := by exact prefixLift 2647427
  have htrace : WordTrace (prefixWord ++ tailWord_2647427) baseStart_2647427 baseEnd_2647427 := by
    simpa [prefixWord, tailWord_2647427, baseEnd_2647427] using wordTrace_append hprefix tailTrace_2647427
  have hstable : (prefixWord ++ tailWord_2647427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647427).length < 2 ^ (prefixWord ++ tailWord_2647427).sum := by decide
  have hdescent : baseEnd_2647427 < baseStart_2647427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647444 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_2647444 : Nat := 118140960795 + 2647444 * 2 ^ 59
def prefixEnd_2647444 : Nat := 4983230072969 + 3 ^ 40 * 2647444 * 2
def baseEnd_2647444 : Nat := 1359411277861845096874633

theorem tailTrace_2647444 : CollatzResearch.WordTrace tailWord_2647444 prefixEnd_2647444 1359411277861845096874633 := by
  unfold tailWord_2647444
  simp only [CollatzResearch.WordTrace]
  refine ⟨48280107710385005141506693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64373476947180006855342257 48280107710385005141506693)
  ·
    refine ⟨9052520195697188464032505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48280107710385005141506693 9052520195697188464032505)
    ·
      refine ⟨6789390146772891348024379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9052520195697188464032505 6789390146772891348024379)
      ·
        refine ⟨10184085220159337022036569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789390146772891348024379 10184085220159337022036569)
        ·
          refine ⟨7638063915119502766527427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10184085220159337022036569 7638063915119502766527427)
          ·
            refine ⟨11457095872679254149791141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7638063915119502766527427 11457095872679254149791141)
            ·
              refine ⟨2148205476127360153085839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11457095872679254149791141 2148205476127360153085839)
              ·
                refine ⟨3222308214191040229628759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148205476127360153085839 3222308214191040229628759)
                ·
                  refine ⟨4833462321286560344443139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222308214191040229628759 4833462321286560344443139)
                  ·
                    refine ⟨7250193481929840516664709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4833462321286560344443139 7250193481929840516664709)
                    ·
                      refine ⟨1359411277861845096874633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7250193481929840516664709 1359411277861845096874633)
                      ·
                        rfl

theorem cell23_2647444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_2647444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647444 prefixEnd_2647444 := by exact prefixLift 2647444
  have htrace : WordTrace (prefixWord ++ tailWord_2647444) baseStart_2647444 baseEnd_2647444 := by
    simpa [prefixWord, tailWord_2647444, baseEnd_2647444] using wordTrace_append hprefix tailTrace_2647444
  have hstable : (prefixWord ++ tailWord_2647444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647444).length < 2 ^ (prefixWord ++ tailWord_2647444).sum := by decide
  have hdescent : baseEnd_2647444 < baseStart_2647444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647454 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2647454 : Nat := 118140960795 + 2647454 * 2 ^ 59
def prefixEnd_2647454 : Nat := 4983230072969 + 3 ^ 40 * 2647454 * 2
def baseEnd_2647454 : Nat := 453138804222796685916529

theorem tailTrace_2647454 : CollatzResearch.WordTrace tailWord_2647454 prefixEnd_2647454 453138804222796685916529 := by
  unfold tailWord_2647454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12070072518841722748859677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64373720100489187993918277 12070072518841722748859677)
  ·
    refine ⟨4526277194565646030822379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12070072518841722748859677 4526277194565646030822379)
    ·
      refine ⟨6789415791848469046233569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4526277194565646030822379 6789415791848469046233569)
      ·
        refine ⟨5092061843886351784675177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6789415791848469046233569 5092061843886351784675177)
        ·
          refine ⟨3819046382914763838506383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5092061843886351784675177 3819046382914763838506383)
          ·
            refine ⟨5728569574372145757759575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819046382914763838506383 5728569574372145757759575)
            ·
              refine ⟨8592854361558218636639363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5728569574372145757759575 8592854361558218636639363)
              ·
                refine ⟨12889281542337327954959045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8592854361558218636639363 12889281542337327954959045)
                ·
                  refine ⟨2416740289188248991554821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12889281542337327954959045 2416740289188248991554821)
                  ·
                    refine ⟨453138804222796685916529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2416740289188248991554821 453138804222796685916529)
                    ·
                      rfl

theorem cell23_2647454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2647454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647454 prefixEnd_2647454 := by exact prefixLift 2647454
  have htrace : WordTrace (prefixWord ++ tailWord_2647454) baseStart_2647454 baseEnd_2647454 := by
    simpa [prefixWord, tailWord_2647454, baseEnd_2647454] using wordTrace_append hprefix tailTrace_2647454
  have hstable : (prefixWord ++ tailWord_2647454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647454).length < 2 ^ (prefixWord ++ tailWord_2647454).sum := by decide
  have hdescent : baseEnd_2647454 < baseStart_2647454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647477 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2647477 : Nat := 118140960795 + 2647477 * 2 ^ 59
def prefixEnd_2647477 : Nat := 4983230072969 + 3 ^ 40 * 2647477 * 2
def baseEnd_2647477 : Nat := 1359428222723443467761981

theorem tailTrace_2647477 : CollatzResearch.WordTrace tailWord_2647477 prefixEnd_2647477 1359428222723443467761981 := by
  unfold tailWord_2647477
  simp only [CollatzResearch.WordTrace]
  refine ⟨96561419029650456918964685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64374279353100304612643123 96561419029650456918964685)
  ·
    refine ⟨36210532136118921344611757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96561419029650456918964685 36210532136118921344611757)
    ·
      refine ⟨13578949551044595504229409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36210532136118921344611757 13578949551044595504229409)
      ·
        refine ⟨10184212163283446628172057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13578949551044595504229409 10184212163283446628172057)
        ·
          refine ⟨7638159122462584971129043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10184212163283446628172057 7638159122462584971129043)
          ·
            refine ⟨11457238683693877456693565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7638159122462584971129043 11457238683693877456693565)
            ·
              refine ⟨4296464506385204046260087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11457238683693877456693565 4296464506385204046260087)
              ·
                refine ⟨6444696759577806069390131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296464506385204046260087 6444696759577806069390131)
                ·
                  refine ⟨9667045139366709104085197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6444696759577806069390131 9667045139366709104085197)
                  ·
                    refine ⟨3625141927262515914031949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9667045139366709104085197 3625141927262515914031949)
                    ·
                      refine ⟨1359428222723443467761981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3625141927262515914031949 1359428222723443467761981)
                      ·
                        rfl

theorem cell23_2647477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2647477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647477 prefixEnd_2647477 := by exact prefixLift 2647477
  have htrace : WordTrace (prefixWord ++ tailWord_2647477) baseStart_2647477 baseEnd_2647477 := by
    simpa [prefixWord, tailWord_2647477, baseEnd_2647477] using wordTrace_append hprefix tailTrace_2647477
  have hstable : (prefixWord ++ tailWord_2647477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647477).length < 2 ^ (prefixWord ++ tailWord_2647477).sum := by decide
  have hdescent : baseEnd_2647477 < baseStart_2647477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647484 : List Nat := [2, 2, 2, 4, 3, 1, 2, 7]
def baseStart_2647484 : Nat := 118140960795 + 2647484 * 2 ^ 59
def prefixEnd_2647484 : Nat := 4983230072969 + 3 ^ 40 * 2647484 * 2
def baseEnd_2647484 : Nat := 50349326558815738532387

theorem tailTrace_2647484 : CollatzResearch.WordTrace tailWord_2647484 prefixEnd_2647484 50349326558815738532387 := by
  unfold tailWord_2647484
  simp only [CollatzResearch.WordTrace]
  refine ⟨48280837170312548557234753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64374449560416731409646337 48280837170312548557234753)
  ·
    refine ⟨36210627877734411417926065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48280837170312548557234753 36210627877734411417926065)
    ·
      refine ⟨27157970908300808563444549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36210627877734411417926065 27157970908300808563444549)
      ·
        refine ⟨5092119545306401605645853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27157970908300808563444549 5092119545306401605645853)
        ·
          refine ⟨1909544829489900602117195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5092119545306401605645853 1909544829489900602117195)
          ·
            refine ⟨2864317244234850903175793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909544829489900602117195 2864317244234850903175793)
            ·
              refine ⟨2148237933176138177381845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2864317244234850903175793 2148237933176138177381845)
              ·
                refine ⟨50349326558815738532387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2148237933176138177381845 50349326558815738532387)
                ·
                  rfl

theorem cell23_2647484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 7].length) (baseStart_2647484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647484 prefixEnd_2647484 := by exact prefixLift 2647484
  have htrace : WordTrace (prefixWord ++ tailWord_2647484) baseStart_2647484 baseEnd_2647484 := by
    simpa [prefixWord, tailWord_2647484, baseEnd_2647484] using wordTrace_append hprefix tailTrace_2647484
  have hstable : (prefixWord ++ tailWord_2647484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647484).length < 2 ^ (prefixWord ++ tailWord_2647484).sum := by decide
  have hdescent : baseEnd_2647484 < baseStart_2647484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647503 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_2647503 : Nat := 118140960795 + 2647503 * 2 ^ 59
def prefixEnd_2647503 : Nat := 4983230072969 + 3 ^ 40 * 2647503 * 2
def baseEnd_2647503 : Nat := 1359441573220460366036861

theorem tailTrace_2647503 : CollatzResearch.WordTrace tailWord_2647503 prefixEnd_2647503 1359441573220460366036861 := by
  unfold tailWord_2647503
  simp only [CollatzResearch.WordTrace]
  refine ⟨96562367327556263359411163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64374911551704175572940775 96562367327556263359411163)
  ·
    refine ⟨144843550991334395039116745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96562367327556263359411163 144843550991334395039116745)
    ·
      refine ⟨108632663243500796279337559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144843550991334395039116745 108632663243500796279337559)
      ·
        refine ⟨162948994865251194419006339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108632663243500796279337559 162948994865251194419006339)
        ·
          refine ⟨244423492297876791628509509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162948994865251194419006339 244423492297876791628509509)
          ·
            refine ⟨45829404805851898430345533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 244423492297876791628509509 45829404805851898430345533)
            ·
              refine ⟨17186026802194461911379575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45829404805851898430345533 17186026802194461911379575)
              ·
                refine ⟨25779040203291692867069363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17186026802194461911379575 25779040203291692867069363)
                ·
                  refine ⟨38668560304937539300604045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25779040203291692867069363 38668560304937539300604045)
                  ·
                    refine ⟨14500710114351577237726517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38668560304937539300604045 14500710114351577237726517)
                    ·
                      refine ⟨1359441573220460366036861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14500710114351577237726517 1359441573220460366036861)
                      ·
                        rfl

theorem cell23_2647503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_2647503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647503 prefixEnd_2647503 := by exact prefixLift 2647503
  have htrace : WordTrace (prefixWord ++ tailWord_2647503) baseStart_2647503 baseEnd_2647503 := by
    simpa [prefixWord, tailWord_2647503, baseEnd_2647503] using wordTrace_append hprefix tailTrace_2647503
  have hstable : (prefixWord ++ tailWord_2647503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647503).length < 2 ^ (prefixWord ++ tailWord_2647503).sum := by decide
  have hdescent : baseEnd_2647503 < baseStart_2647503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647580 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2647580 : Nat := 118140960795 + 2647580 * 2 ^ 59
def prefixEnd_2647580 : Nat := 4983230072969 + 3 ^ 40 * 2647580 * 2
def baseEnd_2647580 : Nat := 1359481111230856564774007

theorem tailTrace_2647580 : CollatzResearch.WordTrace tailWord_2647580 prefixEnd_2647580 1359481111230856564774007 := by
  unfold tailWord_2647580
  simp only [CollatzResearch.WordTrace]
  refine ⟨48282587874138652754982097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64376783832184870339976129 48282587874138652754982097)
  ·
    refine ⟨36211940905603989566236573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48282587874138652754982097 36211940905603989566236573)
    ·
      refine ⟨13579477839601496087338715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36211940905603989566236573 13579477839601496087338715)
      ·
        refine ⟨20369216759402244131008073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13579477839601496087338715 20369216759402244131008073)
        ·
          refine ⟨15276912569551683098256055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20369216759402244131008073 15276912569551683098256055)
          ·
            refine ⟨22915368854327524647384083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15276912569551683098256055 22915368854327524647384083)
            ·
              refine ⟨34373053281491286971076125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22915368854327524647384083 34373053281491286971076125)
              ·
                refine ⟨12889894980559232614153547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34373053281491286971076125 12889894980559232614153547)
                ·
                  refine ⟨19334842470838848921230321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12889894980559232614153547 19334842470838848921230321)
                  ·
                    refine ⟨14501131853129136690922741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19334842470838848921230321 14501131853129136690922741)
                    ·
                      refine ⟨1359481111230856564774007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14501131853129136690922741 1359481111230856564774007)
                      ·
                        rfl

theorem cell23_2647580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2647580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647580 prefixEnd_2647580 := by exact prefixLift 2647580
  have htrace : WordTrace (prefixWord ++ tailWord_2647580) baseStart_2647580 baseEnd_2647580 := by
    simpa [prefixWord, tailWord_2647580, baseEnd_2647580] using wordTrace_append hprefix tailTrace_2647580
  have hstable : (prefixWord ++ tailWord_2647580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647580).length < 2 ^ (prefixWord ++ tailWord_2647580).sum := by decide
  have hdescent : baseEnd_2647580 < baseStart_2647580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647607 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_2647607 : Nat := 118140960795 + 2647607 * 2 ^ 59
def prefixEnd_2647607 : Nat := 4983230072969 + 3 ^ 40 * 2647607 * 2
def baseEnd_2647607 : Nat := 1359494975208527959136383

theorem tailTrace_2647607 : CollatzResearch.WordTrace tailWord_2647607 prefixEnd_2647607 1359494975208527959136383 := by
  unfold tailWord_2647607
  simp only [CollatzResearch.WordTrace]
  refine ⟨96566160519179489121197075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64377440346119659414131383 96566160519179489121197075)
  ·
    refine ⟨144849240778769233681795613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96566160519179489121197075 144849240778769233681795613)
    ·
      refine ⟨54318465292038462630673355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144849240778769233681795613 54318465292038462630673355)
      ·
        refine ⟨81477697938057693946010033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54318465292038462630673355 81477697938057693946010033)
        ·
          refine ⟨61108273453543270459507525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81477697938057693946010033 61108273453543270459507525)
          ·
            refine ⟨11457801272539363211157661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61108273453543270459507525 11457801272539363211157661)
            ·
              refine ⟨4296675477202261204184123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11457801272539363211157661 4296675477202261204184123)
              ·
                refine ⟨6445013215803391806276185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296675477202261204184123 6445013215803391806276185)
                ·
                  refine ⟨4833759911852543854707139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6445013215803391806276185 4833759911852543854707139)
                  ·
                    refine ⟨7250639867778815782060709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4833759911852543854707139 7250639867778815782060709)
                    ·
                      refine ⟨1359494975208527959136383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7250639867778815782060709 1359494975208527959136383)
                      ·
                        rfl

theorem cell23_2647607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_2647607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647607 prefixEnd_2647607 := by exact prefixLift 2647607
  have htrace : WordTrace (prefixWord ++ tailWord_2647607) baseStart_2647607 baseEnd_2647607 := by
    simpa [prefixWord, tailWord_2647607, baseEnd_2647607] using wordTrace_append hprefix tailTrace_2647607
  have hstable : (prefixWord ++ tailWord_2647607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647607).length < 2 ^ (prefixWord ++ tailWord_2647607).sum := by decide
  have hdescent : baseEnd_2647607 < baseStart_2647607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647617 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2647617 : Nat := 118140960795 + 2647617 * 2 ^ 59
def prefixEnd_2647617 : Nat := 4983230072969 + 3 ^ 40 * 2647617 * 2
def baseEnd_2647617 : Nat := 453166703338357640003779

theorem tailTrace_2647617 : CollatzResearch.WordTrace tailWord_2647617 prefixEnd_2647617 453166703338357640003779 := by
  unfold tailWord_2647617
  simp only [CollatzResearch.WordTrace]
  refine ⟨96566525249143260829061105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64377683499428840552707403 96566525249143260829061105)
  ·
    refine ⟨72424893936857445621795829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96566525249143260829061105 72424893936857445621795829)
    ·
      refine ⟨6789833806580385527043359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72424893936857445621795829 6789833806580385527043359)
      ·
        refine ⟨10184750709870578290565039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6789833806580385527043359 10184750709870578290565039)
        ·
          refine ⟨15277126064805867435847559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10184750709870578290565039 15277126064805867435847559)
          ·
            refine ⟨22915689097208801153771339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15277126064805867435847559 22915689097208801153771339)
            ·
              refine ⟨34373533645813201730657009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22915689097208801153771339 34373533645813201730657009)
              ·
                refine ⟨25780150234359901297992757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34373533645813201730657009 25780150234359901297992757)
                ·
                  refine ⟨2416889084471240746686821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25780150234359901297992757 2416889084471240746686821)
                  ·
                    refine ⟨453166703338357640003779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2416889084471240746686821 453166703338357640003779)
                    ·
                      rfl

theorem cell23_2647617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2647617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647617 prefixEnd_2647617 := by exact prefixLift 2647617
  have htrace : WordTrace (prefixWord ++ tailWord_2647617) baseStart_2647617 baseEnd_2647617 := by
    simpa [prefixWord, tailWord_2647617, baseEnd_2647617] using wordTrace_append hprefix tailTrace_2647617
  have hstable : (prefixWord ++ tailWord_2647617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647617).length < 2 ^ (prefixWord ++ tailWord_2647617).sum := by decide
  have hdescent : baseEnd_2647617 < baseStart_2647617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647634 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_2647634 : Nat := 118140960795 + 2647634 * 2 ^ 59
def prefixEnd_2647634 : Nat := 4983230072969 + 3 ^ 40 * 2647634 * 2
def baseEnd_2647634 : Nat := 453169613062066451166253

theorem tailTrace_2647634 : CollatzResearch.WordTrace tailWord_2647634 prefixEnd_2647634 453169613062066451166253 := by
  unfold tailWord_2647634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24141786322520418183107489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64378096860054448488286637 24141786322520418183107489)
  ·
    refine ⟨18106339741890313637330617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24141786322520418183107489 18106339741890313637330617)
    ·
      refine ⟨13579754806417735227997963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18106339741890313637330617 13579754806417735227997963)
      ·
        refine ⟨20369632209626602841996945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13579754806417735227997963 20369632209626602841996945)
        ·
          refine ⟨15277224157219952131497709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20369632209626602841996945 15277224157219952131497709)
          ·
            refine ⟨5728959058957482049311641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15277224157219952131497709 5728959058957482049311641)
            ·
              refine ⟨4296719294218111536983731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728959058957482049311641 4296719294218111536983731)
              ·
                refine ⟨6445078941327167305475597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296719294218111536983731 6445078941327167305475597)
                ·
                  refine ⟨2416904602997687739553349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6445078941327167305475597 2416904602997687739553349)
                  ·
                    refine ⟨453169613062066451166253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2416904602997687739553349 453169613062066451166253)
                    ·
                      rfl

theorem cell23_2647634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_2647634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647634 prefixEnd_2647634 := by exact prefixLift 2647634
  have htrace : WordTrace (prefixWord ++ tailWord_2647634) baseStart_2647634 baseEnd_2647634 := by
    simpa [prefixWord, tailWord_2647634, baseEnd_2647634] using wordTrace_append hprefix tailTrace_2647634
  have hstable : (prefixWord ++ tailWord_2647634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647634).length < 2 ^ (prefixWord ++ tailWord_2647634).sum := by decide
  have hdescent : baseEnd_2647634 < baseStart_2647634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647697 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 2, 6, 2]
def baseStart_2647697 : Nat := 118140960795 + 2647697 * 2 ^ 59
def prefixEnd_2647697 : Nat := 4983230072969 + 3 ^ 40 * 2647697 * 2
def baseEnd_2647697 : Nat := 1359541188467432607010969

theorem tailTrace_2647697 : CollatzResearch.WordTrace tailWord_2647697 prefixEnd_2647697 1359541188467432607010969 := by
  unfold tailWord_2647697
  simp only [CollatzResearch.WordTrace]
  refine ⟨96569443088853434491973345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64379628725902289661315563 96569443088853434491973345)
  ·
    refine ⟨72427082316640075868980009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96569443088853434491973345 72427082316640075868980009)
    ·
      refine ⟨54320311737480056901735007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72427082316640075868980009 54320311737480056901735007)
      ·
        refine ⟨81480467606220085352602511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54320311737480056901735007 81480467606220085352602511)
        ·
          refine ⟨122220701409330128028903767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81480467606220085352602511 122220701409330128028903767)
          ·
            refine ⟨183331052113995192043355651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122220701409330128028903767 183331052113995192043355651)
            ·
              refine ⟨274996578170992788065033477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183331052113995192043355651 274996578170992788065033477)
              ·
                refine ⟨51561858407061147762193777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274996578170992788065033477 51561858407061147762193777)
                ·
                  refine ⟨38671393805295860821645333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51561858407061147762193777 38671393805295860821645333)
                  ·
                    refine ⟨1812721584623243476014625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38671393805295860821645333 1812721584623243476014625)
                    ·
                      refine ⟨1359541188467432607010969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812721584623243476014625 1359541188467432607010969)
                      ·
                        rfl

theorem cell23_2647697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_2647697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647697 prefixEnd_2647697 := by exact prefixLift 2647697
  have htrace : WordTrace (prefixWord ++ tailWord_2647697) baseStart_2647697 baseEnd_2647697 := by
    simpa [prefixWord, tailWord_2647697, baseEnd_2647697] using wordTrace_append hprefix tailTrace_2647697
  have hstable : (prefixWord ++ tailWord_2647697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647697).length < 2 ^ (prefixWord ++ tailWord_2647697).sum := by decide
  have hdescent : baseEnd_2647697 < baseStart_2647697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647698 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 6]
def baseStart_2647698 : Nat := 118140960795 + 2647698 * 2 ^ 59
def prefixEnd_2647698 : Nat := 4983230072969 + 3 ^ 40 * 2647698 * 2
def baseEnd_2647698 : Nat := 151060189105343011455385

theorem tailTrace_2647698 : CollatzResearch.WordTrace tailWord_2647698 prefixEnd_2647698 151060189105343011455385 := by
  unfold tailWord_2647698
  simp only [CollatzResearch.WordTrace]
  refine ⟨24142369890462452915689937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64379653041233207775173165 24142369890462452915689937)
  ·
    refine ⟨18106777417846839686767453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24142369890462452915689937 18106777417846839686767453)
    ·
      refine ⟨6790041531692564882537795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18106777417846839686767453 6790041531692564882537795)
      ·
        refine ⟨10185062297538847323806693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6790041531692564882537795 10185062297538847323806693)
        ·
          refine ⟨1909699180788533873213755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10185062297538847323806693 1909699180788533873213755)
          ·
            refine ⟨2864548771182800809820633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909699180788533873213755 2864548771182800809820633)
            ·
              refine ⟨2148411578387100607365475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2864548771182800809820633 2148411578387100607365475)
              ·
                refine ⟨3222617367580650911048213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148411578387100607365475 3222617367580650911048213)
                ·
                  refine ⟨151060189105343011455385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3222617367580650911048213 151060189105343011455385)
                  ·
                    rfl

theorem cell23_2647698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_2647698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647698 prefixEnd_2647698 := by exact prefixLift 2647698
  have htrace : WordTrace (prefixWord ++ tailWord_2647698) baseStart_2647698 baseEnd_2647698 := by
    simpa [prefixWord, tailWord_2647698, baseEnd_2647698] using wordTrace_append hprefix tailTrace_2647698
  have hstable : (prefixWord ++ tailWord_2647698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647698).length < 2 ^ (prefixWord ++ tailWord_2647698).sum := by decide
  have hdescent : baseEnd_2647698 < baseStart_2647698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647727 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_2647727 : Nat := 118140960795 + 2647727 * 2 ^ 59
def prefixEnd_2647727 : Nat := 4983230072969 + 3 ^ 40 * 2647727 * 2
def baseEnd_2647727 : Nat := 1359556592887067489635831

theorem tailTrace_2647727 : CollatzResearch.WordTrace tailWord_2647727 prefixEnd_2647727 1359556592887067489635831 := by
  unfold tailWord_2647727
  simp only [CollatzResearch.WordTrace]
  refine ⟨96570537278744749615565435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64380358185829833077043623 96570537278744749615565435)
  ·
    refine ⟨144855805918117124423348153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96570537278744749615565435 144855805918117124423348153)
    ·
      refine ⟨108641854438587843317511115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144855805918117124423348153 108641854438587843317511115)
      ·
        refine ⟨162962781657881764976266673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108641854438587843317511115 162962781657881764976266673)
        ·
          refine ⟨122222086243411323732200005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162962781657881764976266673 122222086243411323732200005)
          ·
            refine ⟨22916641170639623199787501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122222086243411323732200005 22916641170639623199787501)
            ·
              refine ⟨8593740438989858699920313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22916641170639623199787501 8593740438989858699920313)
              ·
                refine ⟨6445305329242394024940235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8593740438989858699920313 6445305329242394024940235)
                ·
                  refine ⟨9667957993863591037410353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6445305329242394024940235 9667957993863591037410353)
                  ·
                    refine ⟨7250968495397693278057765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9667957993863591037410353 7250968495397693278057765)
                    ·
                      refine ⟨1359556592887067489635831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7250968495397693278057765 1359556592887067489635831)
                      ·
                        rfl

theorem cell23_2647727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_2647727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647727 prefixEnd_2647727 := by exact prefixLift 2647727
  have htrace : WordTrace (prefixWord ++ tailWord_2647727) baseStart_2647727 baseEnd_2647727 := by
    simpa [prefixWord, tailWord_2647727, baseEnd_2647727] using wordTrace_append hprefix tailTrace_2647727
  have hstable : (prefixWord ++ tailWord_2647727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647727).length < 2 ^ (prefixWord ++ tailWord_2647727).sum := by decide
  have hdescent : baseEnd_2647727 < baseStart_2647727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647754 : List Nat := [3, 1, 2, 1, 5, 2, 1, 8]
def baseStart_2647754 : Nat := 118140960795 + 2647754 * 2 ^ 59
def prefixEnd_2647754 : Nat := 4983230072969 + 3 ^ 40 * 2647754 * 2
def baseEnd_2647754 : Nat := 50354461365360699407341

theorem tailTrace_2647754 : CollatzResearch.WordTrace tailWord_2647754 prefixEnd_2647754 50354461365360699407341 := by
  unfold tailWord_2647754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24142880512411733306699579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64381014699764622151198877 24142880512411733306699579)
  ·
    refine ⟨36214320768617599960049369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24142880512411733306699579 36214320768617599960049369)
    ·
      refine ⟨27160740576463199970037027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36214320768617599960049369 27160740576463199970037027)
      ·
        refine ⟨40741110864694799955055541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27160740576463199970037027 40741110864694799955055541)
        ·
          refine ⟨3819479143565137495786457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40741110864694799955055541 3819479143565137495786457)
          ·
            refine ⟨2864609357673853121839843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3819479143565137495786457 2864609357673853121839843)
            ·
              refine ⟨4296914036510779682759765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864609357673853121839843 4296914036510779682759765)
              ·
                refine ⟨50354461365360699407341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4296914036510779682759765 50354461365360699407341)
                ·
                  rfl

theorem cell23_2647754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 8].length) (baseStart_2647754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647754 prefixEnd_2647754 := by exact prefixLift 2647754
  have htrace : WordTrace (prefixWord ++ tailWord_2647754) baseStart_2647754 baseEnd_2647754 := by
    simpa [prefixWord, tailWord_2647754, baseEnd_2647754] using wordTrace_append hprefix tailTrace_2647754
  have hstable : (prefixWord ++ tailWord_2647754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647754).length < 2 ^ (prefixWord ++ tailWord_2647754).sum := by decide
  have hdescent : baseEnd_2647754 < baseStart_2647754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647791 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 1, 3, 2]
def baseStart_2647791 : Nat := 118140960795 + 2647791 * 2 ^ 59
def prefixEnd_2647791 : Nat := 4983230072969 + 3 ^ 40 * 2647791 * 2
def baseEnd_2647791 : Nat := 1359589455648955239235537

theorem tailTrace_2647791 : CollatzResearch.WordTrace tailWord_2647791 prefixEnd_2647791 1359589455648955239235537 := by
  unfold tailWord_2647791
  simp only [CollatzResearch.WordTrace]
  refine ⟨96572871550512888545895227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64381914367008592363930151 96572871550512888545895227)
  ·
    refine ⟨144859307325769332818842841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96572871550512888545895227 144859307325769332818842841)
    ·
      refine ⟨108644480494326999614132131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144859307325769332818842841 108644480494326999614132131)
      ·
        refine ⟨162966720741490499421198197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108644480494326999614132131 162966720741490499421198197)
        ·
          refine ⟨15278130069514734320737331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162966720741490499421198197 15278130069514734320737331)
          ·
            refine ⟨22917195104272101481105997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15278130069514734320737331 22917195104272101481105997)
            ·
              refine ⟨8593948164102038055414749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22917195104272101481105997 8593948164102038055414749)
              ·
                refine ⟨3222730561538264270780531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8593948164102038055414749 3222730561538264270780531)
                ·
                  refine ⟨4834095842307396406170797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222730561538264270780531 4834095842307396406170797)
                  ·
                    refine ⟨1812785940865273652314049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4834095842307396406170797 1812785940865273652314049)
                    ·
                      refine ⟨1359589455648955239235537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812785940865273652314049 1359589455648955239235537)
                      ·
                        rfl

theorem cell23_2647791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 3, 2].length) (baseStart_2647791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647791 prefixEnd_2647791 := by exact prefixLift 2647791
  have htrace : WordTrace (prefixWord ++ tailWord_2647791) baseStart_2647791 baseEnd_2647791 := by
    simpa [prefixWord, tailWord_2647791, baseEnd_2647791] using wordTrace_append hprefix tailTrace_2647791
  have hstable : (prefixWord ++ tailWord_2647791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647791).length < 2 ^ (prefixWord ++ tailWord_2647791).sum := by decide
  have hdescent : baseEnd_2647791 < baseStart_2647791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647798 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2647798 : Nat := 118140960795 + 2647798 * 2 ^ 59
def prefixEnd_2647798 : Nat := 4983230072969 + 3 ^ 40 * 2647798 * 2
def baseEnd_2647798 : Nat := 1359593050013536711848005

theorem tailTrace_2647798 : CollatzResearch.WordTrace tailWord_2647798 prefixEnd_2647798 1359593050013536711848005 := by
  unfold tailWord_2647798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6035820428842970546337503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64382084574325019160933365 6035820428842970546337503)
  ·
    refine ⟨9053730643264455819506255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6035820428842970546337503 9053730643264455819506255)
    ·
      refine ⟨13580595964896683729259383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9053730643264455819506255 13580595964896683729259383)
      ·
        refine ⟨20370893947345025593889075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13580595964896683729259383 20370893947345025593889075)
        ·
          refine ⟨30556340921017538390833613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20370893947345025593889075 30556340921017538390833613)
          ·
            refine ⟨11458627845381576896562605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30556340921017538390833613 11458627845381576896562605)
            ·
              refine ⟨4296985442018091336210977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11458627845381576896562605 4296985442018091336210977)
              ·
                refine ⟨3222739081513568502158233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4296985442018091336210977 3222739081513568502158233)
                ·
                  refine ⟨2417054311135176376618675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3222739081513568502158233 2417054311135176376618675)
                  ·
                    refine ⟨3625581466702764564928013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2417054311135176376618675 3625581466702764564928013)
                    ·
                      refine ⟨1359593050013536711848005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3625581466702764564928013 1359593050013536711848005)
                      ·
                        rfl

theorem cell23_2647798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2647798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647798 prefixEnd_2647798 := by exact prefixLift 2647798
  have htrace : WordTrace (prefixWord ++ tailWord_2647798) baseStart_2647798 baseEnd_2647798 := by
    simpa [prefixWord, tailWord_2647798, baseEnd_2647798] using wordTrace_append hprefix tailTrace_2647798
  have hstable : (prefixWord ++ tailWord_2647798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647798).length < 2 ^ (prefixWord ++ tailWord_2647798).sum := by decide
  have hdescent : baseEnd_2647798 < baseStart_2647798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647807 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 3]
def baseStart_2647807 : Nat := 118140960795 + 2647807 * 2 ^ 59
def prefixEnd_2647807 : Nat := 4983230072969 + 3 ^ 40 * 2647807 * 2
def baseEnd_2647807 : Nat := 1359597671339427176635463

theorem tailTrace_2647807 : CollatzResearch.WordTrace tailWord_2647807 prefixEnd_2647807 1359597671339427176635463 := by
  unfold tailWord_2647807
  simp only [CollatzResearch.WordTrace]
  refine ⟨96573455118454923278477675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64382303412303282185651783 96573455118454923278477675)
  ·
    refine ⟨144860182677682384917716513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96573455118454923278477675 144860182677682384917716513)
    ·
      refine ⟨108645137008261788688287385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144860182677682384917716513 108645137008261788688287385)
      ·
        refine ⟨81483852756196341516215539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108645137008261788688287385 81483852756196341516215539)
        ·
          refine ⟨122225779134294512274323309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81483852756196341516215539 122225779134294512274323309)
          ·
            refine ⟨45834667175360442102871241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122225779134294512274323309 45834667175360442102871241)
            ·
              refine ⟨34376000381520331577153431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45834667175360442102871241 34376000381520331577153431)
              ·
                refine ⟨51564000572280497365730147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34376000381520331577153431 51564000572280497365730147)
                ·
                  refine ⟨77346000858420746048595221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51564000572280497365730147 77346000858420746048595221)
                  ·
                    refine ⟨3625593790238472471027901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77346000858420746048595221 3625593790238472471027901)
                    ·
                      refine ⟨1359597671339427176635463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3625593790238472471027901 1359597671339427176635463)
                      ·
                        rfl

theorem cell23_2647807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_2647807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647807 prefixEnd_2647807 := by exact prefixLift 2647807
  have htrace : WordTrace (prefixWord ++ tailWord_2647807) baseStart_2647807 baseEnd_2647807 := by
    simpa [prefixWord, tailWord_2647807, baseEnd_2647807] using wordTrace_append hprefix tailTrace_2647807
  have hstable : (prefixWord ++ tailWord_2647807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647807).length < 2 ^ (prefixWord ++ tailWord_2647807).sum := by decide
  have hdescent : baseEnd_2647807 < baseStart_2647807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647815 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2647815 : Nat := 118140960795 + 2647815 * 2 ^ 59
def prefixEnd_2647815 : Nat := 4983230072969 + 3 ^ 40 * 2647815 * 2
def baseEnd_2647815 : Nat := 1359601779184663145335427

theorem tailTrace_2647815 : CollatzResearch.WordTrace tailWord_2647815 prefixEnd_2647815 1359601779184663145335427 := by
  unfold tailWord_2647815
  simp only [CollatzResearch.WordTrace]
  refine ⟨96573746902425940644768899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64382497934950627096512599 96573746902425940644768899)
  ·
    refine ⟨144860620353638910967153349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96573746902425940644768899 144860620353638910967153349)
    ·
      refine ⟨27161366316307295806341253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144860620353638910967153349 27161366316307295806341253)
      ·
        refine ⟨5092756184307617963688985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27161366316307295806341253 5092756184307617963688985)
        ·
          refine ⟨3819567138230713472766739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5092756184307617963688985 3819567138230713472766739)
          ·
            refine ⟨5729350707346070209150109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819567138230713472766739 5729350707346070209150109)
            ·
              refine ⟨2148506515254776328431291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5729350707346070209150109 2148506515254776328431291)
              ·
                refine ⟨3222759772882164492646937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148506515254776328431291 3222759772882164492646937)
                ·
                  refine ⟨2417069829661623369485203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3222759772882164492646937 2417069829661623369485203)
                  ·
                    refine ⟨3625604744492435054227805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2417069829661623369485203 3625604744492435054227805)
                    ·
                      refine ⟨1359601779184663145335427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3625604744492435054227805 1359601779184663145335427)
                      ·
                        rfl

theorem cell23_2647815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2647815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647815 prefixEnd_2647815 := by exact prefixLift 2647815
  have htrace : WordTrace (prefixWord ++ tailWord_2647815) baseStart_2647815 baseEnd_2647815 := by
    simpa [prefixWord, tailWord_2647815, baseEnd_2647815] using wordTrace_append hprefix tailTrace_2647815
  have hstable : (prefixWord ++ tailWord_2647815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647815).length < 2 ^ (prefixWord ++ tailWord_2647815).sum := by decide
  have hdescent : baseEnd_2647815 < baseStart_2647815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647861 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 7]
def baseStart_2647861 : Nat := 118140960795 + 2647861 * 2 ^ 59
def prefixEnd_2647861 : Nat := 4983230072969 + 3 ^ 40 * 2647861 * 2
def baseEnd_2647861 : Nat := 151069488810529996151135

theorem tailTrace_2647861 : CollatzResearch.WordTrace tailWord_2647861 prefixEnd_2647861 151069488810529996151135 := by
  unfold tailWord_2647861
  simp only [CollatzResearch.WordTrace]
  refine ⟨96575424660259290500943437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64383616440172860333962291 96575424660259290500943437)
  ·
    refine ⟨36215784247597233937853789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96575424660259290500943437 36215784247597233937853789)
    ·
      refine ⟨13580919092848962726695171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36215784247597233937853789 13580919092848962726695171)
      ·
        refine ⟨20371378639273444090042757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13580919092848962726695171 20371378639273444090042757)
        ·
          refine ⟨3819633494863770766883017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20371378639273444090042757 3819633494863770766883017)
          ·
            refine ⟨2864725121147828075162263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3819633494863770766883017 2864725121147828075162263)
            ·
              refine ⟨4297087681721742112743395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864725121147828075162263 4297087681721742112743395)
              ·
                refine ⟨6445631522582613169115093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297087681721742112743395 6445631522582613169115093)
                ·
                  refine ⟨151069488810529996151135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6445631522582613169115093 151069488810529996151135)
                  ·
                    rfl

theorem cell23_2647861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_2647861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647861 prefixEnd_2647861 := by exact prefixLift 2647861
  have htrace : WordTrace (prefixWord ++ tailWord_2647861) baseStart_2647861 baseEnd_2647861 := by
    simpa [prefixWord, tailWord_2647861, baseEnd_2647861] using wordTrace_append hprefix tailTrace_2647861
  have hstable : (prefixWord ++ tailWord_2647861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647861).length < 2 ^ (prefixWord ++ tailWord_2647861).sum := by decide
  have hdescent : baseEnd_2647861 < baseStart_2647861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647911 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_2647911 : Nat := 118140960795 + 2647911 * 2 ^ 59
def prefixEnd_2647911 : Nat := 4983230072969 + 3 ^ 40 * 2647911 * 2
def baseEnd_2647911 : Nat := 1359651073327494769734985

theorem tailTrace_2647911 : CollatzResearch.WordTrace tailWord_2647911 prefixEnd_2647911 1359651073327494769734985 := by
  unfold tailWord_2647911
  simp only [CollatzResearch.WordTrace]
  refine ⟨96577248310078149040263587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64384832206718766026842391 96577248310078149040263587)
  ·
    refine ⟨144865872465117223560395381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96577248310078149040263587 144865872465117223560395381)
    ·
      refine ⟨13581175543604739708787067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144865872465117223560395381 13581175543604739708787067)
      ·
        refine ⟨20371763315407109563180601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13581175543604739708787067 20371763315407109563180601)
        ·
          refine ⟨15278822486555332172385451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20371763315407109563180601 15278822486555332172385451)
          ·
            refine ⟨22918233729832998258578177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15278822486555332172385451 22918233729832998258578177)
            ·
              refine ⟨17188675297374748693933633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22918233729832998258578177 17188675297374748693933633)
              ·
                refine ⟨12891506473031061520450225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17188675297374748693933633 12891506473031061520450225)
                ·
                  refine ⟨9668629854773296140337669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12891506473031061520450225 9668629854773296140337669)
                  ·
                    refine ⟨1812868097769993026313313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9668629854773296140337669 1812868097769993026313313)
                    ·
                      refine ⟨1359651073327494769734985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812868097769993026313313 1359651073327494769734985)
                      ·
                        rfl

theorem cell23_2647911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_2647911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647911 prefixEnd_2647911 := by exact prefixLift 2647911
  have htrace : WordTrace (prefixWord ++ tailWord_2647911) baseStart_2647911 baseEnd_2647911 := by
    simpa [prefixWord, tailWord_2647911, baseEnd_2647911] using wordTrace_append hprefix tailTrace_2647911
  have hstable : (prefixWord ++ tailWord_2647911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647911).length < 2 ^ (prefixWord ++ tailWord_2647911).sum := by decide
  have hdescent : baseEnd_2647911 < baseStart_2647911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647971 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 4, 3, 2]
def baseStart_2647971 : Nat := 118140960795 + 2647971 * 2 ^ 59
def prefixEnd_2647971 : Nat := 4983230072969 + 3 ^ 40 * 2647971 * 2
def baseEnd_2647971 : Nat := 1359681882166764534984709

theorem tailTrace_2647971 : CollatzResearch.WordTrace tailWord_2647971 prefixEnd_2647971 1359681882166764534984709 := by
  unfold tailWord_2647971
  simp only [CollatzResearch.WordTrace]
  refine ⟨96579436689860779287447767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64386291126573852858298511 96579436689860779287447767)
  ·
    refine ⟨144869155034791168931171651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96579436689860779287447767 144869155034791168931171651)
    ·
      refine ⟨217303732552186753396757477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144869155034791168931171651 217303732552186753396757477)
      ·
        refine ⟨40744449853535016261892027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217303732552186753396757477 40744449853535016261892027)
        ·
          refine ⟨61116674780302524392838041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40744449853535016261892027 61116674780302524392838041)
          ·
            refine ⟨45837506085226893294628531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61116674780302524392838041 45837506085226893294628531)
            ·
              refine ⟨68756259127840339941942797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45837506085226893294628531 68756259127840339941942797)
              ·
                refine ⟨25783597172940127478228549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68756259127840339941942797 25783597172940127478228549)
                ·
                  refine ⟨4834424469926273902167853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25783597172940127478228549 4834424469926273902167853)
                  ·
                    refine ⟨1812909176222352713312945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4834424469926273902167853 1812909176222352713312945)
                    ·
                      refine ⟨1359681882166764534984709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812909176222352713312945 1359681882166764534984709)
                      ·
                        rfl

theorem cell23_2647971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_2647971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647971 prefixEnd_2647971 := by exact prefixLift 2647971
  have htrace : WordTrace (prefixWord ++ tailWord_2647971) baseStart_2647971 baseEnd_2647971 := by
    simpa [prefixWord, tailWord_2647971, baseEnd_2647971] using wordTrace_append hprefix tailTrace_2647971
  have hstable : (prefixWord ++ tailWord_2647971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647971).length < 2 ^ (prefixWord ++ tailWord_2647971).sum := by decide
  have hdescent : baseEnd_2647971 < baseStart_2647971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647994 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_2647994 : Nat := 118140960795 + 2647994 * 2 ^ 59
def prefixEnd_2647994 : Nat := 4983230072969 + 3 ^ 40 * 2647994 * 2
def baseEnd_2647994 : Nat := 453231230740605981665701

theorem tailTrace_2647994 : CollatzResearch.WordTrace tailWord_2647994 prefixEnd_2647994 453231230740605981665701 := by
  unfold tailWord_2647994
  simp only [CollatzResearch.WordTrace]
  refine ⟨24145068892194363553883759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64386850379184969477023357 24145068892194363553883759)
  ·
    refine ⟨36217603338291545330825639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24145068892194363553883759 36217603338291545330825639)
    ·
      refine ⟨54326405007437317996238459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36217603338291545330825639 54326405007437317996238459)
      ·
        refine ⟨81489607511155976994357689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54326405007437317996238459 81489607511155976994357689)
        ·
          refine ⟨61117205633366982745768267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81489607511155976994357689 61117205633366982745768267)
          ·
            refine ⟨91675808450050474118652401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61117205633366982745768267 91675808450050474118652401)
            ·
              refine ⟨68756856337537855588989301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91675808450050474118652401 68756856337537855588989301)
              ·
                refine ⟨6445955281644173961467747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68756856337537855588989301 6445955281644173961467747)
                ·
                  refine ⟨9668932922466260942201621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6445955281644173961467747 9668932922466260942201621)
                  ·
                    refine ⟨453231230740605981665701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9668932922466260942201621 453231230740605981665701)
                    ·
                      rfl

theorem cell23_2647994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_2647994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647994 prefixEnd_2647994 := by exact prefixLift 2647994
  have htrace : WordTrace (prefixWord ++ tailWord_2647994) baseStart_2647994 baseEnd_2647994 := by
    simpa [prefixWord, tailWord_2647994, baseEnd_2647994] using wordTrace_append hprefix tailTrace_2647994
  have hstable : (prefixWord ++ tailWord_2647994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647994).length < 2 ^ (prefixWord ++ tailWord_2647994).sum := by decide
  have hdescent : baseEnd_2647994 < baseStart_2647994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2647998 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2647998 : Nat := 118140960795 + 2647998 * 2 ^ 59
def prefixEnd_2647998 : Nat := 4983230072969 + 3 ^ 40 * 2647998 * 2
def baseEnd_2647998 : Nat := 453231915381478643115695

theorem tailTrace_2647998 : CollatzResearch.WordTrace tailWord_2647998 prefixEnd_2647998 453231915381478643115695 := by
  unfold tailWord_2647998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12072552682595370362335081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64386947640508641932453765 12072552682595370362335081)
  ·
    refine ⟨9054414511946527771751311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12072552682595370362335081 9054414511946527771751311)
    ·
      refine ⟨13581621767919791657626967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9054414511946527771751311 13581621767919791657626967)
      ·
        refine ⟨20372432651879687486440451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13581621767919791657626967 20372432651879687486440451)
        ·
          refine ⟨30558648977819531229660677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20372432651879687486440451 30558648977819531229660677)
          ·
            refine ⟨5729746683341162105561377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30558648977819531229660677 5729746683341162105561377)
            ·
              refine ⟨4297310012505871579171033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5729746683341162105561377 4297310012505871579171033)
              ·
                refine ⟨3222982509379403684378275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297310012505871579171033 3222982509379403684378275)
                ·
                  refine ⟨4834473764069105526567413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222982509379403684378275 4834473764069105526567413)
                  ·
                    refine ⟨453231915381478643115695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4834473764069105526567413 453231915381478643115695)
                    ·
                      rfl

theorem cell23_2647998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2647998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2647998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2647998 prefixEnd_2647998 := by exact prefixLift 2647998
  have htrace : WordTrace (prefixWord ++ tailWord_2647998) baseStart_2647998 baseEnd_2647998 := by
    simpa [prefixWord, tailWord_2647998, baseEnd_2647998] using wordTrace_append hprefix tailTrace_2647998
  have hstable : (prefixWord ++ tailWord_2647998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2647998).length < 2 ^ (prefixWord ++ tailWord_2647998).sum := by decide
  have hdescent : baseEnd_2647998 < baseStart_2647998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2647998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648012 : List Nat := [2, 2, 1, 4, 1, 4, 1, 3, 1, 1, 3]
def baseStart_2648012 : Nat := 118140960795 + 2648012 * 2 ^ 59
def prefixEnd_2648012 : Nat := 4983230072969 + 3 ^ 40 * 2648012 * 2
def baseEnd_2648012 : Nat := 1359702934873598874572021

theorem tailTrace_2648012 : CollatzResearch.WordTrace tailWord_2648012 prefixEnd_2648012 1359702934873598874572021 := by
  unfold tailWord_2648012
  simp only [CollatzResearch.WordTrace]
  refine ⟨48290466041356121644845145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64387288055141495526460193 48290466041356121644845145)
  ·
    refine ⟨36217849531017091233633859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48290466041356121644845145 36217849531017091233633859)
    ·
      refine ⟨54326774296525636850450789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36217849531017091233633859 54326774296525636850450789)
      ·
        refine ⟨10186270180598556909459523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54326774296525636850450789 10186270180598556909459523)
        ·
          refine ⟨15279405270897835364189285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10186270180598556909459523 15279405270897835364189285)
          ·
            refine ⟨2864888488293344130785491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15279405270897835364189285 2864888488293344130785491)
            ·
              refine ⟨4297332732440016196178237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864888488293344130785491 4297332732440016196178237)
              ·
                refine ⟨1611499774665006073566839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4297332732440016196178237 1611499774665006073566839)
                ·
                  refine ⟨2417249661997509110350259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611499774665006073566839 2417249661997509110350259)
                  ·
                    refine ⟨3625874492996263665525389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2417249661997509110350259 3625874492996263665525389)
                    ·
                      refine ⟨1359702934873598874572021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3625874492996263665525389 1359702934873598874572021)
                      ·
                        rfl

theorem cell23_2648012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_2648012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648012 prefixEnd_2648012 := by exact prefixLift 2648012
  have htrace : WordTrace (prefixWord ++ tailWord_2648012) baseStart_2648012 baseEnd_2648012 := by
    simpa [prefixWord, tailWord_2648012, baseEnd_2648012] using wordTrace_append hprefix tailTrace_2648012
  have hstable : (prefixWord ++ tailWord_2648012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648012).length < 2 ^ (prefixWord ++ tailWord_2648012).sum := by decide
  have hdescent : baseEnd_2648012 < baseStart_2648012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648021 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2648021 : Nat := 118140960795 + 2648021 * 2 ^ 59
def prefixEnd_2648021 : Nat := 4983230072969 + 3 ^ 40 * 2648021 * 2
def baseEnd_2648021 : Nat := 1359707556199489339359479

theorem tailTrace_2648021 : CollatzResearch.WordTrace tailWord_2648021 prefixEnd_2648021 1359707556199489339359479 := by
  unfold tailWord_2648021
  simp only [CollatzResearch.WordTrace]
  refine ⟨96581260339679637826767917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64387506893119758551178611 96581260339679637826767917)
  ·
    refine ⟨36217972627379864185037969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96581260339679637826767917 36217972627379864185037969)
    ·
      refine ⟨27163479470534898138778477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36217972627379864185037969 27163479470534898138778477)
      ·
        refine ⟨10186304801450586802041929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27163479470534898138778477 10186304801450586802041929)
        ·
          refine ⟨7639728601087940101531447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10186304801450586802041929 7639728601087940101531447)
          ·
            refine ⟨11459592901631910152297171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7639728601087940101531447 11459592901631910152297171)
            ·
              refine ⟨17189389352447865228445757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11459592901631910152297171 17189389352447865228445757)
              ·
                refine ⟨6446021007167949460667159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17189389352447865228445757 6446021007167949460667159)
                ·
                  refine ⟨9669031510751924191000739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6446021007167949460667159 9669031510751924191000739)
                  ·
                    refine ⟨14503547266127886286501109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9669031510751924191000739 14503547266127886286501109)
                    ·
                      refine ⟨1359707556199489339359479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14503547266127886286501109 1359707556199489339359479)
                      ·
                        rfl

theorem cell23_2648021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2648021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648021 prefixEnd_2648021 := by exact prefixLift 2648021
  have htrace : WordTrace (prefixWord ++ tailWord_2648021) baseStart_2648021 baseEnd_2648021 := by
    simpa [prefixWord, tailWord_2648021, baseEnd_2648021] using wordTrace_append hprefix tailTrace_2648021
  have hstable : (prefixWord ++ tailWord_2648021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648021).length < 2 ^ (prefixWord ++ tailWord_2648021).sum := by decide
  have hdescent : baseEnd_2648021 < baseStart_2648021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648022 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_2648022 : Nat := 118140960795 + 2648022 * 2 ^ 59
def prefixEnd_2648022 : Nat := 4983230072969 + 3 ^ 40 * 2648022 * 2
def baseEnd_2648022 : Nat := 1359708069680143835446975

theorem tailTrace_2648022 : CollatzResearch.WordTrace tailWord_2648022 prefixEnd_2648022 1359708069680143835446975 := by
  unfold tailWord_2648022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6036331050792250937347145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64387531208450676665036213 6036331050792250937347145)
  ·
    refine ⟨4527248288094188203010359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6036331050792250937347145 4527248288094188203010359)
    ·
      refine ⟨6790872432141282304515539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4527248288094188203010359 6790872432141282304515539)
      ·
        refine ⟨10186308648211923456773309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6790872432141282304515539 10186308648211923456773309)
        ·
          refine ⟨3819865743079471296289991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10186308648211923456773309 3819865743079471296289991)
          ·
            refine ⟨5729798614619206944434987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819865743079471296289991 5729798614619206944434987)
            ·
              refine ⟨8594697921928810416652481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5729798614619206944434987 8594697921928810416652481)
              ·
                refine ⟨6446023441446607812489361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8594697921928810416652481 6446023441446607812489361)
                ·
                  refine ⟨4834517581084955859367021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6446023441446607812489361 4834517581084955859367021)
                  ·
                    refine ⟨1812944092906858447262633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4834517581084955859367021 1812944092906858447262633)
                    ·
                      refine ⟨1359708069680143835446975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812944092906858447262633 1359708069680143835446975)
                      ·
                        rfl

theorem cell23_2648022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_2648022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648022 prefixEnd_2648022 := by exact prefixLift 2648022
  have htrace : WordTrace (prefixWord ++ tailWord_2648022) baseStart_2648022 baseEnd_2648022 := by
    simpa [prefixWord, tailWord_2648022, baseEnd_2648022] using wordTrace_append hprefix tailTrace_2648022
  have hstable : (prefixWord ++ tailWord_2648022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648022).length < 2 ^ (prefixWord ++ tailWord_2648022).sum := by decide
  have hdescent : baseEnd_2648022 < baseStart_2648022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648029 : List Nat := [1, 4, 3, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_2648029 : Nat := 118140960795 + 2648029 * 2 ^ 59
def prefixEnd_2648029 : Nat := 4983230072969 + 3 ^ 40 * 2648029 * 2
def baseEnd_2648029 : Nat := 1359711664044725308059443

theorem tailTrace_2648029 : CollatzResearch.WordTrace tailWord_2648029 prefixEnd_2648029 1359711664044725308059443 := by
  unfold tailWord_2648029
  simp only [CollatzResearch.WordTrace]
  refine ⟨96581552123650655193059141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64387701415767103462039427 96581552123650655193059141)
  ·
    refine ⟨18109041023184497848698589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96581552123650655193059141 18109041023184497848698589)
    ·
      refine ⟨6790890383694186693261971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18109041023184497848698589 6790890383694186693261971)
      ·
        refine ⟨10186335575541280039892957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6790890383694186693261971 10186335575541280039892957)
        ·
          refine ⟨3819875840827980014959859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10186335575541280039892957 3819875840827980014959859)
          ·
            refine ⟨5729813761241970022439789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819875840827980014959859 5729813761241970022439789)
            ·
              refine ⟨2148680160465738758414921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5729813761241970022439789 2148680160465738758414921)
              ·
                refine ⟨1611510120349304068811191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2148680160465738758414921 1611510120349304068811191)
                ·
                  refine ⟨2417265180523956103216787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611510120349304068811191 2417265180523956103216787)
                  ·
                    refine ⟨3625897770785934154825181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2417265180523956103216787 3625897770785934154825181)
                    ·
                      refine ⟨1359711664044725308059443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3625897770785934154825181 1359711664044725308059443)
                      ·
                        rfl

theorem cell23_2648029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_2648029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648029 prefixEnd_2648029 := by exact prefixLift 2648029
  have htrace : WordTrace (prefixWord ++ tailWord_2648029) baseStart_2648029 baseEnd_2648029 := by
    simpa [prefixWord, tailWord_2648029, baseEnd_2648029] using wordTrace_append hprefix tailTrace_2648029
  have hstable : (prefixWord ++ tailWord_2648029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648029).length < 2 ^ (prefixWord ++ tailWord_2648029).sum := by decide
  have hdescent : baseEnd_2648029 < baseStart_2648029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648035 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 3, 2, 2]
def baseStart_2648035 : Nat := 118140960795 + 2648035 * 2 ^ 59
def prefixEnd_2648035 : Nat := 4983230072969 + 3 ^ 40 * 2648035 * 2
def baseEnd_2648035 : Nat := 1359714744928652284584415

theorem tailTrace_2648035 : CollatzResearch.WordTrace tailWord_2648035 prefixEnd_2648035 1359714744928652284584415 := by
  unfold tailWord_2648035
  simp only [CollatzResearch.WordTrace]
  refine ⟨96581770961628918217777559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64387847307752612145185039 96581770961628918217777559)
  ·
    refine ⟨144872656442443377326666339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96581770961628918217777559 144872656442443377326666339)
    ·
      refine ⟨217308984663665065989999509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144872656442443377326666339 217308984663665065989999509)
      ·
        refine ⟨10186358656109299968281227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 217308984663665065989999509 10186358656109299968281227)
        ·
          refine ⟨15279537984163949952421841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10186358656109299968281227 15279537984163949952421841)
          ·
            refine ⟨11459653488122962464316381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15279537984163949952421841 11459653488122962464316381)
            ·
              refine ⟨4297370058046110924118643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11459653488122962464316381 4297370058046110924118643)
              ·
                refine ⟨6446055087069166386177965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297370058046110924118643 6446055087069166386177965)
                ·
                  refine ⟨2417270657650937394816737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6446055087069166386177965 2417270657650937394816737)
                  ·
                    refine ⟨1812952993238203046112553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2417270657650937394816737 1812952993238203046112553)
                    ·
                      refine ⟨1359714744928652284584415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1812952993238203046112553 1359714744928652284584415)
                      ·
                        rfl

theorem cell23_2648035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_2648035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648035 prefixEnd_2648035 := by exact prefixLift 2648035
  have htrace : WordTrace (prefixWord ++ tailWord_2648035) baseStart_2648035 baseEnd_2648035 := by
    simpa [prefixWord, tailWord_2648035, baseEnd_2648035] using wordTrace_append hprefix tailTrace_2648035
  have hstable : (prefixWord ++ tailWord_2648035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648035).length < 2 ^ (prefixWord ++ tailWord_2648035).sum := by decide
  have hdescent : baseEnd_2648035 < baseStart_2648035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648064 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_2648064 : Nat := 118140960795 + 2648064 * 2 ^ 59
def prefixEnd_2648064 : Nat := 4983230072969 + 3 ^ 40 * 2648064 * 2
def baseEnd_2648064 : Nat := 1359729635867632671121781

theorem tailTrace_2648064 : CollatzResearch.WordTrace tailWord_2648064 prefixEnd_2648064 1359729635867632671121781 := by
  unfold tailWord_2648064
  simp only [CollatzResearch.WordTrace]
  refine ⟨48291414339261928085291623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64388552452349237447055497 48291414339261928085291623)
  ·
    refine ⟨72437121508892892127937435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48291414339261928085291623 72437121508892892127937435)
    ·
      refine ⟨108655682263339338191906153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72437121508892892127937435 108655682263339338191906153)
      ·
        refine ⟨81491761697504503643929615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108655682263339338191906153 81491761697504503643929615)
        ·
          refine ⟨122237642546256755465894423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81491761697504503643929615 122237642546256755465894423)
          ·
            refine ⟨183356463819385133198841635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122237642546256755465894423 183356463819385133198841635)
            ·
              refine ⟨275034695729077699798262453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183356463819385133198841635 275034695729077699798262453)
              ·
                refine ⟨25784502724601034356087105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275034695729077699798262453 25784502724601034356087105)
                ·
                  refine ⟨19338377043450775767065329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25784502724601034356087105 19338377043450775767065329)
                  ·
                    refine ⟨14503782782588081825298997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19338377043450775767065329 14503782782588081825298997)
                    ·
                      refine ⟨1359729635867632671121781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14503782782588081825298997 1359729635867632671121781)
                      ·
                        rfl

theorem cell23_2648064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_2648064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648064 prefixEnd_2648064 := by exact prefixLift 2648064
  have htrace : WordTrace (prefixWord ++ tailWord_2648064) baseStart_2648064 baseEnd_2648064 := by
    simpa [prefixWord, tailWord_2648064, baseEnd_2648064] using wordTrace_append hprefix tailTrace_2648064
  have hstable : (prefixWord ++ tailWord_2648064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648064).length < 2 ^ (prefixWord ++ tailWord_2648064).sum := by decide
  have hdescent : baseEnd_2648064 < baseStart_2648064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648101 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_2648101 : Nat := 118140960795 + 2648101 * 2 ^ 59
def prefixEnd_2648101 : Nat := 4983230072969 + 3 ^ 40 * 2648101 * 2
def baseEnd_2648101 : Nat := 453249544883949675453037

theorem tailTrace_2648101 : CollatzResearch.WordTrace tailWord_2648101 prefixEnd_2648101 453249544883949675453037 := by
  unfold tailWord_2648101
  simp only [CollatzResearch.WordTrace]
  refine ⟨96584178179389811489680157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64389452119593207659786771 96584178179389811489680157)
  ·
    refine ⟨36219066817271179308630059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96584178179389811489680157 36219066817271179308630059)
    ·
      refine ⟨54328600225906768962945089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36219066817271179308630059 54328600225906768962945089)
      ·
        refine ⟨40746450169430076722208817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54328600225906768962945089 40746450169430076722208817)
        ·
          refine ⟨30559837627072557541656613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40746450169430076722208817 30559837627072557541656613)
          ·
            refine ⟨5729969555076104539060615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30559837627072557541656613 5729969555076104539060615)
            ·
              refine ⟨8594954332614156808590923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5729969555076104539060615 8594954332614156808590923)
              ·
                refine ⟨12892431498921235212886385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8594954332614156808590923 12892431498921235212886385)
                ·
                  refine ⟨9669323624190926409664789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12892431498921235212886385 9669323624190926409664789)
                  ·
                    refine ⟨453249544883949675453037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9669323624190926409664789 453249544883949675453037)
                    ·
                      rfl

theorem cell23_2648101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_2648101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648101 prefixEnd_2648101 := by exact prefixLift 2648101
  have htrace : WordTrace (prefixWord ++ tailWord_2648101) baseStart_2648101 baseEnd_2648101 := by
    simpa [prefixWord, tailWord_2648101, baseEnd_2648101] using wordTrace_append hprefix tailTrace_2648101
  have hstable : (prefixWord ++ tailWord_2648101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648101).length < 2 ^ (prefixWord ++ tailWord_2648101).sum := by decide
  have hdescent : baseEnd_2648101 < baseStart_2648101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648125 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_2648125 : Nat := 118140960795 + 2648125 * 2 ^ 59
def prefixEnd_2648125 : Nat := 4983230072969 + 3 ^ 40 * 2648125 * 2
def baseEnd_2648125 : Nat := 1359760958187556932459001

theorem tailTrace_2648125 : CollatzResearch.WordTrace tailWord_2648125 prefixEnd_2648125 1359760958187556932459001 := by
  unfold tailWord_2648125
  simp only [CollatzResearch.WordTrace]
  refine ⟨96585053531302863588553829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64390035687535242392369219 96585053531302863588553829)
  ·
    refine ⟨18109697537119286922853843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96585053531302863588553829 18109697537119286922853843)
    ·
      refine ⟨27164546305678930384280765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18109697537119286922853843 27164546305678930384280765)
      ·
        refine ⟨10186704864629598894105287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27164546305678930384280765 10186704864629598894105287)
        ·
          refine ⟨15280057296944398341157931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10186704864629598894105287 15280057296944398341157931)
          ·
            refine ⟨22920085945416597511736897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15280057296944398341157931 22920085945416597511736897)
            ·
              refine ⟨17190064459062448133802673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22920085945416597511736897 17190064459062448133802673)
              ·
                refine ⟨12892548344296836100352005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17190064459062448133802673 12892548344296836100352005)
                ·
                  refine ⟨2417352814555656768816001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12892548344296836100352005 2417352814555656768816001)
                  ·
                    refine ⟨1813014610916742576612001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2417352814555656768816001 1813014610916742576612001)
                    ·
                      refine ⟨1359760958187556932459001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813014610916742576612001 1359760958187556932459001)
                      ·
                        rfl

theorem cell23_2648125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_2648125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648125 prefixEnd_2648125 := by exact prefixLift 2648125
  have htrace : WordTrace (prefixWord ++ tailWord_2648125) baseStart_2648125 baseEnd_2648125 := by
    simpa [prefixWord, tailWord_2648125, baseEnd_2648125] using wordTrace_append hprefix tailTrace_2648125
  have hstable : (prefixWord ++ tailWord_2648125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648125).length < 2 ^ (prefixWord ++ tailWord_2648125).sum := by decide
  have hdescent : baseEnd_2648125 < baseStart_2648125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648129 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_2648129 : Nat := 118140960795 + 2648129 * 2 ^ 59
def prefixEnd_2648129 : Nat := 4983230072969 + 3 ^ 40 * 2648129 * 2
def baseEnd_2648129 : Nat := 1359763012110174916808983

theorem tailTrace_2648129 : CollatzResearch.WordTrace tailWord_2648129 prefixEnd_2648129 1359763012110174916808983 := by
  unfold tailWord_2648129
  simp only [CollatzResearch.WordTrace]
  refine ⟨96585199423288372271699441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64390132948858914847799627 96585199423288372271699441)
  ·
    refine ⟨72438899567466279203774581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96585199423288372271699441 72438899567466279203774581)
    ·
      refine ⟨6791146834449963675353867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72438899567466279203774581 6791146834449963675353867)
      ·
        refine ⟨10186720251674945513030801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6791146834449963675353867 10186720251674945513030801)
        ·
          refine ⟨7640040188756209134773101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10186720251674945513030801 7640040188756209134773101)
          ·
            refine ⟨2865015070783578425539913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7640040188756209134773101 2865015070783578425539913)
            ·
              refine ⟨2148761303087683819154935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2865015070783578425539913 2148761303087683819154935)
              ·
                refine ⟨3223141954631525728732403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148761303087683819154935 3223141954631525728732403)
                ·
                  refine ⟨4834712931947288593098605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223141954631525728732403 4834712931947288593098605)
                  ·
                    refine ⟨1813017349480233222411977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4834712931947288593098605 1813017349480233222411977)
                    ·
                      refine ⟨1359763012110174916808983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813017349480233222411977 1359763012110174916808983)
                      ·
                        rfl

theorem cell23_2648129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_2648129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648129 prefixEnd_2648129 := by exact prefixLift 2648129
  have htrace : WordTrace (prefixWord ++ tailWord_2648129) baseStart_2648129 baseEnd_2648129 := by
    simpa [prefixWord, tailWord_2648129, baseEnd_2648129] using wordTrace_append hprefix tailTrace_2648129
  have hstable : (prefixWord ++ tailWord_2648129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648129).length < 2 ^ (prefixWord ++ tailWord_2648129).sum := by decide
  have hdescent : baseEnd_2648129 < baseStart_2648129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648142 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_2648142 : Nat := 118140960795 + 2648142 * 2 ^ 59
def prefixEnd_2648142 : Nat := 4983230072969 + 3 ^ 40 * 2648142 * 2
def baseEnd_2648142 : Nat := 1359769687358683365946423

theorem tailTrace_2648142 : CollatzResearch.WordTrace tailWord_2648142 prefixEnd_2648142 1359769687358683365946423 := by
  unfold tailWord_2648142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073209196530159436490335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64390449048160850327948453 12073209196530159436490335)
  ·
    refine ⟨18109813794795239154735503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12073209196530159436490335 18109813794795239154735503)
    ·
      refine ⟨27164720692192858732103255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18109813794795239154735503 27164720692192858732103255)
      ·
        refine ⟨40747081038289288098154883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27164720692192858732103255 40747081038289288098154883)
        ·
          refine ⟨61120621557433932147232325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40747081038289288098154883 61120621557433932147232325)
          ·
            refine ⟨11460116542018862277606061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61120621557433932147232325 11460116542018862277606061)
            ·
              refine ⟨4297543703257073354102273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11460116542018862277606061 4297543703257073354102273)
              ·
                refine ⟨3223157777442805015576705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4297543703257073354102273 3223157777442805015576705)
                ·
                  refine ⟨2417368333082103761682529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3223157777442805015576705 2417368333082103761682529)
                  ·
                    refine ⟨1813026249811577821261897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2417368333082103761682529 1813026249811577821261897)
                    ·
                      refine ⟨1359769687358683365946423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813026249811577821261897 1359769687358683365946423)
                      ·
                        rfl

theorem cell23_2648142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_2648142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648142 prefixEnd_2648142 := by exact prefixLift 2648142
  have htrace : WordTrace (prefixWord ++ tailWord_2648142) baseStart_2648142 baseEnd_2648142 := by
    simpa [prefixWord, tailWord_2648142, baseEnd_2648142] using wordTrace_append hprefix tailTrace_2648142
  have hstable : (prefixWord ++ tailWord_2648142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648142).length < 2 ^ (prefixWord ++ tailWord_2648142).sum := by decide
  have hdescent : baseEnd_2648142 < baseStart_2648142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648182 : List Nat := [5, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_2648182 : Nat := 118140960795 + 2648182 * 2 ^ 59
def prefixEnd_2648182 : Nat := 4983230072969 + 3 ^ 40 * 2648182 * 2
def baseEnd_2648182 : Nat := 151087802953873689938471

theorem tailTrace_2648182 : CollatzResearch.WordTrace tailWord_2648182 prefixEnd_2648182 151087802953873689938471 := by
  unfold tailWord_2648182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6036695780756022645211175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64391421661397574882252533 6036695780756022645211175)
  ·
    refine ⟨9055043671134033967816763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6036695780756022645211175 9055043671134033967816763)
    ·
      refine ⟨13582565506701050951725145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9055043671134033967816763 13582565506701050951725145)
      ·
        refine ⟨10186924130025788213793859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13582565506701050951725145 10186924130025788213793859)
        ·
          refine ⟨15280386195038682320690789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10186924130025788213793859 15280386195038682320690789)
          ·
            refine ⟨2865072411569752935129523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15280386195038682320690789 2865072411569752935129523)
            ·
              refine ⟨4297608617354629402694285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865072411569752935129523 4297608617354629402694285)
              ·
                refine ⟨1611603231507986026010357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4297608617354629402694285 1611603231507986026010357)
                ·
                  refine ⟨151087802953873689938471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1611603231507986026010357 151087802953873689938471)
                  ·
                    rfl

theorem cell23_2648182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_2648182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648182 prefixEnd_2648182 := by exact prefixLift 2648182
  have htrace : WordTrace (prefixWord ++ tailWord_2648182) baseStart_2648182 baseEnd_2648182 := by
    simpa [prefixWord, tailWord_2648182, baseEnd_2648182] using wordTrace_append hprefix tailTrace_2648182
  have hstable : (prefixWord ++ tailWord_2648182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648182).length < 2 ^ (prefixWord ++ tailWord_2648182).sum := by decide
  have hdescent : baseEnd_2648182 < baseStart_2648182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648285 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2648285 : Nat := 118140960795 + 2648285 * 2 ^ 59
def prefixEnd_2648285 : Nat := 4983230072969 + 3 ^ 40 * 2648285 * 2
def baseEnd_2648285 : Nat := 453281038364092102152755

theorem tailTrace_2648285 : CollatzResearch.WordTrace tailWord_2648285 prefixEnd_2648285 453281038364092102152755 := by
  unfold tailWord_2648285
  simp only [CollatzResearch.WordTrace]
  refine ⟨96590889210723210914378309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64393926140482140609585539 96590889210723210914378309)
  ·
    refine ⟨18110791727010602046445933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96590889210723210914378309 18110791727010602046445933)
    ·
      refine ⟨6791546897628975767417225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18110791727010602046445933 6791546897628975767417225)
      ·
        refine ⟨5093660173221731825562919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6791546897628975767417225 5093660173221731825562919)
        ·
          refine ⟨7640490259832597738344379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5093660173221731825562919 7640490259832597738344379)
          ·
            refine ⟨11460735389748896607516569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7640490259832597738344379 11460735389748896607516569)
            ·
              refine ⟨8595551542311672455637427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11460735389748896607516569 8595551542311672455637427)
              ·
                refine ⟨12893327313467508683456141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8595551542311672455637427 12893327313467508683456141)
                ·
                  refine ⟨4834997742550315756296053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12893327313467508683456141 4834997742550315756296053)
                  ·
                    refine ⟨453281038364092102152755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4834997742550315756296053 453281038364092102152755)
                    ·
                      rfl

theorem cell23_2648285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2648285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648285 prefixEnd_2648285 := by exact prefixLift 2648285
  have htrace : WordTrace (prefixWord ++ tailWord_2648285) baseStart_2648285 baseEnd_2648285 := by
    simpa [prefixWord, tailWord_2648285, baseEnd_2648285] using wordTrace_append hprefix tailTrace_2648285
  have hstable : (prefixWord ++ tailWord_2648285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648285).length < 2 ^ (prefixWord ++ tailWord_2648285).sum := by decide
  have hdescent : baseEnd_2648285 < baseStart_2648285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648288 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_2648288 : Nat := 118140960795 + 2648288 * 2 ^ 59
def prefixEnd_2648288 : Nat := 4983230072969 + 3 ^ 40 * 2648288 * 2
def baseEnd_2648288 : Nat := 1359844655534239794720751

theorem tailTrace_2648288 : CollatzResearch.WordTrace tailWord_2648288 prefixEnd_2648288 1359844655534239794720751 := by
  unfold tailWord_2648288
  simp only [CollatzResearch.WordTrace]
  refine ⟨48295499314856171213368759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64393999086474894951158345 48295499314856171213368759)
  ·
    refine ⟨72443248972284256820053139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48295499314856171213368759 72443248972284256820053139)
    ·
      refine ⟨108664873458426385230079709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72443248972284256820053139 108664873458426385230079709)
      ·
        refine ⟨40749327546909894461279891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108664873458426385230079709 40749327546909894461279891)
        ·
          refine ⟨61123991320364841691919837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40749327546909894461279891 61123991320364841691919837)
          ·
            refine ⟨22921496745136815634469939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61123991320364841691919837 22921496745136815634469939)
            ·
              refine ⟨34382245117705223451704909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22921496745136815634469939 34382245117705223451704909)
              ·
                refine ⟨12893341919139458794389341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34382245117705223451704909 12893341919139458794389341)
                ·
                  refine ⟨4835003219677297047896003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12893341919139458794389341 4835003219677297047896003)
                  ·
                    refine ⟨7252504829515945571844005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4835003219677297047896003 7252504829515945571844005)
                    ·
                      refine ⟨1359844655534239794720751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7252504829515945571844005 1359844655534239794720751)
                      ·
                        rfl

theorem cell23_2648288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_2648288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648288 prefixEnd_2648288 := by exact prefixLift 2648288
  have htrace : WordTrace (prefixWord ++ tailWord_2648288) baseStart_2648288 baseEnd_2648288 := by
    simpa [prefixWord, tailWord_2648288, baseEnd_2648288] using wordTrace_append hprefix tailTrace_2648288
  have hstable : (prefixWord ++ tailWord_2648288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648288).length < 2 ^ (prefixWord ++ tailWord_2648288).sum := by decide
  have hdescent : baseEnd_2648288 < baseStart_2648288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648298 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_2648298 : Nat := 118140960795 + 2648298 * 2 ^ 59
def prefixEnd_2648298 : Nat := 4983230072969 + 3 ^ 40 * 2648298 * 2
def baseEnd_2648298 : Nat := 453283263446928251865235

theorem tailTrace_2648298 : CollatzResearch.WordTrace tailWord_2648298 prefixEnd_2648298 453283263446928251865235 := by
  unfold tailWord_2648298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24147840839919028533650387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64394242239784076089734365 24147840839919028533650387)
  ·
    refine ⟨36221761259878542800475581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24147840839919028533650387 36221761259878542800475581)
    ·
      refine ⟨13583160472454453550178343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36221761259878542800475581 13583160472454453550178343)
      ·
        refine ⟨20374740708681680325267515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13583160472454453550178343 20374740708681680325267515)
        ·
          refine ⟨30562111063022520487901273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20374740708681680325267515 30562111063022520487901273)
          ·
            refine ⟨22921583297266890365925955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30562111063022520487901273 22921583297266890365925955)
            ·
              refine ⟨34382374945900335548888933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22921583297266890365925955 34382374945900335548888933)
              ·
                refine ⟨6446695302356312915416675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34382374945900335548888933 6446695302356312915416675)
                ·
                  refine ⟨9670042953534469373125013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6446695302356312915416675 9670042953534469373125013)
                  ·
                    refine ⟨453283263446928251865235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9670042953534469373125013 453283263446928251865235)
                    ·
                      rfl

theorem cell23_2648298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_2648298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648298 prefixEnd_2648298 := by exact prefixLift 2648298
  have htrace : WordTrace (prefixWord ++ tailWord_2648298) baseStart_2648298 baseEnd_2648298 := by
    simpa [prefixWord, tailWord_2648298, baseEnd_2648298] using wordTrace_append hprefix tailTrace_2648298
  have hstable : (prefixWord ++ tailWord_2648298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648298).length < 2 ^ (prefixWord ++ tailWord_2648298).sum := by decide
  have hdescent : baseEnd_2648298 < baseStart_2648298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648332 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_2648332 : Nat := 118140960795 + 2648332 * 2 ^ 59
def prefixEnd_2648332 : Nat := 4983230072969 + 3 ^ 40 * 2648332 * 2
def baseEnd_2648332 : Nat := 453289082894345874190183

theorem tailTrace_2648332 : CollatzResearch.WordTrace tailWord_2648332 prefixEnd_2648332 453289082894345874190183 := by
  unfold tailWord_2648332
  simp only [CollatzResearch.WordTrace]
  refine ⟨48296301720776468970669625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64395068961035291960892833 48296301720776468970669625)
  ·
    refine ⟨36222226290582351728002219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48296301720776468970669625 36222226290582351728002219)
    ·
      refine ⟨54333339435873527592003329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36222226290582351728002219 54333339435873527592003329)
      ·
        refine ⟨40750004576905145694002497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54333339435873527592003329 40750004576905145694002497)
        ·
          refine ⟨30562503432678859270501873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40750004576905145694002497 30562503432678859270501873)
          ·
            refine ⟨22921877574509144452876405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30562503432678859270501873 22921877574509144452876405)
            ·
              refine ⟨2148926022610232292457163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22921877574509144452876405 2148926022610232292457163)
              ·
                refine ⟨3223389033915348438685745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148926022610232292457163 3223389033915348438685745)
                ·
                  refine ⟨2417541775436511329014309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3223389033915348438685745 2417541775436511329014309)
                  ·
                    refine ⟨453289082894345874190183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417541775436511329014309 453289082894345874190183)
                    ·
                      rfl

theorem cell23_2648332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_2648332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648332 prefixEnd_2648332 := by exact prefixLift 2648332
  have htrace : WordTrace (prefixWord ++ tailWord_2648332) baseStart_2648332 baseEnd_2648332 := by
    simpa [prefixWord, tailWord_2648332, baseEnd_2648332] using wordTrace_append hprefix tailTrace_2648332
  have hstable : (prefixWord ++ tailWord_2648332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648332).length < 2 ^ (prefixWord ++ tailWord_2648332).sum := by decide
  have hdescent : baseEnd_2648332 < baseStart_2648332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648355 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 3]
def baseStart_2648355 : Nat := 118140960795 + 2648355 * 2 ^ 59
def prefixEnd_2648355 : Nat := 4983230072969 + 3 ^ 40 * 2648355 * 2
def baseEnd_2648355 : Nat := 1359879058738091032582943

theorem tailTrace_2648355 : CollatzResearch.WordTrace tailWord_2648355 prefixEnd_2648355 1359879058738091032582943 := by
  unfold tailWord_2648355
  simp only [CollatzResearch.WordTrace]
  refine ⟨96593442320469612869426519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64395628213646408579617679 96593442320469612869426519)
  ·
    refine ⟨144890163480704419304139779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96593442320469612869426519 144890163480704419304139779)
    ·
      refine ⟨217335245221056628956209669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144890163480704419304139779 217335245221056628956209669)
      ·
        refine ⟨40750358478948117929289313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217335245221056628956209669 40750358478948117929289313)
        ·
          refine ⟨30562768859211088446966985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40750358478948117929289313 30562768859211088446966985)
          ·
            refine ⟨22922076644408316335225239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30562768859211088446966985 22922076644408316335225239)
            ·
              refine ⟨34383114966612474502837859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22922076644408316335225239 34383114966612474502837859)
              ·
                refine ⟨51574672449918711754256789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34383114966612474502837859 51574672449918711754256789)
                ·
                  refine ⟨2417562771089939613480787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51574672449918711754256789 2417562771089939613480787)
                  ·
                    refine ⟨3626344156634909420221181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2417562771089939613480787 3626344156634909420221181)
                    ·
                      refine ⟨1359879058738091032582943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3626344156634909420221181 1359879058738091032582943)
                      ·
                        rfl

theorem cell23_2648355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_2648355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648355 prefixEnd_2648355 := by exact prefixLift 2648355
  have htrace : WordTrace (prefixWord ++ tailWord_2648355) baseStart_2648355 baseEnd_2648355 := by
    simpa [prefixWord, tailWord_2648355, baseEnd_2648355] using wordTrace_append hprefix tailTrace_2648355
  have hstable : (prefixWord ++ tailWord_2648355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648355).length < 2 ^ (prefixWord ++ tailWord_2648355).sum := by decide
  have hdescent : baseEnd_2648355 < baseStart_2648355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648356 : List Nat := [2, 3, 1, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_2648356 : Nat := 118140960795 + 2648356 * 2 ^ 59
def prefixEnd_2648356 : Nat := 4983230072969 + 3 ^ 40 * 2648356 * 2
def baseEnd_2648356 : Nat := 1359879572218745528670439

theorem tailTrace_2648356 : CollatzResearch.WordTrace tailWord_2648356 prefixEnd_2648356 1359879572218745528670439 := by
  unfold tailWord_2648356
  simp only [CollatzResearch.WordTrace]
  refine ⟨48296739396732995020106461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64395652528977326693475281 48296739396732995020106461)
  ·
    refine ⟨18111277273774873132539923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48296739396732995020106461 18111277273774873132539923)
    ·
      refine ⟨27166915910662309698809885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18111277273774873132539923 27166915910662309698809885)
      ·
        refine ⟨10187593466498366137053707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27166915910662309698809885 10187593466498366137053707)
        ·
          refine ⟨15281390199747549205580561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10187593466498366137053707 15281390199747549205580561)
          ·
            refine ⟨11461042649810661904185421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15281390199747549205580561 11461042649810661904185421)
            ·
              refine ⟨4297890993678998214069533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11461042649810661904185421 4297890993678998214069533)
              ·
                refine ⟨1611709122629624330276075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4297890993678998214069533 1611709122629624330276075)
                ·
                  refine ⟨2417563683944436495414113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611709122629624330276075 2417563683944436495414113)
                  ·
                    refine ⟨1813172762958327371560585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2417563683944436495414113 1813172762958327371560585)
                    ·
                      refine ⟨1359879572218745528670439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813172762958327371560585 1359879572218745528670439)
                      ·
                        rfl

theorem cell23_2648356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_2648356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648356 prefixEnd_2648356 := by exact prefixLift 2648356
  have htrace : WordTrace (prefixWord ++ tailWord_2648356) baseStart_2648356 baseEnd_2648356 := by
    simpa [prefixWord, tailWord_2648356, baseEnd_2648356] using wordTrace_append hprefix tailTrace_2648356
  have hstable : (prefixWord ++ tailWord_2648356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648356).length < 2 ^ (prefixWord ++ tailWord_2648356).sum := by decide
  have hdescent : baseEnd_2648356 < baseStart_2648356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648362 : List Nat := [3, 1, 4, 2, 3, 1, 9]
def baseStart_2648362 : Nat := 118140960795 + 2648362 * 2 ^ 59
def prefixEnd_2648362 : Nat := 4983230072969 + 3 ^ 40 * 2648362 * 2
def baseEnd_2648362 : Nat := 16788674729662623520931

theorem tailTrace_2648362 : CollatzResearch.WordTrace tailWord_2648362 prefixEnd_2648362 16788674729662623520931 := by
  unfold tailWord_2648362
  simp only [CollatzResearch.WordTrace]
  refine ⟨24148424407861063266232835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64395798420962835376620893 24148424407861063266232835)
  ·
    refine ⟨36222636611791594899349253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24148424407861063266232835 36222636611791594899349253)
    ·
      refine ⟨6791744364710924043627985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36222636611791594899349253 6791744364710924043627985)
      ·
        refine ⟨5093808273533193032720989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6791744364710924043627985 5093808273533193032720989)
        ·
          refine ⟨1910178102574947387270371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5093808273533193032720989 1910178102574947387270371)
          ·
            refine ⟨2865267153862421080905557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910178102574947387270371 2865267153862421080905557)
            ·
              refine ⟨16788674729662623520931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2865267153862421080905557 16788674729662623520931)
              ·
                rfl

theorem cell23_2648362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 9].length) (baseStart_2648362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648362 prefixEnd_2648362 := by exact prefixLift 2648362
  have htrace : WordTrace (prefixWord ++ tailWord_2648362) baseStart_2648362 baseEnd_2648362 := by
    simpa [prefixWord, tailWord_2648362, baseEnd_2648362] using wordTrace_append hprefix tailTrace_2648362
  have hstable : (prefixWord ++ tailWord_2648362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648362).length < 2 ^ (prefixWord ++ tailWord_2648362).sum := by decide
  have hdescent : baseEnd_2648362 < baseStart_2648362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648408 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2648408 : Nat := 118140960795 + 2648408 * 2 ^ 59
def prefixEnd_2648408 : Nat := 4983230072969 + 3 ^ 40 * 2648408 * 2
def baseEnd_2648408 : Nat := 1359906273212779325220199

theorem tailTrace_2648408 : CollatzResearch.WordTrace tailWord_2648408 prefixEnd_2648408 1359906273212779325220199 := by
  unfold tailWord_2648408
  simp only [CollatzResearch.WordTrace]
  refine ⟨48297687694638801460552939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64396916926185068614070585 48297687694638801460552939)
  ·
    refine ⟨72446531541958202190829409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48297687694638801460552939 72446531541958202190829409)
    ·
      refine ⟨54334898656468651643122057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72446531541958202190829409 54334898656468651643122057)
      ·
        refine ⟨40751173992351488732341543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54334898656468651643122057 40751173992351488732341543)
        ·
          refine ⟨61126760988527233098512315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40751173992351488732341543 61126760988527233098512315)
          ·
            refine ⟨91690141482790849647768473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61126760988527233098512315 91690141482790849647768473)
            ·
              refine ⟨68767606112093137235826355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91690141482790849647768473 68767606112093137235826355)
              ·
                refine ⟨103151409168139705853739533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68767606112093137235826355 103151409168139705853739533)
                ·
                  refine ⟨38681778438052389695152325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103151409168139705853739533 38681778438052389695152325)
                  ·
                    refine ⟨7252833457134823067841061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38681778438052389695152325 7252833457134823067841061)
                    ·
                      refine ⟨1359906273212779325220199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7252833457134823067841061 1359906273212779325220199)
                      ·
                        rfl

theorem cell23_2648408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2648408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648408 prefixEnd_2648408 := by exact prefixLift 2648408
  have htrace : WordTrace (prefixWord ++ tailWord_2648408) baseStart_2648408 baseEnd_2648408 := by
    simpa [prefixWord, tailWord_2648408, baseEnd_2648408] using wordTrace_append hprefix tailTrace_2648408
  have hstable : (prefixWord ++ tailWord_2648408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648408).length < 2 ^ (prefixWord ++ tailWord_2648408).sum := by decide
  have hdescent : baseEnd_2648408 < baseStart_2648408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648416 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 1, 3, 2]
def baseStart_2648416 : Nat := 118140960795 + 2648416 * 2 ^ 59
def prefixEnd_2648416 : Nat := 4983230072969 + 3 ^ 40 * 2648416 * 2
def baseEnd_2648416 : Nat := 1359910381058015293920163

theorem tailTrace_2648416 : CollatzResearch.WordTrace tailWord_2648416 prefixEnd_2648416 1359910381058015293920163 := by
  unfold tailWord_2648416
  simp only [CollatzResearch.WordTrace]
  refine ⟨48297833586624310143698551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64397111448832413524931401 48297833586624310143698551)
  ·
    refine ⟨72446750379936465215547827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48297833586624310143698551 72446750379936465215547827)
    ·
      refine ⟨108670125569904697823321741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72446750379936465215547827 108670125569904697823321741)
      ·
        refine ⟨40751297088714261683745653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108670125569904697823321741 40751297088714261683745653)
        ·
          refine ⟨3820434102066962032851155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40751297088714261683745653 3820434102066962032851155)
          ·
            refine ⟨5730651153100443049276733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820434102066962032851155 5730651153100443049276733)
            ·
              refine ⟨2148994182412666143478775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5730651153100443049276733 2148994182412666143478775)
              ·
                refine ⟨3223491273618999215218163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148994182412666143478775 3223491273618999215218163)
                ·
                  refine ⟨4835236910428498822827245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223491273618999215218163 4835236910428498822827245)
                  ·
                    refine ⟨1813213841410687058560217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4835236910428498822827245 1813213841410687058560217)
                    ·
                      refine ⟨1359910381058015293920163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813213841410687058560217 1359910381058015293920163)
                      ·
                        rfl

theorem cell23_2648416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_2648416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648416 prefixEnd_2648416 := by exact prefixLift 2648416
  have htrace : WordTrace (prefixWord ++ tailWord_2648416) baseStart_2648416 baseEnd_2648416 := by
    simpa [prefixWord, tailWord_2648416, baseEnd_2648416] using wordTrace_append hprefix tailTrace_2648416
  have hstable : (prefixWord ++ tailWord_2648416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648416).length < 2 ^ (prefixWord ++ tailWord_2648416).sum := by decide
  have hdescent : baseEnd_2648416 < baseStart_2648416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648435 : List Nat := [1, 1, 1, 2, 2, 1, 2, 8, 5]
def baseStart_2648435 : Nat := 118140960795 + 2648435 * 2 ^ 59
def prefixEnd_2648435 : Nat := 4983230072969 + 3 ^ 40 * 2648435 * 2
def baseEnd_2648435 : Nat := 151102237465605635509175

theorem tailTrace_2648435 : CollatzResearch.WordTrace tailWord_2648435 prefixEnd_2648435 151102237465605635509175 := by
  unfold tailWord_2648435
  simp only [CollatzResearch.WordTrace]
  refine ⟨96596360160179786532338759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64397573440119857688225839 96596360160179786532338759)
  ·
    refine ⟨144894540240269679798508139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96596360160179786532338759 144894540240269679798508139)
    ·
      refine ⟨217341810360404519697762209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144894540240269679798508139 217341810360404519697762209)
      ·
        refine ⟨163006357770303389773321657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217341810360404519697762209 163006357770303389773321657)
        ·
          refine ⟨122254768327727542329991243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163006357770303389773321657 122254768327727542329991243)
          ·
            refine ⟨183382152491591313494986865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122254768327727542329991243 183382152491591313494986865)
            ·
              refine ⟨137536614368693485121240149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183382152491591313494986865 137536614368693485121240149)
              ·
                refine ⟨1611757199633126778764533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 137536614368693485121240149 1611757199633126778764533)
                ·
                  refine ⟨151102237465605635509175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1611757199633126778764533 151102237465605635509175)
                  ·
                    rfl

theorem cell23_2648435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 5].length) (baseStart_2648435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648435 prefixEnd_2648435 := by exact prefixLift 2648435
  have htrace : WordTrace (prefixWord ++ tailWord_2648435) baseStart_2648435 baseEnd_2648435 := by
    simpa [prefixWord, tailWord_2648435, baseEnd_2648435] using wordTrace_append hprefix tailTrace_2648435
  have hstable : (prefixWord ++ tailWord_2648435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648435).length < 2 ^ (prefixWord ++ tailWord_2648435).sum := by decide
  have hdescent : baseEnd_2648435 < baseStart_2648435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648445 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_2648445 : Nat := 118140960795 + 2648445 * 2 ^ 59
def prefixEnd_2648445 : Nat := 4983230072969 + 3 ^ 40 * 2648445 * 2
def baseEnd_2648445 : Nat := 1359925271996995680457529

theorem tailTrace_2648445 : CollatzResearch.WordTrace tailWord_2648445 prefixEnd_2648445 1359925271996995680457529 := by
  unfold tailWord_2648445
  simp only [CollatzResearch.WordTrace]
  refine ⟨96596724890143558240202789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64397816593429038826801859 96596724890143558240202789)
  ·
    refine ⟨18111885916901917170038023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96596724890143558240202789 18111885916901917170038023)
    ·
      refine ⟨27167828875352875755057035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18111885916901917170038023 27167828875352875755057035)
      ·
        refine ⟨40751743313029313632585553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27167828875352875755057035 40751743313029313632585553)
        ·
          refine ⟨30563807484771985224439165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40751743313029313632585553 30563807484771985224439165)
          ·
            refine ⟨11461427806789494459164687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30563807484771985224439165 11461427806789494459164687)
            ·
              refine ⟨17192141710184241688747031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11461427806789494459164687 17192141710184241688747031)
              ·
                refine ⟨25788212565276362533120547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17192141710184241688747031 25788212565276362533120547)
                ·
                  refine ⟨38682318847914543799680821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25788212565276362533120547 38682318847914543799680821)
                  ·
                    refine ⟨3626467391991988481220077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38682318847914543799680821 3626467391991988481220077)
                    ·
                      refine ⟨1359925271996995680457529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3626467391991988481220077 1359925271996995680457529)
                      ·
                        rfl

theorem cell23_2648445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_2648445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648445 prefixEnd_2648445 := by exact prefixLift 2648445
  have htrace : WordTrace (prefixWord ++ tailWord_2648445) baseStart_2648445 baseEnd_2648445 := by
    simpa [prefixWord, tailWord_2648445, baseEnd_2648445] using wordTrace_append hprefix tailTrace_2648445
  have hstable : (prefixWord ++ tailWord_2648445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648445).length < 2 ^ (prefixWord ++ tailWord_2648445).sum := by decide
  have hdescent : baseEnd_2648445 < baseStart_2648445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648485 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_2648485 : Nat := 118140960795 + 2648485 * 2 ^ 59
def prefixEnd_2648485 : Nat := 4983230072969 + 3 ^ 40 * 2648485 * 2
def baseEnd_2648485 : Nat := 1359945811223175523957345

theorem tailTrace_2648485 : CollatzResearch.WordTrace tailWord_2648485 prefixEnd_2648485 1359945811223175523957345 := by
  unfold tailWord_2648485
  simp only [CollatzResearch.WordTrace]
  refine ⟨96598183809998645071658909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64398789206665763381105939 96598183809998645071658909)
  ·
    refine ⟨36224318928749491901872091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96598183809998645071658909 36224318928749491901872091)
    ·
      refine ⟨54336478393124237852808137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36224318928749491901872091 54336478393124237852808137)
      ·
        refine ⟨40752358794843178389606103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54336478393124237852808137 40752358794843178389606103)
        ·
          refine ⟨61128538192264767584409155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40752358794843178389606103 61128538192264767584409155)
          ·
            refine ⟨91692807288397151376613733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61128538192264767584409155 91692807288397151376613733)
            ·
              refine ⟨17192401366574465883115075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91692807288397151376613733 17192401366574465883115075)
              ·
                refine ⟨25788602049861698824672613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17192401366574465883115075 25788602049861698824672613)
                ·
                  refine ⟨4835362884349068529626115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25788602049861698824672613 4835362884349068529626115)
                  ·
                    refine ⟨7253044326523602794439173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4835362884349068529626115 7253044326523602794439173)
                    ·
                      refine ⟨1359945811223175523957345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7253044326523602794439173 1359945811223175523957345)
                      ·
                        rfl

theorem cell23_2648485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_2648485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648485 prefixEnd_2648485 := by exact prefixLift 2648485
  have htrace : WordTrace (prefixWord ++ tailWord_2648485) baseStart_2648485 baseEnd_2648485 := by
    simpa [prefixWord, tailWord_2648485, baseEnd_2648485] using wordTrace_append hprefix tailTrace_2648485
  have hstable : (prefixWord ++ tailWord_2648485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648485).length < 2 ^ (prefixWord ++ tailWord_2648485).sum := by decide
  have hdescent : baseEnd_2648485 < baseStart_2648485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648522 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_2648522 : Nat := 118140960795 + 2648522 * 2 ^ 59
def prefixEnd_2648522 : Nat := 4983230072969 + 3 ^ 40 * 2648522 * 2
def baseEnd_2648522 : Nat := 1359964810007391879194675

theorem tailTrace_2648522 : CollatzResearch.WordTrace tailWord_2648522 prefixEnd_2648522 1359964810007391879194675 := by
  unfold tailWord_2648522
  simp only [CollatzResearch.WordTrace]
  refine ⟨24149883327716150097688955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64399688873909733593837213 24149883327716150097688955)
  ·
    refine ⟨36224824991574225146533433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24149883327716150097688955 36224824991574225146533433)
    ·
      refine ⟨27168618743680668859900075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36224824991574225146533433 27168618743680668859900075)
      ·
        refine ⟨40752928115521003289850113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27168618743680668859900075 40752928115521003289850113)
        ·
          refine ⟨30564696086640752467387585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40752928115521003289850113 30564696086640752467387585)
          ·
            refine ⟨22923522064980564350540689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30564696086640752467387585 22923522064980564350540689)
            ·
              refine ⟨17192641548735423262905517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22923522064980564350540689 17192641548735423262905517)
              ·
                refine ⟨6447240580775783723589569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17192641548735423262905517 6447240580775783723589569)
                ·
                  refine ⟨4835430435581837792692177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6447240580775783723589569 4835430435581837792692177)
                  ·
                    refine ⟨3626572826686378344519133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4835430435581837792692177 3626572826686378344519133)
                    ·
                      refine ⟨1359964810007391879194675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3626572826686378344519133 1359964810007391879194675)
                      ·
                        rfl

theorem cell23_2648522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_2648522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648522 prefixEnd_2648522 := by exact prefixLift 2648522
  have htrace : WordTrace (prefixWord ++ tailWord_2648522) baseStart_2648522 baseEnd_2648522 := by
    simpa [prefixWord, tailWord_2648522, baseEnd_2648522] using wordTrace_append hprefix tailTrace_2648522
  have hstable : (prefixWord ++ tailWord_2648522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648522).length < 2 ^ (prefixWord ++ tailWord_2648522).sum := by decide
  have hdescent : baseEnd_2648522 < baseStart_2648522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648555 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 3, 5]
def baseStart_2648555 : Nat := 118140960795 + 2648555 * 2 ^ 59
def prefixEnd_2648555 : Nat := 4983230072969 + 3 ^ 40 * 2648555 * 2
def baseEnd_2648555 : Nat := 453327251622996750027341

theorem tailTrace_2648555 : CollatzResearch.WordTrace tailWord_2648555 prefixEnd_2648555 453327251622996750027341 := by
  unfold tailWord_2648555
  simp only [CollatzResearch.WordTrace]
  refine ⟨96600736919745047026707119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64400491279830031351138079 96600736919745047026707119)
  ·
    refine ⟨144901105379617570540060679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96600736919745047026707119 144901105379617570540060679)
    ·
      refine ⟨217351658069426355810091019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144901105379617570540060679 217351658069426355810091019)
      ·
        refine ⟨326027487104139533715136529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217351658069426355810091019 326027487104139533715136529)
        ·
          refine ⟨244520615328104650286352397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326027487104139533715136529 244520615328104650286352397)
          ·
            refine ⟨91695230748039243857382149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244520615328104650286352397 91695230748039243857382149)
            ·
              refine ⟨17192855765257358223259153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91695230748039243857382149 17192855765257358223259153)
              ·
                refine ⟨12894641823943018667444365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17192855765257358223259153 12894641823943018667444365)
                ·
                  refine ⟨4835490683978632000291637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12894641823943018667444365 4835490683978632000291637)
                  ·
                    refine ⟨453327251622996750027341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4835490683978632000291637 453327251622996750027341)
                    ·
                      rfl

theorem cell23_2648555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 5].length) (baseStart_2648555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648555 prefixEnd_2648555 := by exact prefixLift 2648555
  have htrace : WordTrace (prefixWord ++ tailWord_2648555) baseStart_2648555 baseEnd_2648555 := by
    simpa [prefixWord, tailWord_2648555, baseEnd_2648555] using wordTrace_append hprefix tailTrace_2648555
  have hstable : (prefixWord ++ tailWord_2648555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648555).length < 2 ^ (prefixWord ++ tailWord_2648555).sum := by decide
  have hdescent : baseEnd_2648555 < baseStart_2648555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648579 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 2, 3, 2]
def baseStart_2648579 : Nat := 118140960795 + 2648579 * 2 ^ 59
def prefixEnd_2648579 : Nat := 4983230072969 + 3 ^ 40 * 2648579 * 2
def baseEnd_2648579 : Nat := 1359994078404698156181913

theorem tailTrace_2648579 : CollatzResearch.WordTrace tailWord_2648579 prefixEnd_2648579 1359994078404698156181913 := by
  unfold tailWord_2648579
  simp only [CollatzResearch.WordTrace]
  refine ⟨96601612271658099125580791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64401074847772066083720527 96601612271658099125580791)
  ·
    refine ⟨144902418407487148688371187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96601612271658099125580791 144902418407487148688371187)
    ·
      refine ⟨217353627611230723032556781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144902418407487148688371187 217353627611230723032556781)
      ·
        refine ⟨81507610354211521137208793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217353627611230723032556781 81507610354211521137208793)
        ·
          refine ⟨61130707765658640852906595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81507610354211521137208793 61130707765658640852906595)
          ·
            refine ⟨91696061648487961279359893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61130707765658640852906595 91696061648487961279359893)
            ·
              refine ⟨4298252889772873184969995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91696061648487961279359893 4298252889772873184969995)
              ·
                refine ⟨6447379334659309777454993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298252889772873184969995 6447379334659309777454993)
                ·
                  refine ⟨4835534500994482333091245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6447379334659309777454993 4835534500994482333091245)
                  ·
                    refine ⟨1813325437872930874909217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4835534500994482333091245 1813325437872930874909217)
                    ·
                      refine ⟨1359994078404698156181913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813325437872930874909217 1359994078404698156181913)
                      ·
                        rfl

theorem cell23_2648579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_2648579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648579 prefixEnd_2648579 := by exact prefixLift 2648579
  have htrace : WordTrace (prefixWord ++ tailWord_2648579) baseStart_2648579 baseEnd_2648579 := by
    simpa [prefixWord, tailWord_2648579, baseEnd_2648579] using wordTrace_append hprefix tailTrace_2648579
  have hstable : (prefixWord ++ tailWord_2648579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648579).length < 2 ^ (prefixWord ++ tailWord_2648579).sum := by decide
  have hdescent : baseEnd_2648579 < baseStart_2648579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648586 : List Nat := [3, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_2648586 : Nat := 118140960795 + 2648586 * 2 ^ 59
def prefixEnd_2648586 : Nat := 4983230072969 + 3 ^ 40 * 2648586 * 2
def baseEnd_2648586 : Nat := 1359997672769279628794381

theorem tailTrace_2648586 : CollatzResearch.WordTrace tailWord_2648586 prefixEnd_2648586 1359997672769279628794381 := by
  unfold tailWord_2648586
  simp only [CollatzResearch.WordTrace]
  refine ⟨24150466895658184830271403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64401245055088492880723741 24150466895658184830271403)
  ·
    refine ⟨36225700343487277245407105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24150466895658184830271403 36225700343487277245407105)
    ·
      refine ⟨27169275257615457934055329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36225700343487277245407105 27169275257615457934055329)
      ·
        refine ⟨20376956443211593450541497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27169275257615457934055329 20376956443211593450541497)
        ·
          refine ⟨15282717332408695087906123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20376956443211593450541497 15282717332408695087906123)
          ·
            refine ⟨22924075998613042631859185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15282717332408695087906123 22924075998613042631859185)
            ·
              refine ⟨17193056998959781973894389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22924075998613042631859185 17193056998959781973894389)
              ·
                refine ⟨1611849093652479560052599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17193056998959781973894389 1611849093652479560052599)
                ·
                  refine ⟨2417773640478719340078899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611849093652479560052599 2417773640478719340078899)
                  ·
                    refine ⟨3626660460718079010118349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2417773640478719340078899 3626660460718079010118349)
                    ·
                      refine ⟨1359997672769279628794381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3626660460718079010118349 1359997672769279628794381)
                      ·
                        rfl

theorem cell23_2648586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_2648586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648586 prefixEnd_2648586 := by exact prefixLift 2648586
  have htrace : WordTrace (prefixWord ++ tailWord_2648586) baseStart_2648586 baseEnd_2648586 := by
    simpa [prefixWord, tailWord_2648586, baseEnd_2648586] using wordTrace_append hprefix tailTrace_2648586
  have hstable : (prefixWord ++ tailWord_2648586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648586).length < 2 ^ (prefixWord ++ tailWord_2648586).sum := by decide
  have hdescent : baseEnd_2648586 < baseStart_2648586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648602 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_2648602 : Nat := 118140960795 + 2648602 * 2 ^ 59
def prefixEnd_2648602 : Nat := 4983230072969 + 3 ^ 40 * 2648602 * 2
def baseEnd_2648602 : Nat := 453335296153250522064769

theorem tailTrace_2648602 : CollatzResearch.WordTrace tailWord_2648602 prefixEnd_2648602 453335296153250522064769 := by
  unfold tailWord_2648602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24150612787643693513417015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64401634100383182702445373 24150612787643693513417015)
  ·
    refine ⟨36225919181465540270125523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24150612787643693513417015 36225919181465540270125523)
    ·
      refine ⟨54338878772198310405188285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36225919181465540270125523 54338878772198310405188285)
      ·
        refine ⟨20377079539574366401945607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54338878772198310405188285 20377079539574366401945607)
        ·
          refine ⟨30565619309361549602918411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20377079539574366401945607 30565619309361549602918411)
          ·
            refine ⟨45848428964042324404377617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30565619309361549602918411 45848428964042324404377617)
            ·
              refine ⟨34386321723031743303283213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45848428964042324404377617 34386321723031743303283213)
              ·
                refine ⟨12894870646136903738731205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34386321723031743303283213 12894870646136903738731205)
                ·
                  refine ⟨2417788246150669451012101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12894870646136903738731205 2417788246150669451012101)
                  ·
                    refine ⟨453335296153250522064769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417788246150669451012101 453335296153250522064769)
                    ·
                      rfl

theorem cell23_2648602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_2648602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648602 prefixEnd_2648602 := by exact prefixLift 2648602
  have htrace : WordTrace (prefixWord ++ tailWord_2648602) baseStart_2648602 baseEnd_2648602 := by
    simpa [prefixWord, tailWord_2648602, baseEnd_2648602] using wordTrace_append hprefix tailTrace_2648602
  have hstable : (prefixWord ++ tailWord_2648602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648602).length < 2 ^ (prefixWord ++ tailWord_2648602).sum := by decide
  have hdescent : baseEnd_2648602 < baseStart_2648602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648629 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_2648629 : Nat := 118140960795 + 2648629 * 2 ^ 59
def prefixEnd_2648629 : Nat := 4983230072969 + 3 ^ 40 * 2648629 * 2
def baseEnd_2648629 : Nat := 1360019752437422960556683

theorem tailTrace_2648629 : CollatzResearch.WordTrace tailWord_2648629 prefixEnd_2648629 1360019752437422960556683 := by
  unfold tailWord_2648629
  simp only [CollatzResearch.WordTrace]
  refine ⟨96603435921476957664900941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64402290614317971776600627 96603435921476957664900941)
  ·
    refine ⟨36226288470553859124337853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96603435921476957664900941 36226288470553859124337853)
    ·
      refine ⟨13584858176457697171626695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36226288470553859124337853 13584858176457697171626695)
      ·
        refine ⟨20377287264686545757440043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13584858176457697171626695 20377287264686545757440043)
        ·
          refine ⟨30565930897029818636160065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20377287264686545757440043 30565930897029818636160065)
          ·
            refine ⟨22924448172772363977120049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30565930897029818636160065 22924448172772363977120049)
            ·
              refine ⟨17193336129579272982840037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22924448172772363977120049 17193336129579272982840037)
              ·
                refine ⟨3223750524296113684282507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17193336129579272982840037 3223750524296113684282507)
                ·
                  refine ⟨4835625786444170526423761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3223750524296113684282507 4835625786444170526423761)
                  ·
                    refine ⟨3626719339833127894817821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4835625786444170526423761 3626719339833127894817821)
                    ·
                      refine ⟨1360019752437422960556683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3626719339833127894817821 1360019752437422960556683)
                      ·
                        rfl

theorem cell23_2648629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_2648629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648629 prefixEnd_2648629 := by exact prefixLift 2648629
  have htrace : WordTrace (prefixWord ++ tailWord_2648629) baseStart_2648629 baseEnd_2648629 := by
    simpa [prefixWord, tailWord_2648629, baseEnd_2648629] using wordTrace_append hprefix tailTrace_2648629
  have hstable : (prefixWord ++ tailWord_2648629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648629).length < 2 ^ (prefixWord ++ tailWord_2648629).sum := by decide
  have hdescent : baseEnd_2648629 < baseStart_2648629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648632 : List Nat := [2, 1, 2, 1, 4, 1, 5, 7]
def baseStart_2648632 : Nat := 118140960795 + 2648632 * 2 ^ 59
def prefixEnd_2648632 : Nat := 4983230072969 + 3 ^ 40 * 2648632 * 2
def baseEnd_2648632 : Nat := 50371158995532831437747

theorem tailTrace_2648632 : CollatzResearch.WordTrace tailWord_2648632 prefixEnd_2648632 50371158995532831437747 := by
  unfold tailWord_2648632
  simp only [CollatzResearch.WordTrace]
  refine ⟨48301772670233044588630075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64402363560310726118173433 48301772670233044588630075)
  ·
    refine ⟨72452659005349566882945113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48301772670233044588630075 72452659005349566882945113)
    ·
      refine ⟨54339494254012175162208835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72452659005349566882945113 54339494254012175162208835)
      ·
        refine ⟨81509241381018262743313253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54339494254012175162208835 81509241381018262743313253)
        ·
          refine ⟨15282982758940924264371235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81509241381018262743313253 15282982758940924264371235)
          ·
            refine ⟨22924474138411386396556853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15282982758940924264371235 22924474138411386396556853)
            ·
              refine ⟨2149169450476067474677205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22924474138411386396556853 2149169450476067474677205)
              ·
                refine ⟨50371158995532831437747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2149169450476067474677205 50371158995532831437747)
                ·
                  rfl

theorem cell23_2648632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 7].length) (baseStart_2648632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648632 prefixEnd_2648632 := by exact prefixLift 2648632
  have htrace : WordTrace (prefixWord ++ tailWord_2648632) baseStart_2648632 baseEnd_2648632 := by
    simpa [prefixWord, tailWord_2648632, baseEnd_2648632] using wordTrace_append hprefix tailTrace_2648632
  have hstable : (prefixWord ++ tailWord_2648632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648632).length < 2 ^ (prefixWord ++ tailWord_2648632).sum := by decide
  have hdescent : baseEnd_2648632 < baseStart_2648632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648653 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_2648653 : Nat := 118140960795 + 2648653 * 2 ^ 59
def prefixEnd_2648653 : Nat := 4983230072969 + 3 ^ 40 * 2648653 * 2
def baseEnd_2648653 : Nat := 453344025324376955552191

theorem tailTrace_2648653 : CollatzResearch.WordTrace tailWord_2648653 prefixEnd_2648653 453344025324376955552191 := by
  unfold tailWord_2648653
  simp only [CollatzResearch.WordTrace]
  refine ⟨96604311273390009763774613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64402874182260006509183075 96604311273390009763774613)
  ·
    refine ⟨4528327090940156707676935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96604311273390009763774613 4528327090940156707676935)
    ·
      refine ⟨6792490636410235061515403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4528327090940156707676935 6792490636410235061515403)
      ·
        refine ⟨10188735954615352592273105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6792490636410235061515403 10188735954615352592273105)
        ·
          refine ⟨7641551965961514444204829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10188735954615352592273105 7641551965961514444204829)
          ·
            refine ⟨2865581987235567916576811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7641551965961514444204829 2865581987235567916576811)
            ·
              refine ⟨4298372980853351874865217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865581987235567916576811 4298372980853351874865217)
              ·
                refine ⟨3223779735640013906148913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4298372980853351874865217 3223779735640013906148913)
                ·
                  refine ⟨2417834801730010429611685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3223779735640013906148913 2417834801730010429611685)
                  ·
                    refine ⟨453344025324376955552191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417834801730010429611685 453344025324376955552191)
                    ·
                      rfl

theorem cell23_2648653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_2648653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648653 prefixEnd_2648653 := by exact prefixLift 2648653
  have htrace : WordTrace (prefixWord ++ tailWord_2648653) baseStart_2648653 baseEnd_2648653 := by
    simpa [prefixWord, tailWord_2648653, baseEnd_2648653] using wordTrace_append hprefix tailTrace_2648653
  have hstable : (prefixWord ++ tailWord_2648653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648653).length < 2 ^ (prefixWord ++ tailWord_2648653).sum := by decide
  have hdescent : baseEnd_2648653 < baseStart_2648653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648670 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2648670 : Nat := 118140960795 + 2648670 * 2 ^ 59
def prefixEnd_2648670 : Nat := 4983230072969 + 3 ^ 40 * 2648670 * 2
def baseEnd_2648670 : Nat := 453346935048085766714665

theorem tailTrace_2648670 : CollatzResearch.WordTrace tailWord_2648670 prefixEnd_2648670 453346935048085766714665 := by
  unfold tailWord_2648670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12075616414291052708392933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64403287542885614444762309 12075616414291052708392933)
  ·
    refine ⟨2264178077679572382823675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12075616414291052708392933 2264178077679572382823675)
    ·
      refine ⟨3396267116519358574235513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2264178077679572382823675 3396267116519358574235513)
      ·
        refine ⟨2547200337389518930676635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3396267116519358574235513 2547200337389518930676635)
        ·
          refine ⟨3820800506084278396014953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547200337389518930676635 3820800506084278396014953)
          ·
            refine ⟨2865600379563208797011215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3820800506084278396014953 2865600379563208797011215)
            ·
              refine ⟨4298400569344813195516823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865600379563208797011215 4298400569344813195516823)
              ·
                refine ⟨6447600854017219793275235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298400569344813195516823 6447600854017219793275235)
                ·
                  refine ⟨9671401281025829689912853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6447600854017219793275235 9671401281025829689912853)
                  ·
                    refine ⟨453346935048085766714665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9671401281025829689912853 453346935048085766714665)
                    ·
                      rfl

theorem cell23_2648670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2648670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648670 prefixEnd_2648670 := by exact prefixLift 2648670
  have htrace : WordTrace (prefixWord ++ tailWord_2648670) baseStart_2648670 baseEnd_2648670 := by
    simpa [prefixWord, tailWord_2648670, baseEnd_2648670] using wordTrace_append hprefix tailTrace_2648670
  have hstable : (prefixWord ++ tailWord_2648670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648670).length < 2 ^ (prefixWord ++ tailWord_2648670).sum := by decide
  have hdescent : baseEnd_2648670 < baseStart_2648670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648694 : List Nat := [5, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_2648694 : Nat := 118140960795 + 2648694 * 2 ^ 59
def prefixEnd_2648694 : Nat := 4983230072969 + 3 ^ 40 * 2648694 * 2
def baseEnd_2648694 : Nat := 1360053128679965206243885

theorem tailTrace_2648694 : CollatzResearch.WordTrace tailWord_2648694 prefixEnd_2648694 1360053128679965206243885 := by
  unfold tailWord_2648694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037862916640092110376071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64403871110827649177344757 6037862916640092110376071)
  ·
    refine ⟨9056794374960138165564107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6037862916640092110376071 9056794374960138165564107)
    ·
      refine ⟨13585191562440207248346161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9056794374960138165564107 13585191562440207248346161)
      ·
        refine ⟨10188893671830155436259621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13585191562440207248346161 10188893671830155436259621)
        ·
          refine ⟨1910417563468154144298679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10188893671830155436259621 1910417563468154144298679)
          ·
            refine ⟨2865626345202231216448019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910417563468154144298679 2865626345202231216448019)
            ·
              refine ⟨4298439517803346824672029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865626345202231216448019 4298439517803346824672029)
              ·
                refine ⟨1611914819176255059252011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4298439517803346824672029 1611914819176255059252011)
                ·
                  refine ⟨2417872228764382588878017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611914819176255059252011 2417872228764382588878017)
                  ·
                    refine ⟨1813404171573286941658513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2417872228764382588878017 1813404171573286941658513)
                    ·
                      refine ⟨1360053128679965206243885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813404171573286941658513 1360053128679965206243885)
                      ·
                        rfl

theorem cell23_2648694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_2648694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648694 prefixEnd_2648694 := by exact prefixLift 2648694
  have htrace : WordTrace (prefixWord ++ tailWord_2648694) baseStart_2648694 baseEnd_2648694 := by
    simpa [prefixWord, tailWord_2648694, baseEnd_2648694] using wordTrace_append hprefix tailTrace_2648694
  have hstable : (prefixWord ++ tailWord_2648694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648694).length < 2 ^ (prefixWord ++ tailWord_2648694).sum := by decide
  have hdescent : baseEnd_2648694 < baseStart_2648694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648762 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_2648762 : Nat := 118140960795 + 2648762 * 2 ^ 59
def prefixEnd_2648762 : Nat := 4983230072969 + 3 ^ 40 * 2648762 * 2
def baseEnd_2648762 : Nat := 1360088045364470940193571

theorem tailTrace_2648762 : CollatzResearch.WordTrace tailWord_2648762 prefixEnd_2648762 1360088045364470940193571 := by
  unfold tailWord_2648762
  simp only [CollatzResearch.WordTrace]
  refine ⟨24152071707498780344873135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64405524553330080919661693 24152071707498780344873135)
  ·
    refine ⟨36228107561248170517309703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24152071707498780344873135 36228107561248170517309703)
    ·
      refine ⟨54342161341872255775964555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36228107561248170517309703 54342161341872255775964555)
      ·
        refine ⟨81513242012808383663946833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54342161341872255775964555 81513242012808383663946833)
        ·
          refine ⟨61134931509606287747960125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81513242012808383663946833 61134931509606287747960125)
          ·
            refine ⟨22925599316102357905485047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61134931509606287747960125 22925599316102357905485047)
            ·
              refine ⟨34388398974153536858227571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22925599316102357905485047 34388398974153536858227571)
              ·
                refine ⟨51582598461230305287341357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34388398974153536858227571 51582598461230305287341357)
                ·
                  refine ⟨19343474422961364482753009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51582598461230305287341357 19343474422961364482753009)
                  ·
                    refine ⟨14507605817221023362064757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19343474422961364482753009 14507605817221023362064757)
                    ·
                      refine ⟨1360088045364470940193571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14507605817221023362064757 1360088045364470940193571)
                      ·
                        rfl

theorem cell23_2648762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_2648762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648762 prefixEnd_2648762 := by exact prefixLift 2648762
  have htrace : WordTrace (prefixWord ++ tailWord_2648762) baseStart_2648762 baseEnd_2648762 := by
    simpa [prefixWord, tailWord_2648762, baseEnd_2648762] using wordTrace_append hprefix tailTrace_2648762
  have hstable : (prefixWord ++ tailWord_2648762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648762).length < 2 ^ (prefixWord ++ tailWord_2648762).sum := by decide
  have hdescent : baseEnd_2648762 < baseStart_2648762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648799 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 5, 4]
def baseStart_2648799 : Nat := 118140960795 + 2648799 * 2 ^ 59
def prefixEnd_2648799 : Nat := 4983230072969 + 3 ^ 40 * 2648799 * 2
def baseEnd_2648799 : Nat := 453369014716229098476967

theorem tailTrace_2648799 : CollatzResearch.WordTrace tailWord_2648799 prefixEnd_2648799 453369014716229098476967 := by
  unfold tailWord_2648799
  simp only [CollatzResearch.WordTrace]
  refine ⟨96609636330861076698589451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64406424220574051132392967 96609636330861076698589451)
  ·
    refine ⟨144914454496291615047884177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96609636330861076698589451 144914454496291615047884177)
    ·
      refine ⟨108685840872218711285913133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144914454496291615047884177 108685840872218711285913133)
      ·
        refine ⟨40757190327082016732217425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108685840872218711285913133 40757190327082016732217425)
        ·
          refine ⟨30567892745311512549163069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40757190327082016732217425 30567892745311512549163069)
          ·
            refine ⟨11462959779491817205936151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30567892745311512549163069 11462959779491817205936151)
            ·
              refine ⟨17194439669237725808904227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11462959779491817205936151 17194439669237725808904227)
              ·
                refine ⟨25791659503856588713356341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17194439669237725808904227 25791659503856588713356341)
                ·
                  refine ⟨2417968078486555191877157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25791659503856588713356341 2417968078486555191877157)
                  ·
                    refine ⟨453369014716229098476967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417968078486555191877157 453369014716229098476967)
                    ·
                      rfl

theorem cell23_2648799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 4].length) (baseStart_2648799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648799 prefixEnd_2648799 := by exact prefixLift 2648799
  have htrace : WordTrace (prefixWord ++ tailWord_2648799) baseStart_2648799 baseEnd_2648799 := by
    simpa [prefixWord, tailWord_2648799, baseEnd_2648799] using wordTrace_append hprefix tailTrace_2648799
  have hstable : (prefixWord ++ tailWord_2648799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648799).length < 2 ^ (prefixWord ++ tailWord_2648799).sum := by decide
  have hdescent : baseEnd_2648799 < baseStart_2648799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648812 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 8]
def baseStart_2648812 : Nat := 118140960795 + 2648812 * 2 ^ 59
def prefixEnd_2648812 : Nat := 4983230072969 + 3 ^ 40 * 2648812 * 2
def baseEnd_2648812 : Nat := 151123746599688416063149

theorem tailTrace_2648812 : CollatzResearch.WordTrace tailWord_2648812 prefixEnd_2648812 151123746599688416063149 := by
  unfold tailWord_2648812
  simp only [CollatzResearch.WordTrace]
  refine ⟨48305055239906989959406345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64406740319875986612541793 48305055239906989959406345)
  ·
    refine ⟨36228791429930242469554759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48305055239906989959406345 36228791429930242469554759)
    ·
      refine ⟨54343187144895363704332139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36228791429930242469554759 54343187144895363704332139)
      ·
        refine ⟨81514780717343045556498209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54343187144895363704332139 81514780717343045556498209)
        ·
          refine ⟨61136085538007284167373657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81514780717343045556498209 61136085538007284167373657)
          ·
            refine ⟨45852064153505463125530243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61136085538007284167373657 45852064153505463125530243)
            ·
              refine ⟨68778096230258194688295365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45852064153505463125530243 68778096230258194688295365)
              ·
                refine ⟨12895893043173411504055381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68778096230258194688295365 12895893043173411504055381)
                ·
                  refine ⟨151123746599688416063149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12895893043173411504055381 151123746599688416063149)
                  ·
                    rfl

theorem cell23_2648812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_2648812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648812 prefixEnd_2648812 := by exact prefixLift 2648812
  have htrace : WordTrace (prefixWord ++ tailWord_2648812) baseStart_2648812 baseEnd_2648812 := by
    simpa [prefixWord, tailWord_2648812, baseEnd_2648812] using wordTrace_append hprefix tailTrace_2648812
  have hstable : (prefixWord ++ tailWord_2648812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648812).length < 2 ^ (prefixWord ++ tailWord_2648812).sum := by decide
  have hdescent : baseEnd_2648812 < baseStart_2648812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648883 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 2, 3, 2]
def baseStart_2648883 : Nat := 118140960795 + 2648883 * 2 ^ 59
def prefixEnd_2648883 : Nat := 4983230072969 + 3 ^ 40 * 2648883 * 2
def baseEnd_2648883 : Nat := 1360150176523664966780515

theorem tailTrace_2648883 : CollatzResearch.WordTrace tailWord_2648883 prefixEnd_2648883 1360150176523664966780515 := by
  unfold tailWord_2648883
  simp only [CollatzResearch.WordTrace]
  refine ⟨96612700062556759044647303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64408466708371172696431535 96612700062556759044647303)
  ·
    refine ⟨144919050093835138566970955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96612700062556759044647303 144919050093835138566970955)
    ·
      refine ⟨217378575140752707850456433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144919050093835138566970955 217378575140752707850456433)
      ·
        refine ⟨163033931355564530887842325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217378575140752707850456433 163033931355564530887842325)
        ·
          refine ⟨7642215532292087385367609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163033931355564530887842325 7642215532292087385367609)
          ·
            refine ⟨5731661649219065539025707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7642215532292087385367609 5731661649219065539025707)
            ·
              refine ⟨8597492473828598308538561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731661649219065539025707 8597492473828598308538561)
              ·
                refine ⟨6448119355371448731403921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8597492473828598308538561 6448119355371448731403921)
                ·
                  refine ⟨4836089516528586548552941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6448119355371448731403921 4836089516528586548552941)
                  ·
                    refine ⟨1813533568698219955707353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4836089516528586548552941 1813533568698219955707353)
                    ·
                      refine ⟨1360150176523664966780515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813533568698219955707353 1360150176523664966780515)
                      ·
                        rfl

theorem cell23_2648883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 3, 2].length) (baseStart_2648883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648883 prefixEnd_2648883 := by exact prefixLift 2648883
  have htrace : WordTrace (prefixWord ++ tailWord_2648883) baseStart_2648883 baseEnd_2648883 := by
    simpa [prefixWord, tailWord_2648883, baseEnd_2648883] using wordTrace_append hprefix tailTrace_2648883
  have hstable : (prefixWord ++ tailWord_2648883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648883).length < 2 ^ (prefixWord ++ tailWord_2648883).sum := by decide
  have hdescent : baseEnd_2648883 < baseStart_2648883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648890 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_2648890 : Nat := 118140960795 + 2648890 * 2 ^ 59
def prefixEnd_2648890 : Nat := 4983230072969 + 3 ^ 40 * 2648890 * 2
def baseEnd_2648890 : Nat := 1360153770888246439392983

theorem tailTrace_2648890 : CollatzResearch.WordTrace tailWord_2648890 prefixEnd_2648890 1360153770888246439392983 := by
  unfold tailWord_2648890
  simp only [CollatzResearch.WordTrace]
  refine ⟨24153238843382849810038031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64408636915687599493434749 24153238843382849810038031)
  ·
    refine ⟨36229858265074274715057047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24153238843382849810038031 36229858265074274715057047)
    ·
      refine ⟨54344787397611412072585571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36229858265074274715057047 54344787397611412072585571)
      ·
        refine ⟨81517181096417118108878357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54344787397611412072585571 81517181096417118108878357)
        ·
          refine ⟨3821117863894552411353673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81517181096417118108878357 3821117863894552411353673)
          ·
            refine ⟨2865838397920914308515255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3821117863894552411353673 2865838397920914308515255)
            ·
              refine ⟨4298757596881371462772883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2865838397920914308515255 4298757596881371462772883)
              ·
                refine ⟨6448136395322057194159325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298757596881371462772883 6448136395322057194159325)
                ·
                  refine ⟨2418051148245771447809747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6448136395322057194159325 2418051148245771447809747)
                  ·
                    refine ⟨3627076722368657171714621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2418051148245771447809747 3627076722368657171714621)
                    ·
                      refine ⟨1360153770888246439392983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3627076722368657171714621 1360153770888246439392983)
                      ·
                        rfl

theorem cell23_2648890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_2648890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648890 prefixEnd_2648890 := by exact prefixLift 2648890
  have htrace : WordTrace (prefixWord ++ tailWord_2648890) baseStart_2648890 baseEnd_2648890 := by
    simpa [prefixWord, tailWord_2648890, baseEnd_2648890] using wordTrace_append hprefix tailTrace_2648890
  have hstable : (prefixWord ++ tailWord_2648890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648890).length < 2 ^ (prefixWord ++ tailWord_2648890).sum := by decide
  have hdescent : baseEnd_2648890 < baseStart_2648890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648897 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 6]
def baseStart_2648897 : Nat := 118140960795 + 2648897 * 2 ^ 59
def prefixEnd_2648897 : Nat := 4983230072969 + 3 ^ 40 * 2648897 * 2
def baseEnd_2648897 : Nat := 151128596139203101333939

theorem tailTrace_2648897 : CollatzResearch.WordTrace tailWord_2648897 prefixEnd_2648897 151128596139203101333939 := by
  unfold tailWord_2648897
  simp only [CollatzResearch.WordTrace]
  refine ⟨96613210684506039435656945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64408807123004026290437963 96613210684506039435656945)
  ·
    refine ⟨72459908013379529576742709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96613210684506039435656945 72459908013379529576742709)
    ·
      refine ⟨6793116376254330897819629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72459908013379529576742709 6793116376254330897819629)
      ·
        refine ⟨2547418641095374086682361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6793116376254330897819629 2547418641095374086682361)
        ·
          refine ⟨1910563980821530565011771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2547418641095374086682361 1910563980821530565011771)
          ·
            refine ⟨2865845971232295847517657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910563980821530565011771 2865845971232295847517657)
            ·
              refine ⟨2149384478424221885638243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2865845971232295847517657 2149384478424221885638243)
              ·
                refine ⟨3224076717636332828457365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149384478424221885638243 3224076717636332828457365)
                ·
                  refine ⟨151128596139203101333939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3224076717636332828457365 151128596139203101333939)
                  ·
                    rfl

theorem cell23_2648897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 6].length) (baseStart_2648897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648897 prefixEnd_2648897 := by exact prefixLift 2648897
  have htrace : WordTrace (prefixWord ++ tailWord_2648897) baseStart_2648897 baseEnd_2648897 := by
    simpa [prefixWord, tailWord_2648897, baseEnd_2648897] using wordTrace_append hprefix tailTrace_2648897
  have hstable : (prefixWord ++ tailWord_2648897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648897).length < 2 ^ (prefixWord ++ tailWord_2648897).sum := by decide
  have hdescent : baseEnd_2648897 < baseStart_2648897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648899 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 5]
def baseStart_2648899 : Nat := 118140960795 + 2648899 * 2 ^ 59
def prefixEnd_2648899 : Nat := 4983230072969 + 3 ^ 40 * 2648899 * 2
def baseEnd_2648899 : Nat := 1360158392214136904180441

theorem tailTrace_2648899 : CollatzResearch.WordTrace tailWord_2648899 prefixEnd_2648899 1360158392214136904180441 := by
  unfold tailWord_2648899
  simp only [CollatzResearch.WordTrace]
  refine ⟨96613283630498793777229751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64408855753665862518153167 96613283630498793777229751)
  ·
    refine ⟨144919925445748190665844627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96613283630498793777229751 144919925445748190665844627)
    ·
      refine ⟨217379888168622285998766941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144919925445748190665844627 217379888168622285998766941)
      ·
        refine ⟨81517458063233357249537603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217379888168622285998766941 81517458063233357249537603)
        ·
          refine ⟨122276187094850035874306405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81517458063233357249537603 122276187094850035874306405)
          ·
            refine ⟨22926785080284381726432451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122276187094850035874306405 22926785080284381726432451)
            ·
              refine ⟨34390177620426572589648677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22926785080284381726432451 34390177620426572589648677)
              ·
                refine ⟨6448158303829982360559127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34390177620426572589648677 6448158303829982360559127)
                ·
                  refine ⟨9672237455744973540838691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448158303829982360559127 9672237455744973540838691)
                  ·
                    refine ⟨14508356183617460311258037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9672237455744973540838691 14508356183617460311258037)
                    ·
                      refine ⟨1360158392214136904180441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14508356183617460311258037 1360158392214136904180441)
                      ·
                        rfl

theorem cell23_2648899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_2648899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648899 prefixEnd_2648899 := by exact prefixLift 2648899
  have htrace : WordTrace (prefixWord ++ tailWord_2648899) baseStart_2648899 baseEnd_2648899 := by
    simpa [prefixWord, tailWord_2648899, baseEnd_2648899] using wordTrace_append hprefix tailTrace_2648899
  have hstable : (prefixWord ++ tailWord_2648899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648899).length < 2 ^ (prefixWord ++ tailWord_2648899).sum := by decide
  have hdescent : baseEnd_2648899 < baseStart_2648899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648919 : List Nat := [1, 1, 3, 2, 4, 1, 2, 9]
def baseStart_2648919 : Nat := 118140960795 + 2648919 * 2 ^ 59
def prefixEnd_2648919 : Nat := 4983230072969 + 3 ^ 40 * 2648919 * 2
def baseEnd_2648919 : Nat := 50376617104712104664087

theorem tailTrace_2648919 : CollatzResearch.WordTrace tailWord_2648919 prefixEnd_2648919 50376617104712104664087 := by
  unfold tailWord_2648919
  simp only [CollatzResearch.WordTrace]
  refine ⟨96614013090426337192957811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64409342060284224795305207 96614013090426337192957811)
  ·
    refine ⟨144921019635639505789436717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96614013090426337192957811 144921019635639505789436717)
    ·
      refine ⟨54345382363364814671038769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144921019635639505789436717 54345382363364814671038769)
      ·
        refine ⟨40759036772523611003279077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54345382363364814671038769 40759036772523611003279077)
        ·
          refine ⟨7642319394848177063114827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40759036772523611003279077 7642319394848177063114827)
          ·
            refine ⟨11463479092272265594672241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7642319394848177063114827 11463479092272265594672241)
            ·
              refine ⟨8597609319204199196004181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11463479092272265594672241 8597609319204199196004181)
              ·
                refine ⟨50376617104712104664087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8597609319204199196004181 50376617104712104664087)
                ·
                  rfl

theorem cell23_2648919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 9].length) (baseStart_2648919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648919 prefixEnd_2648919 := by exact prefixLift 2648919
  have htrace : WordTrace (prefixWord ++ tailWord_2648919) baseStart_2648919 baseEnd_2648919 := by
    simpa [prefixWord, tailWord_2648919, baseEnd_2648919] using wordTrace_append hprefix tailTrace_2648919
  have hstable : (prefixWord ++ tailWord_2648919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648919).length < 2 ^ (prefixWord ++ tailWord_2648919).sum := by decide
  have hdescent : baseEnd_2648919 < baseStart_2648919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648947 : List Nat := [1, 1, 1, 2, 2, 1, 8, 2, 1, 2, 2]
def baseStart_2648947 : Nat := 118140960795 + 2648947 * 2 ^ 59
def prefixEnd_2648947 : Nat := 4983230072969 + 3 ^ 40 * 2648947 * 2
def baseEnd_2648947 : Nat := 1360183039285552716380221

theorem tailTrace_2648947 : CollatzResearch.WordTrace tailWord_2648947 prefixEnd_2648947 1360183039285552716380221 := by
  unfold tailWord_2648947
  simp only [CollatzResearch.WordTrace]
  refine ⟨96615034334324897974977095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64410022889549931983318063 96615034334324897974977095)
  ·
    refine ⟨144922551501487346962465643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96615034334324897974977095 144922551501487346962465643)
    ·
      refine ⟨217383827252231020443698465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144922551501487346962465643 217383827252231020443698465)
      ·
        refine ⟨163037870439173265332773849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217383827252231020443698465 163037870439173265332773849)
        ·
          refine ⟨122278402829379948999580387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163037870439173265332773849 122278402829379948999580387)
          ·
            refine ⟨183417604244069923499370581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122278402829379948999580387 183417604244069923499370581)
            ·
              refine ⟨2149425049735194416008249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 183417604244069923499370581 2149425049735194416008249)
              ·
                refine ⟨1612068787301395812006187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2149425049735194416008249 1612068787301395812006187)
                ·
                  refine ⟨2418103180952093718009281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612068787301395812006187 2418103180952093718009281)
                  ·
                    refine ⟨1813577385714070288506961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418103180952093718009281 1813577385714070288506961)
                    ·
                      refine ⟨1360183039285552716380221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813577385714070288506961 1360183039285552716380221)
                      ·
                        rfl

theorem cell23_2648947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 2, 2].length) (baseStart_2648947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648947 prefixEnd_2648947 := by exact prefixLift 2648947
  have htrace : WordTrace (prefixWord ++ tailWord_2648947) baseStart_2648947 baseEnd_2648947 := by
    simpa [prefixWord, tailWord_2648947, baseEnd_2648947] using wordTrace_append hprefix tailTrace_2648947
  have hstable : (prefixWord ++ tailWord_2648947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648947).length < 2 ^ (prefixWord ++ tailWord_2648947).sum := by decide
  have hdescent : baseEnd_2648947 < baseStart_2648947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2648963 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 3]
def baseStart_2648963 : Nat := 118140960795 + 2648963 * 2 ^ 59
def prefixEnd_2648963 : Nat := 4983230072969 + 3 ^ 40 * 2648963 * 2
def baseEnd_2648963 : Nat := 1360191254976024653780147

theorem tailTrace_2648963 : CollatzResearch.WordTrace tailWord_2648963 prefixEnd_2648963 1360191254976024653780147 := by
  unfold tailWord_2648963
  simp only [CollatzResearch.WordTrace]
  refine ⟨96615617902266932707559543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64410411934844621805039695 96615617902266932707559543)
  ·
    refine ⟨144923426853400399061339315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96615617902266932707559543 144923426853400399061339315)
    ·
      refine ⟨217385140280100598592008973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144923426853400399061339315 217385140280100598592008973)
      ·
        refine ⟨81519427605037724472003365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217385140280100598592008973 81519427605037724472003365)
        ·
          refine ⟨15284892675944573338500631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81519427605037724472003365 15284892675944573338500631)
          ·
            refine ⟨22927339013916860007750947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15284892675944573338500631 22927339013916860007750947)
            ·
              refine ⟨34391008520875290011626421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22927339013916860007750947 34391008520875290011626421)
              ·
                refine ⟨3224157048832058438589977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34391008520875290011626421 3224157048832058438589977)
                ·
                  refine ⟨2418117786624043828942483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3224157048832058438589977 2418117786624043828942483)
                  ·
                    refine ⟨3627176679936065743413725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2418117786624043828942483 3627176679936065743413725)
                    ·
                      refine ⟨1360191254976024653780147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3627176679936065743413725 1360191254976024653780147)
                      ·
                        rfl

theorem cell23_2648963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_2648963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2648963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2648963 prefixEnd_2648963 := by exact prefixLift 2648963
  have htrace : WordTrace (prefixWord ++ tailWord_2648963) baseStart_2648963 baseEnd_2648963 := by
    simpa [prefixWord, tailWord_2648963, baseEnd_2648963] using wordTrace_append hprefix tailTrace_2648963
  have hstable : (prefixWord ++ tailWord_2648963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2648963).length < 2 ^ (prefixWord ++ tailWord_2648963).sum := by decide
  have hdescent : baseEnd_2648963 < baseStart_2648963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2648963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 4, 2, 2]
def baseStart_2649003 : Nat := 118140960795 + 2649003 * 2 ^ 59
def prefixEnd_2649003 : Nat := 4983230072969 + 3 ^ 40 * 2649003 * 2
def baseEnd_2649003 : Nat := 1360211794202204497279963

theorem tailTrace_2649003 : CollatzResearch.WordTrace tailWord_2649003 prefixEnd_2649003 1360211794202204497279963 := by
  unfold tailWord_2649003
  simp only [CollatzResearch.WordTrace]
  refine ⟨96617076822122019539015663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64411384548081346359343775 96617076822122019539015663)
  ·
    refine ⟨144925615233183029308523495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96617076822122019539015663 144925615233183029308523495)
    ·
      refine ⟨217388422849774543962785243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144925615233183029308523495 217388422849774543962785243)
      ·
        refine ⟨326082634274661815944177865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217388422849774543962785243 326082634274661815944177865)
        ·
          refine ⟨244561975705996361958133399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326082634274661815944177865 244561975705996361958133399)
          ·
            refine ⟨366842963558994542937200099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244561975705996361958133399 366842963558994542937200099)
            ·
              refine ⟨550264445338491814405800149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366842963558994542937200099 550264445338491814405800149)
              ·
                refine ⟨12896822937620901900135941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 550264445338491814405800149 12896822937620901900135941)
                ·
                  refine ⟨2418154300803919106275489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12896822937620901900135941 2418154300803919106275489)
                  ·
                    refine ⟨1813615725602939329706617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418154300803919106275489 1813615725602939329706617)
                    ·
                      refine ⟨1360211794202204497279963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813615725602939329706617 1360211794202204497279963)
                      ·
                        rfl

theorem cell23_2649003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 2, 2].length) (baseStart_2649003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649003 prefixEnd_2649003 := by exact prefixLift 2649003
  have htrace : WordTrace (prefixWord ++ tailWord_2649003) baseStart_2649003 baseEnd_2649003 := by
    simpa [prefixWord, tailWord_2649003, baseEnd_2649003] using wordTrace_append hprefix tailTrace_2649003
  have hstable : (prefixWord ++ tailWord_2649003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649003).length < 2 ^ (prefixWord ++ tailWord_2649003).sum := by decide
  have hdescent : baseEnd_2649003 < baseStart_2649003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649016 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_2649016 : Nat := 118140960795 + 2649016 * 2 ^ 59
def prefixEnd_2649016 : Nat := 4983230072969 + 3 ^ 40 * 2649016 * 2
def baseEnd_2649016 : Nat := 1360218469450712946417403

theorem tailTrace_2649016 : CollatzResearch.WordTrace tailWord_2649016 prefixEnd_2649016 1360218469450712946417403 := by
  unfold tailWord_2649016
  simp only [CollatzResearch.WordTrace]
  refine ⟨48308775485537461379619451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64411700647383281839492601 48308775485537461379619451)
  ·
    refine ⟨72463163228306192069429177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48308775485537461379619451 72463163228306192069429177)
    ·
      refine ⟨54347372421229644052071883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72463163228306192069429177 54347372421229644052071883)
      ·
        refine ⟨81521058631844466078107825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54347372421229644052071883 81521058631844466078107825)
        ·
          refine ⟨61140793973883349558580869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81521058631844466078107825 61140793973883349558580869)
          ·
            refine ⟨11463898870103128042233913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61140793973883349558580869 11463898870103128042233913)
            ·
              refine ⟨8597924152577346031675435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11463898870103128042233913 8597924152577346031675435)
              ·
                refine ⟨12896886228866019047513153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8597924152577346031675435 12896886228866019047513153)
                ·
                  refine ⟨9672664671649514285634865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12896886228866019047513153 9672664671649514285634865)
                  ·
                    refine ⟨7254498503737135714226149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9672664671649514285634865 7254498503737135714226149)
                    ·
                      refine ⟨1360218469450712946417403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7254498503737135714226149 1360218469450712946417403)
                      ·
                        rfl

theorem cell23_2649016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_2649016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649016 prefixEnd_2649016 := by exact prefixLift 2649016
  have htrace : WordTrace (prefixWord ++ tailWord_2649016) baseStart_2649016 baseEnd_2649016 := by
    simpa [prefixWord, tailWord_2649016, baseEnd_2649016] using wordTrace_append hprefix tailTrace_2649016
  have hstable : (prefixWord ++ tailWord_2649016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649016).length < 2 ^ (prefixWord ++ tailWord_2649016).sum := by decide
  have hdescent : baseEnd_2649016 < baseStart_2649016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649029 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_2649029 : Nat := 118140960795 + 2649029 * 2 ^ 59
def prefixEnd_2649029 : Nat := 4983230072969 + 3 ^ 40 * 2649029 * 2
def baseEnd_2649029 : Nat := 1360225144699221395554843

theorem tailTrace_2649029 : CollatzResearch.WordTrace tailWord_2649029 prefixEnd_2649029 1360225144699221395554843 := by
  unfold tailWord_2649029
  simp only [CollatzResearch.WordTrace]
  refine ⟨96618025120027825979462141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64412016746685217319641427 96618025120027825979462141)
  ·
    refine ⟨36231759420010434742298303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96618025120027825979462141 36231759420010434742298303)
    ·
      refine ⟨54347639130015652113447455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36231759420010434742298303 54347639130015652113447455)
      ·
        refine ⟨81521458695023478170171183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54347639130015652113447455 81521458695023478170171183)
        ·
          refine ⟨122282188042535217255256775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81521458695023478170171183 122282188042535217255256775)
          ·
            refine ⟨183423282063802825882885163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122282188042535217255256775 183423282063802825882885163)
            ·
              refine ⟨275134923095704238824327745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183423282063802825882885163 275134923095704238824327745)
              ·
                refine ⟨206351192321778179118245809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275134923095704238824327745 206351192321778179118245809)
                ·
                  refine ⟨154763394241333634338684357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206351192321778179118245809 154763394241333634338684357)
                  ·
                    refine ⟨29018136420250056438503317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154763394241333634338684357 29018136420250056438503317)
                    ·
                      refine ⟨1360225144699221395554843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29018136420250056438503317 1360225144699221395554843)
                      ·
                        rfl

theorem cell23_2649029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_2649029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649029 prefixEnd_2649029 := by exact prefixLift 2649029
  have htrace : WordTrace (prefixWord ++ tailWord_2649029) baseStart_2649029 baseEnd_2649029 := by
    simpa [prefixWord, tailWord_2649029, baseEnd_2649029] using wordTrace_append hprefix tailTrace_2649029
  have hstable : (prefixWord ++ tailWord_2649029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649029).length < 2 ^ (prefixWord ++ tailWord_2649029).sum := by decide
  have hdescent : baseEnd_2649029 < baseStart_2649029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649066 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_2649066 : Nat := 118140960795 + 2649066 * 2 ^ 59
def prefixEnd_2649066 : Nat := 4983230072969 + 3 ^ 40 * 2649066 * 2
def baseEnd_2649066 : Nat := 1360244143483437750792173

theorem tailTrace_2649066 : CollatzResearch.WordTrace tailWord_2649066 prefixEnd_2649066 1360244143483437750792173 := by
  unfold tailWord_2649066
  simp only [CollatzResearch.WordTrace]
  refine ⟨24154843655223445324639763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64412916413929187532372701 24154843655223445324639763)
  ·
    refine ⟨36232265482835167986959645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24154843655223445324639763 36232265482835167986959645)
    ·
      refine ⟨13587099556063187995109867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36232265482835167986959645 13587099556063187995109867)
      ·
        refine ⟨20380649334094781992664801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13587099556063187995109867 20380649334094781992664801)
        ·
          refine ⟨15285487000571086494498601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20380649334094781992664801 15285487000571086494498601)
          ·
            refine ⟨11464115250428314870873951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15285487000571086494498601 11464115250428314870873951)
            ·
              refine ⟨17196172875642472306310927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11464115250428314870873951 17196172875642472306310927)
              ·
                refine ⟨25794259313463708459466391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17196172875642472306310927 25794259313463708459466391)
                ·
                  refine ⟨38691388970195562689199587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25794259313463708459466391 38691388970195562689199587)
                  ·
                    refine ⟨58037083455293344033799381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38691388970195562689199587 58037083455293344033799381)
                    ·
                      refine ⟨1360244143483437750792173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58037083455293344033799381 1360244143483437750792173)
                      ·
                        rfl

theorem cell23_2649066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_2649066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649066 prefixEnd_2649066 := by exact prefixLift 2649066
  have htrace : WordTrace (prefixWord ++ tailWord_2649066) baseStart_2649066 baseEnd_2649066 := by
    simpa [prefixWord, tailWord_2649066, baseEnd_2649066] using wordTrace_append hprefix tailTrace_2649066
  have hstable : (prefixWord ++ tailWord_2649066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649066).length < 2 ^ (prefixWord ++ tailWord_2649066).sum := by decide
  have hdescent : baseEnd_2649066 < baseStart_2649066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649093 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_2649093 : Nat := 118140960795 + 2649093 * 2 ^ 59
def prefixEnd_2649093 : Nat := 4983230072969 + 3 ^ 40 * 2649093 * 2
def baseEnd_2649093 : Nat := 1360258007461109145154549

theorem tailTrace_2649093 : CollatzResearch.WordTrace tailWord_2649093 prefixEnd_2649093 1360258007461109145154549 := by
  unfold tailWord_2649093
  simp only [CollatzResearch.WordTrace]
  refine ⟨96620359391795964909791933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64413572927863976606527955 96620359391795964909791933)
  ·
    refine ⟨36232634771923486841171975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96620359391795964909791933 36232634771923486841171975)
    ·
      refine ⟨54348952157885230261757963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36232634771923486841171975 54348952157885230261757963)
      ·
        refine ⟨81523428236827845392636945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54348952157885230261757963 81523428236827845392636945)
        ·
          refine ⟨61142571177620884044477709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81523428236827845392636945 61142571177620884044477709)
          ·
            refine ⟨22928464191607831516679141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61142571177620884044477709 22928464191607831516679141)
            ·
              refine ⟨4299087035926468409377339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22928464191607831516679141 4299087035926468409377339)
              ·
                refine ⟨6448630553889702614066009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299087035926468409377339 6448630553889702614066009)
                ·
                  refine ⟨4836472915417276960549507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6448630553889702614066009 4836472915417276960549507)
                  ·
                    refine ⟨7254709373125915440824261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4836472915417276960549507 7254709373125915440824261)
                    ·
                      refine ⟨1360258007461109145154549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7254709373125915440824261 1360258007461109145154549)
                      ·
                        rfl

theorem cell23_2649093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_2649093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649093 prefixEnd_2649093 := by exact prefixLift 2649093
  have htrace : WordTrace (prefixWord ++ tailWord_2649093) baseStart_2649093 baseEnd_2649093 := by
    simpa [prefixWord, tailWord_2649093, baseEnd_2649093] using wordTrace_append hprefix tailTrace_2649093
  have hstable : (prefixWord ++ tailWord_2649093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649093).length < 2 ^ (prefixWord ++ tailWord_2649093).sum := by decide
  have hdescent : baseEnd_2649093 < baseStart_2649093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649113 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 3]
def baseStart_2649113 : Nat := 118140960795 + 2649113 * 2 ^ 59
def prefixEnd_2649113 : Nat := 4983230072969 + 3 ^ 40 * 2649113 * 2
def baseEnd_2649113 : Nat := 1360268277074199066904457

theorem tailTrace_2649113 : CollatzResearch.WordTrace tailWord_2649113 prefixEnd_2649113 1360268277074199066904457 := by
  unfold tailWord_2649113
  simp only [CollatzResearch.WordTrace]
  refine ⟨96621088851723508325519993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64414059234482338883679995 96621088851723508325519993)
  ·
    refine ⟨72465816638792631244139995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96621088851723508325519993 72465816638792631244139995)
    ·
      refine ⟨108698724958188946866209993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72465816638792631244139995 108698724958188946866209993)
      ·
        refine ⟨81524043718641710149657495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108698724958188946866209993 81524043718641710149657495)
        ·
          refine ⟨122286065577962565224486243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81524043718641710149657495 122286065577962565224486243)
          ·
            refine ⟨183429098366943847836729365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122286065577962565224486243 183429098366943847836729365)
            ·
              refine ⟨8598238985950492867346689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 183429098366943847836729365 8598238985950492867346689)
              ·
                refine ⟨6448679239462869650510017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8598238985950492867346689 6448679239462869650510017)
                ·
                  refine ⟨4836509429597152237882513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6448679239462869650510017 4836509429597152237882513)
                  ·
                    refine ⟨3627382072197864178411885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4836509429597152237882513 3627382072197864178411885)
                    ·
                      refine ⟨1360268277074199066904457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3627382072197864178411885 1360268277074199066904457)
                      ·
                        rfl

theorem cell23_2649113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_2649113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649113 prefixEnd_2649113 := by exact prefixLift 2649113
  have htrace : WordTrace (prefixWord ++ tailWord_2649113) baseStart_2649113 baseEnd_2649113 := by
    simpa [prefixWord, tailWord_2649113, baseEnd_2649113] using wordTrace_append hprefix tailTrace_2649113
  have hstable : (prefixWord ++ tailWord_2649113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649113).length < 2 ^ (prefixWord ++ tailWord_2649113).sum := by decide
  have hdescent : baseEnd_2649113 < baseStart_2649113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649127 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2649127 : Nat := 118140960795 + 2649127 * 2 ^ 59
def prefixEnd_2649127 : Nat := 4983230072969 + 3 ^ 40 * 2649127 * 2
def baseEnd_2649127 : Nat := 1360275465803362012129393

theorem tailTrace_2649127 : CollatzResearch.WordTrace tailWord_2649127 prefixEnd_2649127 1360275465803362012129393 := by
  unfold tailWord_2649127
  simp only [CollatzResearch.WordTrace]
  refine ⟨96621599473672788716529635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64414399649115192477686423 96621599473672788716529635)
  ·
    refine ⟨144932399210509183074794453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96621599473672788716529635 144932399210509183074794453)
    ·
      refine ⟨3396853106496308978315495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 144932399210509183074794453 3396853106496308978315495)
      ·
        refine ⟨5095279659744463467473243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3396853106496308978315495 5095279659744463467473243)
        ·
          refine ⟨7642919489616695201209865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5095279659744463467473243 7642919489616695201209865)
          ·
            refine ⟨5732189617212521400907399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7642919489616695201209865 5732189617212521400907399)
            ·
              refine ⟨8598284425818782101361099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5732189617212521400907399 8598284425818782101361099)
              ·
                refine ⟨12897426638728173152041649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8598284425818782101361099 12897426638728173152041649)
                ·
                  refine ⟨9673069979046129864031237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12897426638728173152041649 9673069979046129864031237)
                  ·
                    refine ⟨1813700621071149349505857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9673069979046129864031237 1813700621071149349505857)
                    ·
                      refine ⟨1360275465803362012129393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813700621071149349505857 1360275465803362012129393)
                      ·
                        rfl

theorem cell23_2649127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2649127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649127 prefixEnd_2649127 := by exact prefixLift 2649127
  have htrace : WordTrace (prefixWord ++ tailWord_2649127) baseStart_2649127 baseEnd_2649127 := by
    simpa [prefixWord, tailWord_2649127, baseEnd_2649127] using wordTrace_append hprefix tailTrace_2649127
  have hstable : (prefixWord ++ tailWord_2649127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649127).length < 2 ^ (prefixWord ++ tailWord_2649127).sum := by decide
  have hdescent : baseEnd_2649127 < baseStart_2649127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649193 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 1, 6]
def baseStart_2649193 : Nat := 118140960795 + 2649193 * 2 ^ 59
def prefixEnd_2649193 : Nat := 4983230072969 + 3 ^ 40 * 2649193 * 2
def baseEnd_2649193 : Nat := 453436451842186251301363

theorem tailTrace_2649193 : CollatzResearch.WordTrace tailWord_2649193 prefixEnd_2649193 453436451842186251301363 := by
  unfold tailWord_2649193
  simp only [CollatzResearch.WordTrace]
  refine ⟨96624006691433681988432233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64416004460955787992288155 96624006691433681988432233)
  ·
    refine ⟨72468005018575261491324175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96624006691433681988432233 72468005018575261491324175)
    ·
      refine ⟨108702007527862892236986263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72468005018575261491324175 108702007527862892236986263)
      ·
        refine ⟨163053011291794338355479395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108702007527862892236986263 163053011291794338355479395)
        ·
          refine ⟨244579516937691507533219093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163053011291794338355479395 244579516937691507533219093)
          ·
            refine ⟨11464664856454289415619645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 244579516937691507533219093 11464664856454289415619645)
            ·
              refine ⟨4299249321170358530857367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11464664856454289415619645 4299249321170358530857367)
              ·
                refine ⟨6448873981755537796286051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299249321170358530857367 6448873981755537796286051)
                ·
                  refine ⟨9673310972633306694429077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448873981755537796286051 9673310972633306694429077)
                  ·
                    refine ⟨453436451842186251301363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9673310972633306694429077 453436451842186251301363)
                    ·
                      rfl

theorem cell23_2649193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_2649193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649193 prefixEnd_2649193 := by exact prefixLift 2649193
  have htrace : WordTrace (prefixWord ++ tailWord_2649193) baseStart_2649193 baseEnd_2649193 := by
    simpa [prefixWord, tailWord_2649193, baseEnd_2649193] using wordTrace_append hprefix tailTrace_2649193
  have hstable : (prefixWord ++ tailWord_2649193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649193).length < 2 ^ (prefixWord ++ tailWord_2649193).sum := by decide
  have hdescent : baseEnd_2649193 < baseStart_2649193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649200 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 4]
def baseStart_2649200 : Nat := 118140960795 + 2649200 * 2 ^ 59
def prefixEnd_2649200 : Nat := 4983230072969 + 3 ^ 40 * 2649200 * 2
def baseEnd_2649200 : Nat := 1360312949891140226516557

theorem tailTrace_2649200 : CollatzResearch.WordTrace tailWord_2649200 prefixEnd_2649200 1360312949891140226516557 := by
  unfold tailWord_2649200
  simp only [CollatzResearch.WordTrace]
  refine ⟨48312131001204161091968527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64416174668272214789291369 48312131001204161091968527)
  ·
    refine ⟨72468196501806241637952791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48312131001204161091968527 72468196501806241637952791)
    ·
      refine ⟨108702294752709362456929187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72468196501806241637952791 108702294752709362456929187)
      ·
        refine ⟨163053442129064043685393781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108702294752709362456929187 163053442129064043685393781)
        ·
          refine ⟨15286260199599754095505667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163053442129064043685393781 15286260199599754095505667)
          ·
            refine ⟨22929390299399631143258501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15286260199599754095505667 22929390299399631143258501)
            ·
              refine ⟨4299260681137430839360969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22929390299399631143258501 4299260681137430839360969)
              ·
                refine ⟨3224445510853073129520727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4299260681137430839360969 3224445510853073129520727)
                ·
                  refine ⟨4836668266279609694281091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224445510853073129520727 4836668266279609694281091)
                  ·
                    refine ⟨7255002399419414541421637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4836668266279609694281091 7255002399419414541421637)
                    ·
                      refine ⟨1360312949891140226516557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7255002399419414541421637 1360312949891140226516557)
                      ·
                        rfl

theorem cell23_2649200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 4].length) (baseStart_2649200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649200 prefixEnd_2649200 := by exact prefixLift 2649200
  have htrace : WordTrace (prefixWord ++ tailWord_2649200) baseStart_2649200 baseEnd_2649200 := by
    simpa [prefixWord, tailWord_2649200, baseEnd_2649200] using wordTrace_append hprefix tailTrace_2649200
  have hstable : (prefixWord ++ tailWord_2649200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649200).length < 2 ^ (prefixWord ++ tailWord_2649200).sum := by decide
  have hdescent : baseEnd_2649200 < baseStart_2649200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649213 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_2649213 : Nat := 118140960795 + 2649213 * 2 ^ 59
def prefixEnd_2649213 : Nat := 4983230072969 + 3 ^ 40 * 2649213 * 2
def baseEnd_2649213 : Nat := 1360319625139648675653997

theorem tailTrace_2649213 : CollatzResearch.WordTrace tailWord_2649213 prefixEnd_2649213 1360319625139648675653997 := by
  unfold tailWord_2649213
  simp only [CollatzResearch.WordTrace]
  refine ⟨96624736151361225404160293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64416490767574150269440195 96624736151361225404160293)
  ·
    refine ⟨18117138028380229763280055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96624736151361225404160293 18117138028380229763280055)
    ·
      refine ⟨27175707042570344644920083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18117138028380229763280055 27175707042570344644920083)
      ·
        refine ⟨40763560563855516967380125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27175707042570344644920083 40763560563855516967380125)
        ·
          refine ⟨15286335211445818862767547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40763560563855516967380125 15286335211445818862767547)
          ·
            refine ⟨22929502817168728294151321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15286335211445818862767547 22929502817168728294151321)
            ·
              refine ⟨17197127112876546220613491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22929502817168728294151321 17197127112876546220613491)
              ·
                refine ⟨25795690669314819330920237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17197127112876546220613491 25795690669314819330920237)
                ·
                  refine ⟨9673384000993057249095089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25795690669314819330920237 9673384000993057249095089)
                  ·
                    refine ⟨7255038000744792936821317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9673384000993057249095089 7255038000744792936821317)
                    ·
                      refine ⟨1360319625139648675653997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7255038000744792936821317 1360319625139648675653997)
                      ·
                        rfl

theorem cell23_2649213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_2649213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649213 prefixEnd_2649213 := by exact prefixLift 2649213
  have htrace : WordTrace (prefixWord ++ tailWord_2649213) baseStart_2649213 baseEnd_2649213 := by
    simpa [prefixWord, tailWord_2649213, baseEnd_2649213] using wordTrace_append hprefix tailTrace_2649213
  have hstable : (prefixWord ++ tailWord_2649213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649213).length < 2 ^ (prefixWord ++ tailWord_2649213).sum := by decide
  have hdescent : baseEnd_2649213 < baseStart_2649213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649220 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_2649220 : Nat := 118140960795 + 2649220 * 2 ^ 59
def prefixEnd_2649220 : Nat := 4983230072969 + 3 ^ 40 * 2649220 * 2
def baseEnd_2649220 : Nat := 1360323219504230148266465

theorem tailTrace_2649220 : CollatzResearch.WordTrace tailWord_2649220 prefixEnd_2649220 1360323219504230148266465 := by
  unfold tailWord_2649220
  simp only [CollatzResearch.WordTrace]
  refine ⟨48312495731167932799832557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64416660974890577066443409 48312495731167932799832557)
  ·
    refine ⟨18117185899187974799937209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48312495731167932799832557 18117185899187974799937209)
    ·
      refine ⟨13587889424390981099952907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18117185899187974799937209 13587889424390981099952907)
      ·
        refine ⟨20381834136586471649929361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13587889424390981099952907 20381834136586471649929361)
        ·
          refine ⟨15286375602439853737447021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20381834136586471649929361 15286375602439853737447021)
          ·
            refine ⟨5732390850914945151542633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15286375602439853737447021 5732390850914945151542633)
            ·
              refine ⟨4299293138186208863656975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5732390850914945151542633 4299293138186208863656975)
              ·
                refine ⟨6448939707279313295485463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299293138186208863656975 6448939707279313295485463)
                ·
                  refine ⟨9673409560918969943228195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6448939707279313295485463 9673409560918969943228195)
                  ·
                    refine ⟨14510114341378454914842293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9673409560918969943228195 14510114341378454914842293)
                    ·
                      refine ⟨1360323219504230148266465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14510114341378454914842293 1360323219504230148266465)
                      ·
                        rfl

theorem cell23_2649220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_2649220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649220 prefixEnd_2649220 := by exact prefixLift 2649220
  have htrace : WordTrace (prefixWord ++ tailWord_2649220) baseStart_2649220 baseEnd_2649220 := by
    simpa [prefixWord, tailWord_2649220, baseEnd_2649220] using wordTrace_append hprefix tailTrace_2649220
  have hstable : (prefixWord ++ tailWord_2649220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649220).length < 2 ^ (prefixWord ++ tailWord_2649220).sum := by decide
  have hdescent : baseEnd_2649220 < baseStart_2649220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649234 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_2649234 : Nat := 118140960795 + 2649234 * 2 ^ 59
def prefixEnd_2649234 : Nat := 4983230072969 + 3 ^ 40 * 2649234 * 2
def baseEnd_2649234 : Nat := 1360330408233393093491401

theorem tailTrace_2649234 : CollatzResearch.WordTrace tailWord_2649234 prefixEnd_2649234 1360330408233393093491401 := by
  unfold tailWord_2649234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24156375521071286497668689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64417001389523430660449837 24156375521071286497668689)
  ·
    refine ⟨18117281640803464873251517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24156375521071286497668689 18117281640803464873251517)
    ·
      refine ⟨6793980615301299327469319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18117281640803464873251517 6793980615301299327469319)
      ·
        refine ⟨10190970922951948991203979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6793980615301299327469319 10190970922951948991203979)
        ·
          refine ⟨15286456384427923486805969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10190970922951948991203979 15286456384427923486805969)
          ·
            refine ⟨11464842288320942615104477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15286456384427923486805969 11464842288320942615104477)
            ·
              refine ⟨4299315858120353480664179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11464842288320942615104477 4299315858120353480664179)
              ·
                refine ⟨6448973787180530220996269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299315858120353480664179 6448973787180530220996269)
                ·
                  refine ⟨2418365170192698832873601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6448973787180530220996269 2418365170192698832873601)
                  ·
                    refine ⟨1813773877644524124655201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418365170192698832873601 1813773877644524124655201)
                    ·
                      refine ⟨1360330408233393093491401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813773877644524124655201 1360330408233393093491401)
                      ·
                        rfl

theorem cell23_2649234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_2649234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649234 prefixEnd_2649234 := by exact prefixLift 2649234
  have htrace : WordTrace (prefixWord ++ tailWord_2649234) baseStart_2649234 baseEnd_2649234 := by
    simpa [prefixWord, tailWord_2649234, baseEnd_2649234] using wordTrace_append hprefix tailTrace_2649234
  have hstable : (prefixWord ++ tailWord_2649234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649234).length < 2 ^ (prefixWord ++ tailWord_2649234).sum := by decide
  have hdescent : baseEnd_2649234 < baseStart_2649234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649244 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_2649244 : Nat := 118140960795 + 2649244 * 2 ^ 59
def prefixEnd_2649244 : Nat := 4983230072969 + 3 ^ 40 * 2649244 * 2
def baseEnd_2649244 : Nat := 453445181013312684788785

theorem tailTrace_2649244 : CollatzResearch.WordTrace tailWord_2649244 prefixEnd_2649244 453445181013312684788785 := by
  unfold tailWord_2649244
  simp only [CollatzResearch.WordTrace]
  refine ⟨48312933407124458849269393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64417244542832611799025857 48312933407124458849269393)
  ·
    refine ⟨36234700055343344136952045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48312933407124458849269393 36234700055343344136952045)
    ·
      refine ⟨13588012520753754051357017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36234700055343344136952045 13588012520753754051357017)
      ·
        refine ⟨10191009390565315538517763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13588012520753754051357017 10191009390565315538517763)
        ·
          refine ⟨15286514085847973307776645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10191009390565315538517763 15286514085847973307776645)
          ·
            refine ⟨2866221391096494995208121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15286514085847973307776645 2866221391096494995208121)
            ·
              refine ⟨2149666043322371246406091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2866221391096494995208121 2149666043322371246406091)
              ·
                refine ⟨3224499064983556869609137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149666043322371246406091 3224499064983556869609137)
                ·
                  refine ⟨2418374298737667652206853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3224499064983556869609137 2418374298737667652206853)
                  ·
                    refine ⟨453445181013312684788785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2418374298737667652206853 453445181013312684788785)
                    ·
                      rfl

theorem cell23_2649244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_2649244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649244 prefixEnd_2649244 := by exact prefixLift 2649244
  have htrace : WordTrace (prefixWord ++ tailWord_2649244) baseStart_2649244 baseEnd_2649244 := by
    simpa [prefixWord, tailWord_2649244, baseEnd_2649244] using wordTrace_append hprefix tailTrace_2649244
  have hstable : (prefixWord ++ tailWord_2649244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649244).length < 2 ^ (prefixWord ++ tailWord_2649244).sum := by decide
  have hdescent : baseEnd_2649244 < baseStart_2649244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649277 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_2649277 : Nat := 118140960795 + 2649277 * 2 ^ 59
def prefixEnd_2649277 : Nat := 4983230072969 + 3 ^ 40 * 2649277 * 2
def baseEnd_2649277 : Nat := 1360352487901536425253703

theorem tailTrace_2649277 : CollatzResearch.WordTrace tailWord_2649277 prefixEnd_2649277 1360352487901536425253703 := by
  unfold tailWord_2649277
  simp only [CollatzResearch.WordTrace]
  refine ⟨96627070423129364334490085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64418046948752909556326723 96627070423129364334490085)
  ·
    refine ⟨18117575704336755812716891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96627070423129364334490085 18117575704336755812716891)
    ·
      refine ⟨27176363556505133719075337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18117575704336755812716891 27176363556505133719075337)
      ·
        refine ⟨20382272667378850289306503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27176363556505133719075337 20382272667378850289306503)
        ·
          refine ⟨30573409001068275433959755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20382272667378850289306503 30573409001068275433959755)
          ·
            refine ⟨45860113501602413150939633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30573409001068275433959755 45860113501602413150939633)
            ·
              refine ⟨34395085126201809863204725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45860113501602413150939633 34395085126201809863204725)
              ·
                refine ⟨3224539230581419674675443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34395085126201809863204725 3224539230581419674675443)
                ·
                  refine ⟨4836808845872129512013165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224539230581419674675443 4836808845872129512013165)
                  ·
                    refine ⟨1813803317202048567004937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4836808845872129512013165 1813803317202048567004937)
                    ·
                      refine ⟨1360352487901536425253703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813803317202048567004937 1360352487901536425253703)
                      ·
                        rfl

theorem cell23_2649277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_2649277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649277 prefixEnd_2649277 := by exact prefixLift 2649277
  have htrace : WordTrace (prefixWord ++ tailWord_2649277) baseStart_2649277 baseEnd_2649277 := by
    simpa [prefixWord, tailWord_2649277, baseEnd_2649277] using wordTrace_append hprefix tailTrace_2649277
  have hstable : (prefixWord ++ tailWord_2649277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649277).length < 2 ^ (prefixWord ++ tailWord_2649277).sum := by decide
  have hdescent : baseEnd_2649277 < baseStart_2649277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649303 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_2649303 : Nat := 118140960795 + 2649303 * 2 ^ 59
def prefixEnd_2649303 : Nat := 4983230072969 + 3 ^ 40 * 2649303 * 2
def baseEnd_2649303 : Nat := 1360365838398553323528583

theorem tailTrace_2649303 : CollatzResearch.WordTrace tailWord_2649303 prefixEnd_2649303 1360365838398553323528583 := by
  unfold tailWord_2649303
  simp only [CollatzResearch.WordTrace]
  refine ⟨96628018721035170774936563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64418679147356780516624375 96628018721035170774936563)
  ·
    refine ⟨144942028081552756162404845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96628018721035170774936563 144942028081552756162404845)
    ·
      refine ⟨54353260530582283560901817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144942028081552756162404845 54353260530582283560901817)
      ·
        refine ⟨40764945397936712670676363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54353260530582283560901817 40764945397936712670676363)
        ·
          refine ⟨61147418096905069006014545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40764945397936712670676363 61147418096905069006014545)
          ·
            refine ⟨45860563572678801754510909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61147418096905069006014545 45860563572678801754510909)
            ·
              refine ⟨17197711339754550657941591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45860563572678801754510909 17197711339754550657941591)
              ·
                refine ⟨25796567009631825986912387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17197711339754550657941591 25796567009631825986912387)
                ·
                  refine ⟨38694850514447738980368581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25796567009631825986912387 38694850514447738980368581)
                  ·
                    refine ⟨7255284471458951058819109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38694850514447738980368581 7255284471458951058819109)
                    ·
                      refine ⟨1360365838398553323528583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7255284471458951058819109 1360365838398553323528583)
                      ·
                        rfl

theorem cell23_2649303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_2649303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649303 prefixEnd_2649303 := by exact prefixLift 2649303
  have htrace : WordTrace (prefixWord ++ tailWord_2649303) baseStart_2649303 baseEnd_2649303 := by
    simpa [prefixWord, tailWord_2649303, baseEnd_2649303] using wordTrace_append hprefix tailTrace_2649303
  have hstable : (prefixWord ++ tailWord_2649303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649303).length < 2 ^ (prefixWord ++ tailWord_2649303).sum := by decide
  have hdescent : baseEnd_2649303 < baseStart_2649303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649313 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 9]
def baseStart_2649313 : Nat := 118140960795 + 2649313 * 2 ^ 59
def prefixEnd_2649313 : Nat := 4983230072969 + 3 ^ 40 * 2649313 * 2
def baseEnd_2649313 : Nat := 151152330356122031600393

theorem tailTrace_2649313 : CollatzResearch.WordTrace tailWord_2649313 prefixEnd_2649313 151152330356122031600393 := by
  unfold tailWord_2649313
  simp only [CollatzResearch.WordTrace]
  refine ⟨96628383450998942482800593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64418922300665961655200395 96628383450998942482800593)
  ·
    refine ⟨72471287588249206862100445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96628383450998942482800593 72471287588249206862100445)
    ·
      refine ⟨27176732845593452573287667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72471287588249206862100445 27176732845593452573287667)
      ·
        refine ⟨40765099268390178859931501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27176732845593452573287667 40765099268390178859931501)
        ·
          refine ⟨15286912225646317072474313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40765099268390178859931501 15286912225646317072474313)
          ·
            refine ⟨11465184169234737804355735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15286912225646317072474313 11465184169234737804355735)
            ·
              refine ⟨17197776253852106706533603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11465184169234737804355735 17197776253852106706533603)
              ·
                refine ⟨25796664380778160059800405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17197776253852106706533603 25796664380778160059800405)
                ·
                  refine ⟨151152330356122031600393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25796664380778160059800405 151152330356122031600393)
                  ·
                    rfl

theorem cell23_2649313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 9].length) (baseStart_2649313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649313 prefixEnd_2649313 := by exact prefixLift 2649313
  have htrace : WordTrace (prefixWord ++ tailWord_2649313) baseStart_2649313 baseEnd_2649313 := by
    simpa [prefixWord, tailWord_2649313, baseEnd_2649313] using wordTrace_append hprefix tailTrace_2649313
  have hstable : (prefixWord ++ tailWord_2649313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649313).length < 2 ^ (prefixWord ++ tailWord_2649313).sum := by decide
  have hdescent : baseEnd_2649313 < baseStart_2649313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649353 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_2649353 : Nat := 118140960795 + 2649353 * 2 ^ 59
def prefixEnd_2649353 : Nat := 4983230072969 + 3 ^ 40 * 2649353 * 2
def baseEnd_2649353 : Nat := 1360391512431278127903353

theorem tailTrace_2649353 : CollatzResearch.WordTrace tailWord_2649353 prefixEnd_2649353 1360391512431278127903353 := by
  unfold tailWord_2649353
  simp only [CollatzResearch.WordTrace]
  refine ⟨96629842370854029314256713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64419894913902686209504475 96629842370854029314256713)
  ·
    refine ⟨72472381778140521985692535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96629842370854029314256713 72472381778140521985692535)
    ·
      refine ⟨108708572667210782978538803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72472381778140521985692535 108708572667210782978538803)
      ·
        refine ⟨163062859000816174467808205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108708572667210782978538803 163062859000816174467808205)
        ·
          refine ⟨61148572125306065425428077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163062859000816174467808205 61148572125306065425428077)
          ·
            refine ⟨22930714546989774534535529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61148572125306065425428077 22930714546989774534535529)
            ·
              refine ⟨17198035910242330900901647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22930714546989774534535529 17198035910242330900901647)
              ·
                refine ⟨25797053865363496351352471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17198035910242330900901647 25797053865363496351352471)
                ·
                  refine ⟨38695580798045244527028707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25797053865363496351352471 38695580798045244527028707)
                  ·
                    refine ⟨58043371197067866790543061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38695580798045244527028707 58043371197067866790543061)
                    ·
                      refine ⟨1360391512431278127903353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58043371197067866790543061 1360391512431278127903353)
                      ·
                        rfl

theorem cell23_2649353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_2649353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649353 prefixEnd_2649353 := by exact prefixLift 2649353
  have htrace : WordTrace (prefixWord ++ tailWord_2649353) baseStart_2649353 baseEnd_2649353 := by
    simpa [prefixWord, tailWord_2649353, baseEnd_2649353] using wordTrace_append hprefix tailTrace_2649353
  have hstable : (prefixWord ++ tailWord_2649353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649353).length < 2 ^ (prefixWord ++ tailWord_2649353).sum := by decide
  have hdescent : baseEnd_2649353 < baseStart_2649353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649380 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2649380 : Nat := 118140960795 + 2649380 * 2 ^ 59
def prefixEnd_2649380 : Nat := 4983230072969 + 3 ^ 40 * 2649380 * 2
def baseEnd_2649380 : Nat := 1360405376408949522265729

theorem tailTrace_2649380 : CollatzResearch.WordTrace tailWord_2649380 prefixEnd_2649380 1360405376408949522265729 := by
  unfold tailWord_2649380
  simp only [CollatzResearch.WordTrace]
  refine ⟨48315413570878106462744797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64420551427837475283659729 48315413570878106462744797)
  ·
    refine ⟨18118280089079289923529299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48315413570878106462744797 18118280089079289923529299)
    ·
      refine ⟨27177420133618934885293949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18118280089079289923529299 27177420133618934885293949)
      ·
        refine ⟨10191532550107100581985231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27177420133618934885293949 10191532550107100581985231)
        ·
          refine ⟨15287298825160650872977847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10191532550107100581985231 15287298825160650872977847)
          ·
            refine ⟨22930948237740976309466771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15287298825160650872977847 22930948237740976309466771)
            ·
              refine ⟨34396422356611464464200157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22930948237740976309466771 34396422356611464464200157)
              ·
                refine ⟨12898658383729299174075059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34396422356611464464200157 12898658383729299174075059)
                ·
                  refine ⟨19347987575593948761112589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12898658383729299174075059 19347987575593948761112589)
                  ·
                    refine ⟨7255495340847730785417221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19347987575593948761112589 7255495340847730785417221)
                    ·
                      refine ⟨1360405376408949522265729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7255495340847730785417221 1360405376408949522265729)
                      ·
                        rfl

theorem cell23_2649380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2649380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649380 prefixEnd_2649380 := by exact prefixLift 2649380
  have htrace : WordTrace (prefixWord ++ tailWord_2649380) baseStart_2649380 baseEnd_2649380 := by
    simpa [prefixWord, tailWord_2649380, baseEnd_2649380] using wordTrace_append hprefix tailTrace_2649380
  have hstable : (prefixWord ++ tailWord_2649380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649380).length < 2 ^ (prefixWord ++ tailWord_2649380).sum := by decide
  have hdescent : baseEnd_2649380 < baseStart_2649380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649397 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2649397 : Nat := 118140960795 + 2649397 * 2 ^ 59
def prefixEnd_2649397 : Nat := 4983230072969 + 3 ^ 40 * 2649397 * 2
def baseEnd_2649397 : Nat := 1360414105580075955753151

theorem tailTrace_2649397 : CollatzResearch.WordTrace tailWord_2649397 prefixEnd_2649397 1360414105580075955753151 := by
  unfold tailWord_2649397
  simp only [CollatzResearch.WordTrace]
  refine ⟨96631447182694624828858445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64420964788463083219238963 96631447182694624828858445)
  ·
    refine ⟨36236792693510484310821917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96631447182694624828858445 36236792693510484310821917)
    ·
      refine ⟨13588797260066431616558219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36236792693510484310821917 13588797260066431616558219)
      ·
        refine ⟨20383195890099647424837329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13588797260066431616558219 20383195890099647424837329)
        ·
          refine ⟨15287396917574735568627997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20383195890099647424837329 15287396917574735568627997)
          ·
            refine ⟨5732773844090525838235499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15287396917574735568627997 5732773844090525838235499)
            ·
              refine ⟨8599160766135788757353249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5732773844090525838235499 8599160766135788757353249)
              ·
                refine ⟨6449370574601841568014937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8599160766135788757353249 6449370574601841568014937)
                ·
                  refine ⟨4837027930951381176011203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6449370574601841568014937 4837027930951381176011203)
                  ·
                    refine ⟨7255541896427071764016805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4837027930951381176011203 7255541896427071764016805)
                    ·
                      refine ⟨1360414105580075955753151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7255541896427071764016805 1360414105580075955753151)
                      ·
                        rfl

theorem cell23_2649397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2649397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649397 prefixEnd_2649397 := by exact prefixLift 2649397
  have htrace : WordTrace (prefixWord ++ tailWord_2649397) baseStart_2649397 baseEnd_2649397 := by
    simpa [prefixWord, tailWord_2649397, baseEnd_2649397] using wordTrace_append hprefix tailTrace_2649397
  have hstable : (prefixWord ++ tailWord_2649397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649397).length < 2 ^ (prefixWord ++ tailWord_2649397).sum := by decide
  have hdescent : baseEnd_2649397 < baseStart_2649397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649398 : List Nat := [5, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_2649398 : Nat := 118140960795 + 2649398 * 2 ^ 59
def prefixEnd_2649398 : Nat := 4983230072969 + 3 ^ 40 * 2649398 * 2
def baseEnd_2649398 : Nat := 151157179895636716871183

theorem tailTrace_2649398 : CollatzResearch.WordTrace tailWord_2649398 prefixEnd_2649398 151157179895636716871183 := by
  unfold tailWord_2649398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6039467728480687624977803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 64420989103794001333096565 6039467728480687624977803)
  ·
    refine ⟨9059201592721031437466705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6039467728480687624977803 9059201592721031437466705)
    ·
      refine ⟨6794401194540773578100029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9059201592721031437466705 6794401194540773578100029)
      ·
        refine ⟨2547900447952790091787511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6794401194540773578100029 2547900447952790091787511)
        ·
          refine ⟨3821850671929185137681267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547900447952790091787511 3821850671929185137681267)
          ·
            refine ⟨5732776007893777706521901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821850671929185137681267 5732776007893777706521901)
            ·
              refine ⟨2149791002960166639945713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5732776007893777706521901 2149791002960166639945713)
              ·
                refine ⟨1612343252220124979959285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2149791002960166639945713 1612343252220124979959285)
                ·
                  refine ⟨151157179895636716871183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1612343252220124979959285 151157179895636716871183)
                  ·
                    rfl

theorem cell23_2649398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_2649398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649398 prefixEnd_2649398 := by exact prefixLift 2649398
  have htrace : WordTrace (prefixWord ++ tailWord_2649398) baseStart_2649398 baseEnd_2649398 := by
    simpa [prefixWord, tailWord_2649398, baseEnd_2649398] using wordTrace_append hprefix tailTrace_2649398
  have hstable : (prefixWord ++ tailWord_2649398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649398).length < 2 ^ (prefixWord ++ tailWord_2649398).sum := by decide
  have hdescent : baseEnd_2649398 < baseStart_2649398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649407 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 3, 4]
def baseStart_2649407 : Nat := 118140960795 + 2649407 * 2 ^ 59
def prefixEnd_2649407 : Nat := 4983230072969 + 3 ^ 40 * 2649407 * 2
def baseEnd_2649407 : Nat := 453473080128873638876035

theorem tailTrace_2649407 : CollatzResearch.WordTrace tailWord_2649407 prefixEnd_2649407 453473080128873638876035 := by
  unfold tailWord_2649407
  simp only [CollatzResearch.WordTrace]
  refine ⟨96631811912658396536722475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64421207941772264357814983 96631811912658396536722475)
  ·
    refine ⟨144947717868987594805083713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96631811912658396536722475 144947717868987594805083713)
    ·
      refine ⟨108710788401740696103812785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144947717868987594805083713 108710788401740696103812785)
      ·
        refine ⟨81533091301305522077859589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108710788401740696103812785 81533091301305522077859589)
        ·
          refine ⟨15287454618994785389598673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81533091301305522077859589 15287454618994785389598673)
          ·
            refine ⟨11465590964246089042199005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15287454618994785389598673 11465590964246089042199005)
            ·
              refine ⟨4299596611592283390824627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11465590964246089042199005 4299596611592283390824627)
              ·
                refine ⟨6449394917388425086236941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299596611592283390824627 6449394917388425086236941)
                ·
                  refine ⟨2418523094020659407338853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6449394917388425086236941 2418523094020659407338853)
                  ·
                    refine ⟨453473080128873638876035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2418523094020659407338853 453473080128873638876035)
                    ·
                      rfl

theorem cell23_2649407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 4].length) (baseStart_2649407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649407 prefixEnd_2649407 := by exact prefixLift 2649407
  have htrace : WordTrace (prefixWord ++ tailWord_2649407) baseStart_2649407 baseEnd_2649407 := by
    simpa [prefixWord, tailWord_2649407, baseEnd_2649407] using wordTrace_append hprefix tailTrace_2649407
  have hstable : (prefixWord ++ tailWord_2649407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649407).length < 2 ^ (prefixWord ++ tailWord_2649407).sum := by decide
  have hdescent : baseEnd_2649407 < baseStart_2649407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649423 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_2649423 : Nat := 118140960795 + 2649423 * 2 ^ 59
def prefixEnd_2649423 : Nat := 4983230072969 + 3 ^ 40 * 2649423 * 2
def baseEnd_2649423 : Nat := 1360427456077092854028031

theorem tailTrace_2649423 : CollatzResearch.WordTrace tailWord_2649423 prefixEnd_2649423 1360427456077092854028031 := by
  unfold tailWord_2649423
  simp only [CollatzResearch.WordTrace]
  refine ⟨96632395480600431269304923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64421596987066954179536615 96632395480600431269304923)
  ·
    refine ⟨144948593220900646903957385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96632395480600431269304923 144948593220900646903957385)
    ·
      refine ⟨108711444915675485177968039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144948593220900646903957385 108711444915675485177968039)
      ·
        refine ⟨163067167373513227766952059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108711444915675485177968039 163067167373513227766952059)
        ·
          refine ⟨244600751060269841650428089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163067167373513227766952059 244600751060269841650428089)
          ·
            refine ⟨183450563295202381237821067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244600751060269841650428089 183450563295202381237821067)
            ·
              refine ⟨275175844942803571856731601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183450563295202381237821067 275175844942803571856731601)
              ·
                refine ⟨206381883707102678892548701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275175844942803571856731601 206381883707102678892548701)
                ·
                  refine ⟨77393206390163504584705763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206381883707102678892548701 77393206390163504584705763)
                  ·
                    refine ⟨116089809585245256877058645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77393206390163504584705763 116089809585245256877058645)
                    ·
                      refine ⟨1360427456077092854028031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 116089809585245256877058645 1360427456077092854028031)
                      ·
                        rfl

theorem cell23_2649423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_2649423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649423 prefixEnd_2649423 := by exact prefixLift 2649423
  have htrace : WordTrace (prefixWord ++ tailWord_2649423) baseStart_2649423 baseEnd_2649423 := by
    simpa [prefixWord, tailWord_2649423, baseEnd_2649423] using wordTrace_append hprefix tailTrace_2649423
  have hstable : (prefixWord ++ tailWord_2649423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649423).length < 2 ^ (prefixWord ++ tailWord_2649423).sum := by decide
  have hdescent : baseEnd_2649423 < baseStart_2649423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649501 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_2649501 : Nat := 118140960795 + 2649501 * 2 ^ 59
def prefixEnd_2649501 : Nat := 4983230072969 + 3 ^ 40 * 2649501 * 2
def baseEnd_2649501 : Nat := 453489169189381182950891

theorem tailTrace_2649501 : CollatzResearch.WordTrace tailWord_2649501 prefixEnd_2649501 453489169189381182950891 := by
  unfold tailWord_2649501
  simp only [CollatzResearch.WordTrace]
  refine ⟨96635240374317850590644357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64423493582878567060429571 96635240374317850590644357)
  ·
    refine ⟨18119107570184596985745817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96635240374317850590644357 18119107570184596985745817)
    ·
      refine ⟨13589330677638447739309363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18119107570184596985745817 13589330677638447739309363)
      ·
        refine ⟨20383996016457671608964045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13589330677638447739309363 20383996016457671608964045)
        ·
          refine ⟨7643998506171626853361517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20383996016457671608964045 7643998506171626853361517)
          ·
            refine ⟨2866499439814360070010569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7643998506171626853361517 2866499439814360070010569)
            ·
              refine ⟨2149874579860770052507927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2866499439814360070010569 2149874579860770052507927)
              ·
                refine ⟨3224811869791155078761891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149874579860770052507927 3224811869791155078761891)
                ·
                  refine ⟨4837217804686732618142837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3224811869791155078761891 4837217804686732618142837)
                  ·
                    refine ⟨453489169189381182950891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4837217804686732618142837 453489169189381182950891)
                    ·
                      rfl

theorem cell23_2649501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_2649501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649501 prefixEnd_2649501 := by exact prefixLift 2649501
  have htrace : WordTrace (prefixWord ++ tailWord_2649501) baseStart_2649501 baseEnd_2649501 := by
    simpa [prefixWord, tailWord_2649501, baseEnd_2649501] using wordTrace_append hprefix tailTrace_2649501
  have hstable : (prefixWord ++ tailWord_2649501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649501).length < 2 ^ (prefixWord ++ tailWord_2649501).sum := by decide
  have hdescent : baseEnd_2649501 < baseStart_2649501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649504 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 5, 2, 2]
def baseStart_2649504 : Nat := 118140960795 + 2649504 * 2 ^ 59
def prefixEnd_2649504 : Nat := 4983230072969 + 3 ^ 40 * 2649504 * 2
def baseEnd_2649504 : Nat := 1360469048010107037115159

theorem tailTrace_2649504 : CollatzResearch.WordTrace tailWord_2649504 prefixEnd_2649504 1360469048010107037115159 := by
  unfold tailWord_2649504
  simp only [CollatzResearch.WordTrace]
  refine ⟨48317674896653491051501783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64423566528871321402002377 48317674896653491051501783)
  ·
    refine ⟨72476512344980236577252675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48317674896653491051501783 72476512344980236577252675)
    ·
      refine ⟨108714768517470354865879013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72476512344980236577252675 108714768517470354865879013)
      ·
        refine ⟨20384019097025691537352315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108714768517470354865879013 20384019097025691537352315)
        ·
          refine ⟨30576028645538537306028473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20384019097025691537352315 30576028645538537306028473)
          ·
            refine ⟨22932021484153902979521355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30576028645538537306028473 22932021484153902979521355)
            ·
              refine ⟨34398032226230854469282033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22932021484153902979521355 34398032226230854469282033)
              ·
                refine ⟨25798524169673140851961525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34398032226230854469282033 25798524169673140851961525)
                ·
                  refine ⟨2418611640906856954871393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25798524169673140851961525 2418611640906856954871393)
                  ·
                    refine ⟨1813958730680142716153545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418611640906856954871393 1813958730680142716153545)
                    ·
                      refine ⟨1360469048010107037115159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813958730680142716153545 1360469048010107037115159)
                      ·
                        rfl

theorem cell23_2649504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_2649504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649504 prefixEnd_2649504 := by exact prefixLift 2649504
  have htrace : WordTrace (prefixWord ++ tailWord_2649504) baseStart_2649504 baseEnd_2649504 := by
    simpa [prefixWord, tailWord_2649504, baseEnd_2649504] using wordTrace_append hprefix tailTrace_2649504
  have hstable : (prefixWord ++ tailWord_2649504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649504).length < 2 ^ (prefixWord ++ tailWord_2649504).sum := by decide
  have hdescent : baseEnd_2649504 < baseStart_2649504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649521 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 3, 2, 2]
def baseStart_2649521 : Nat := 118140960795 + 2649521 * 2 ^ 59
def prefixEnd_2649521 : Nat := 4983230072969 + 3 ^ 40 * 2649521 * 2
def baseEnd_2649521 : Nat := 1360477777181233470602581

theorem tailTrace_2649521 : CollatzResearch.WordTrace tailWord_2649521 prefixEnd_2649521 1360477777181233470602581 := by
  unfold tailWord_2649521
  simp only [CollatzResearch.WordTrace]
  refine ⟨96635969834245394006372417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64423979889496929337581611 96635969834245394006372417)
  ·
    refine ⟨72476977375684045504779313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96635969834245394006372417 72476977375684045504779313)
    ·
      refine ⟨54357733031763034128584485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72476977375684045504779313 54357733031763034128584485)
      ·
        refine ⟨10192074943455568899109591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54357733031763034128584485 10192074943455568899109591)
        ·
          refine ⟨15288112415183353348664387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10192074943455568899109591 15288112415183353348664387)
          ·
            refine ⟨22932168622775030022996581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15288112415183353348664387 22932168622775030022996581)
            ·
              refine ⟨4299781616770318129311859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22932168622775030022996581 4299781616770318129311859)
              ·
                refine ⟨6449672425155477193967789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299781616770318129311859 6449672425155477193967789)
                ·
                  refine ⟨2418627159433303947737921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6449672425155477193967789 2418627159433303947737921)
                  ·
                    refine ⟨1813970369574977960803441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418627159433303947737921 1813970369574977960803441)
                    ·
                      refine ⟨1360477777181233470602581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1813970369574977960803441 1360477777181233470602581)
                      ·
                        rfl

theorem cell23_2649521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_2649521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649521 prefixEnd_2649521 := by exact prefixLift 2649521
  have htrace : WordTrace (prefixWord ++ tailWord_2649521) baseStart_2649521 baseEnd_2649521 := by
    simpa [prefixWord, tailWord_2649521, baseEnd_2649521] using wordTrace_append hprefix tailTrace_2649521
  have hstable : (prefixWord ++ tailWord_2649521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649521).length < 2 ^ (prefixWord ++ tailWord_2649521).sum := by decide
  have hdescent : baseEnd_2649521 < baseStart_2649521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649594 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2]
def baseStart_2649594 : Nat := 118140960795 + 2649594 * 2 ^ 59
def prefixEnd_2649594 : Nat := 4983230072969 + 3 ^ 40 * 2649594 * 2
def baseEnd_2649594 : Nat := 1360515261269011684989745

theorem tailTrace_2649594 : CollatzResearch.WordTrace tailWord_2649594 prefixEnd_2649594 1360515261269011684989745 := by
  unfold tailWord_2649594
  simp only [CollatzResearch.WordTrace]
  refine ⟨24159658090745231868444959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64425754908653951649186557 24159658090745231868444959)
  ·
    refine ⟨36239487136117847802667439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24159658090745231868444959 36239487136117847802667439)
    ·
      refine ⟨54359230704176771704001159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36239487136117847802667439 54359230704176771704001159)
      ·
        refine ⟨81538846056265157556001739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54359230704176771704001159 81538846056265157556001739)
        ·
          refine ⟨122308269084397736334002609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81538846056265157556001739 122308269084397736334002609)
          ·
            refine ⟨91731201813298302250501957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122308269084397736334002609 91731201813298302250501957)
            ·
              refine ⟨17199600339993431671969117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91731201813298302250501957 17199600339993431671969117)
              ·
                refine ⟨6449850127497536876988419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17199600339993431671969117 6449850127497536876988419)
                ·
                  refine ⟨9674775191246305315482629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6449850127497536876988419 9674775191246305315482629)
                  ·
                    refine ⟨1814020348358682246652993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9674775191246305315482629 1814020348358682246652993)
                    ·
                      refine ⟨1360515261269011684989745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814020348358682246652993 1360515261269011684989745)
                      ·
                        rfl

theorem cell23_2649594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_2649594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649594 prefixEnd_2649594 := by exact prefixLift 2649594
  have htrace : WordTrace (prefixWord ++ tailWord_2649594) baseStart_2649594 baseEnd_2649594 := by
    simpa [prefixWord, tailWord_2649594, baseEnd_2649594] using wordTrace_append hprefix tailTrace_2649594
  have hstable : (prefixWord ++ tailWord_2649594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649594).length < 2 ^ (prefixWord ++ tailWord_2649594).sum := by decide
  have hdescent : baseEnd_2649594 < baseStart_2649594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649597 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_2649597 : Nat := 118140960795 + 2649597 * 2 ^ 59
def prefixEnd_2649597 : Nat := 4983230072969 + 3 ^ 40 * 2649597 * 2
def baseEnd_2649597 : Nat := 1360516801710975173252231

theorem tailTrace_2649597 : CollatzResearch.WordTrace tailWord_2649597 prefixEnd_2649597 1360516801710975173252231 := by
  unfold tailWord_2649597
  simp only [CollatzResearch.WordTrace]
  refine ⟨96638741781970058986139045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64425827854646705990759363 96638741781970058986139045)
  ·
    refine ⟨18119764084119386059901071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96638741781970058986139045 18119764084119386059901071)
    ·
      refine ⟨27179646126179079089851607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18119764084119386059901071 27179646126179079089851607)
      ·
        refine ⟨40769469189268618634777411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27179646126179079089851607 40769469189268618634777411)
        ·
          refine ⟨61154203783902927952166117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40769469189268618634777411 61154203783902927952166117)
          ·
            refine ⟨11466413209481798991031147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61154203783902927952166117 11466413209481798991031147)
            ·
              refine ⟨17199619814222698486546721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11466413209481798991031147 17199619814222698486546721)
              ·
                refine ⟨12899714860667023864910041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17199619814222698486546721 12899714860667023864910041)
                ·
                  refine ⟨9674786145500267898682531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12899714860667023864910041 9674786145500267898682531)
                  ·
                    refine ⟨14512179218250401848023797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9674786145500267898682531 14512179218250401848023797)
                    ·
                      refine ⟨1360516801710975173252231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14512179218250401848023797 1360516801710975173252231)
                      ·
                        rfl

theorem cell23_2649597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_2649597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649597 prefixEnd_2649597 := by exact prefixLift 2649597
  have htrace : WordTrace (prefixWord ++ tailWord_2649597) baseStart_2649597 baseEnd_2649597 := by
    simpa [prefixWord, tailWord_2649597, baseEnd_2649597] using wordTrace_append hprefix tailTrace_2649597
  have hstable : (prefixWord ++ tailWord_2649597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649597).length < 2 ^ (prefixWord ++ tailWord_2649597).sum := by decide
  have hdescent : baseEnd_2649597 < baseStart_2649597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649611 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 1, 4, 2]
def baseStart_2649611 : Nat := 118140960795 + 2649611 * 2 ^ 59
def prefixEnd_2649611 : Nat := 4983230072969 + 3 ^ 40 * 2649611 * 2
def baseEnd_2649611 : Nat := 1360523990440138118477167

theorem tailTrace_2649611 : CollatzResearch.WordTrace tailWord_2649611 prefixEnd_2649611 1360523990440138118477167 := by
  unfold tailWord_2649611
  simp only [CollatzResearch.WordTrace]
  refine ⟨96639252403919339377148687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64426168269279559584765791 96639252403919339377148687)
  ·
    refine ⟨144958878605879009065723031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96639252403919339377148687 144958878605879009065723031)
    ·
      refine ⟨217438317908818513598584547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144958878605879009065723031 217438317908818513598584547)
      ·
        refine ⟨326157476863227770397876821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217438317908818513598584547 326157476863227770397876821)
        ·
          refine ⟨3822157931990950434350119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 326157476863227770397876821 3822157931990950434350119)
          ·
            refine ⟨5733236897986425651525179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822157931990950434350119 5733236897986425651525179)
            ·
              refine ⟨8599855346979638477287769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5733236897986425651525179 8599855346979638477287769)
              ·
                refine ⟨6449891510234728857965827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8599855346979638477287769 6449891510234728857965827)
                ·
                  refine ⟨9674837265352093286948741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6449891510234728857965827 9674837265352093286948741)
                  ·
                    refine ⟨1814031987253517491302889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9674837265352093286948741 1814031987253517491302889)
                    ·
                      refine ⟨1360523990440138118477167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814031987253517491302889 1360523990440138118477167)
                      ·
                        rfl

theorem cell23_2649611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 4, 2].length) (baseStart_2649611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649611 prefixEnd_2649611 := by exact prefixLift 2649611
  have htrace : WordTrace (prefixWord ++ tailWord_2649611) baseStart_2649611 baseEnd_2649611 := by
    simpa [prefixWord, tailWord_2649611, baseEnd_2649611] using wordTrace_append hprefix tailTrace_2649611
  have hstable : (prefixWord ++ tailWord_2649611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649611).length < 2 ^ (prefixWord ++ tailWord_2649611).sum := by decide
  have hdescent : baseEnd_2649611 < baseStart_2649611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649628 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_2649628 : Nat := 118140960795 + 2649628 * 2 ^ 59
def prefixEnd_2649628 : Nat := 4983230072969 + 3 ^ 40 * 2649628 * 2
def baseEnd_2649628 : Nat := 1360532719611264551964589

theorem tailTrace_2649628 : CollatzResearch.WordTrace tailWord_2649628 prefixEnd_2649628 1360532719611264551964589 := by
  unfold tailWord_2649628
  simp only [CollatzResearch.WordTrace]
  refine ⟨48319936222428875640258769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64426581629905167520345025 48319936222428875640258769)
  ·
    refine ⟨36239952166821656730194077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48319936222428875640258769 36239952166821656730194077)
    ·
      refine ⟨13589982062558121273822779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36239952166821656730194077 13589982062558121273822779)
      ·
        refine ⟨20384973093837181910734169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13589982062558121273822779 20384973093837181910734169)
        ·
          refine ⟨15288729820377886433050627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20384973093837181910734169 15288729820377886433050627)
          ·
            refine ⟨22933094730566829649575941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15288729820377886433050627 22933094730566829649575941)
            ·
              refine ⟨4299955261981280559295489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22933094730566829649575941 4299955261981280559295489)
              ·
                refine ⟨3224966446485960419471617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4299955261981280559295489 3224966446485960419471617)
                ·
                  refine ⟨2418724834864470314603713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3224966446485960419471617 2418724834864470314603713)
                  ·
                    refine ⟨1814043626148352735952785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418724834864470314603713 1814043626148352735952785)
                    ·
                      refine ⟨1360532719611264551964589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814043626148352735952785 1360532719611264551964589)
                      ·
                        rfl

theorem cell23_2649628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_2649628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649628 prefixEnd_2649628 := by exact prefixLift 2649628
  have htrace : WordTrace (prefixWord ++ tailWord_2649628) baseStart_2649628 baseEnd_2649628 := by
    simpa [prefixWord, tailWord_2649628, baseEnd_2649628] using wordTrace_append hprefix tailTrace_2649628
  have hstable : (prefixWord ++ tailWord_2649628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649628).length < 2 ^ (prefixWord ++ tailWord_2649628).sum := by decide
  have hdescent : baseEnd_2649628 < baseStart_2649628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649684 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2649684 : Nat := 118140960795 + 2649684 * 2 ^ 59
def prefixEnd_2649684 : Nat := 4983230072969 + 3 ^ 40 * 2649684 * 2
def baseEnd_2649684 : Nat := 1360561474527916332864331

theorem tailTrace_2649684 : CollatzResearch.WordTrace tailWord_2649684 prefixEnd_2649684 1360561474527916332864331 := by
  unfold tailWord_2649684
  simp only [CollatzResearch.WordTrace]
  refine ⟨48320957466327436422278053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64427943288436581896370737 48320957466327436422278053)
  ·
    refine ⟨9060179524936394329177135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48320957466327436422278053 9060179524936394329177135)
    ·
      refine ⟨13590269287404591493765703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9060179524936394329177135 13590269287404591493765703)
      ·
        refine ⟨20385403931106887240648555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13590269287404591493765703 20385403931106887240648555)
        ·
          refine ⟨30578105896660330860972833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20385403931106887240648555 30578105896660330860972833)
          ·
            refine ⟨22933579422495248145729625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30578105896660330860972833 22933579422495248145729625)
            ·
              refine ⟨17200184566871436109297219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22933579422495248145729625 17200184566871436109297219)
              ·
                refine ⟨25800276850307154163945829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17200184566871436109297219 25800276850307154163945829)
                ·
                  refine ⟨4837551909432591405739843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25800276850307154163945829 4837551909432591405739843)
                  ·
                    refine ⟨7256327864148887108609765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4837551909432591405739843 7256327864148887108609765)
                    ·
                      refine ⟨1360561474527916332864331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7256327864148887108609765 1360561474527916332864331)
                      ·
                        rfl

theorem cell23_2649684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2649684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649684 prefixEnd_2649684 := by exact prefixLift 2649684
  have htrace : WordTrace (prefixWord ++ tailWord_2649684) baseStart_2649684 baseEnd_2649684 := by
    simpa [prefixWord, tailWord_2649684, baseEnd_2649684] using wordTrace_append hprefix tailTrace_2649684
  have hstable : (prefixWord ++ tailWord_2649684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649684).length < 2 ^ (prefixWord ++ tailWord_2649684).sum := by decide
  have hdescent : baseEnd_2649684 < baseStart_2649684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649697 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2649697 : Nat := 118140960795 + 2649697 * 2 ^ 59
def prefixEnd_2649697 : Nat := 4983230072969 + 3 ^ 40 * 2649697 * 2
def baseEnd_2649697 : Nat := 1360568149776424782001771

theorem tailTrace_2649697 : CollatzResearch.WordTrace tailWord_2649697 prefixEnd_2649697 1360568149776424782001771 := by
  unfold tailWord_2649697
  simp only [CollatzResearch.WordTrace]
  refine ⟨96642389081607776064779345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64428259387738517376519563 96642389081607776064779345)
  ·
    refine ⟨72481791811205832048584509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96642389081607776064779345 72481791811205832048584509)
    ·
      refine ⟨27180671929202187018219191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72481791811205832048584509 27180671929202187018219191)
      ·
        refine ⟨40771007893803280527328787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27180671929202187018219191 40771007893803280527328787)
        ·
          refine ⟨61156511840704920790993181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40771007893803280527328787 61156511840704920790993181)
          ·
            refine ⟨22933691940264345296622443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61156511840704920790993181 22933691940264345296622443)
            ·
              refine ⟨34400537910396517944933665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22933691940264345296622443 34400537910396517944933665)
              ·
                refine ⟨25800403432797388458700249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34400537910396517944933665 25800403432797388458700249)
                ·
                  refine ⟨19350302574598041344025187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25800403432797388458700249 19350302574598041344025187)
                  ·
                    refine ⟨29025453861897062016037781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19350302574598041344025187 29025453861897062016037781)
                    ·
                      refine ⟨1360568149776424782001771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29025453861897062016037781 1360568149776424782001771)
                      ·
                        rfl

theorem cell23_2649697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2649697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649697 prefixEnd_2649697 := by exact prefixLift 2649697
  have htrace : WordTrace (prefixWord ++ tailWord_2649697) baseStart_2649697 baseEnd_2649697 := by
    simpa [prefixWord, tailWord_2649697, baseEnd_2649697] using wordTrace_append hprefix tailTrace_2649697
  have hstable : (prefixWord ++ tailWord_2649697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649697).length < 2 ^ (prefixWord ++ tailWord_2649697).sum := by decide
  have hdescent : baseEnd_2649697 < baseStart_2649697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649701 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 2, 4, 2]
def baseStart_2649701 : Nat := 118140960795 + 2649701 * 2 ^ 59
def prefixEnd_2649701 : Nat := 4983230072969 + 3 ^ 40 * 2649701 * 2
def baseEnd_2649701 : Nat := 1360570203699042766351753

theorem tailTrace_2649701 : CollatzResearch.WordTrace tailWord_2649701 prefixEnd_2649701 1360570203699042766351753 := by
  unfold tailWord_2649701
  simp only [CollatzResearch.WordTrace]
  refine ⟨96642534973593284747924957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64428356649062189831949971 96642534973593284747924957)
  ·
    refine ⟨36240950615097481780471859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96642534973593284747924957 36240950615097481780471859)
    ·
      refine ⟨54361425922646222670707789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36240950615097481780471859 54361425922646222670707789)
      ·
        refine ⟨20385534720992333501515421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54361425922646222670707789 20385534720992333501515421)
        ·
          refine ⟨7644575520372125063068283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20385534720992333501515421 7644575520372125063068283)
          ·
            refine ⟨11466863280558187594602425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7644575520372125063068283 11466863280558187594602425)
            ·
              refine ⟨8600147460418640695951819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11466863280558187594602425 8600147460418640695951819)
              ·
                refine ⟨12900221190627961043927729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8600147460418640695951819 12900221190627961043927729)
                ·
                  refine ⟨9675165892970970782945797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12900221190627961043927729 9675165892970970782945797)
                  ·
                    refine ⟨1814093604932057021802337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9675165892970970782945797 1814093604932057021802337)
                    ·
                      refine ⟨1360570203699042766351753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814093604932057021802337 1360570203699042766351753)
                      ·
                        rfl

theorem cell23_2649701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_2649701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649701 prefixEnd_2649701 := by exact prefixLift 2649701
  have htrace : WordTrace (prefixWord ++ tailWord_2649701) baseStart_2649701 baseEnd_2649701 := by
    simpa [prefixWord, tailWord_2649701, baseEnd_2649701] using wordTrace_append hprefix tailTrace_2649701
  have hstable : (prefixWord ++ tailWord_2649701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649701).length < 2 ^ (prefixWord ++ tailWord_2649701).sum := by decide
  have hdescent : baseEnd_2649701 < baseStart_2649701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649758 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_2649758 : Nat := 118140960795 + 2649758 * 2 ^ 59
def prefixEnd_2649758 : Nat := 4983230072969 + 3 ^ 40 * 2649758 * 2
def baseEnd_2649758 : Nat := 151177719121816560370999

theorem tailTrace_2649758 : CollatzResearch.WordTrace tailWord_2649758 prefixEnd_2649758 151177719121816560370999 := by
  unfold tailWord_2649758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12080576741798347935343741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 64429742622924522321833285 12080576741798347935343741)
  ·
    refine ⟨4530216278174380475753903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12080576741798347935343741 4530216278174380475753903)
    ·
      refine ⟨6795324417261570713630855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4530216278174380475753903 6795324417261570713630855)
      ·
        refine ⟨10192986625892356070446283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6795324417261570713630855 10192986625892356070446283)
        ·
          refine ⟨15289479938838534105669425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10192986625892356070446283 15289479938838534105669425)
          ·
            refine ⟨11467109954128900579252069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15289479938838534105669425 11467109954128900579252069)
            ·
              refine ⟨2150083116399168858609763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11467109954128900579252069 2150083116399168858609763)
              ·
                refine ⟨3225124674598753287914645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150083116399168858609763 3225124674598753287914645)
                ·
                  refine ⟨151177719121816560370999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3225124674598753287914645 151177719121816560370999)
                  ·
                    rfl

theorem cell23_2649758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_2649758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649758 prefixEnd_2649758 := by exact prefixLift 2649758
  have htrace : WordTrace (prefixWord ++ tailWord_2649758) baseStart_2649758 baseEnd_2649758 := by
    simpa [prefixWord, tailWord_2649758, baseEnd_2649758] using wordTrace_append hprefix tailTrace_2649758
  have hstable : (prefixWord ++ tailWord_2649758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649758).length < 2 ^ (prefixWord ++ tailWord_2649758).sum := by decide
  have hdescent : baseEnd_2649758 < baseStart_2649758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649784 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 6, 4]
def baseStart_2649784 : Nat := 118140960795 + 2649784 * 2 ^ 59
def prefixEnd_2649784 : Nat := 4983230072969 + 3 ^ 40 * 2649784 * 2
def baseEnd_2649784 : Nat := 453537607531121980537957

theorem tailTrace_2649784 : CollatzResearch.WordTrace tailWord_2649784 prefixEnd_2649784 453537607531121980537957 := by
  unfold tailWord_2649784
  simp only [CollatzResearch.WordTrace]
  refine ⟨48322781116146294961598203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64430374821528393282130937 48322781116146294961598203)
  ·
    refine ⟨72484171674219442442397305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48322781116146294961598203 72484171674219442442397305)
    ·
      refine ⟨54363128755664581831797979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72484171674219442442397305 54363128755664581831797979)
      ·
        refine ⟨81544693133496872747696969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54363128755664581831797979 81544693133496872747696969)
        ·
          refine ⟨61158519850122654560772727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81544693133496872747696969 61158519850122654560772727)
          ·
            refine ⟨91737779775183981841159091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61158519850122654560772727 91737779775183981841159091)
            ·
              refine ⟨137606669662775972761738637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91737779775183981841159091 137606669662775972761738637)
              ·
                refine ⟨51602501123540989785651989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137606669662775972761738637 51602501123540989785651989)
                ·
                  refine ⟨2418867240165983896202437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51602501123540989785651989 2418867240165983896202437)
                  ·
                    refine ⟨453537607531121980537957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2418867240165983896202437 453537607531121980537957)
                    ·
                      rfl

theorem cell23_2649784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_2649784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649784 prefixEnd_2649784 := by exact prefixLift 2649784
  have htrace : WordTrace (prefixWord ++ tailWord_2649784) baseStart_2649784 baseEnd_2649784 := by
    simpa [prefixWord, tailWord_2649784, baseEnd_2649784] using wordTrace_append hprefix tailTrace_2649784
  have hstable : (prefixWord ++ tailWord_2649784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649784).length < 2 ^ (prefixWord ++ tailWord_2649784).sum := by decide
  have hdescent : baseEnd_2649784 < baseStart_2649784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649788 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_2649788 : Nat := 118140960795 + 2649788 * 2 ^ 59
def prefixEnd_2649788 : Nat := 4983230072969 + 3 ^ 40 * 2649788 * 2
def baseEnd_2649788 : Nat := 453538292171994641987951

theorem tailTrace_2649788 : CollatzResearch.WordTrace tailWord_2649788 prefixEnd_2649788 453538292171994641987951 := by
  unfold tailWord_2649788
  simp only [CollatzResearch.WordTrace]
  refine ⟨48322854062139049303171009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 64430472082852065737561345 48322854062139049303171009)
  ·
    refine ⟨36242140546604286977378257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48322854062139049303171009 36242140546604286977378257)
    ·
      refine ⟨27181605409953215233033693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36242140546604286977378257 27181605409953215233033693)
      ·
        refine ⟨10193102028732455712387635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27181605409953215233033693 10193102028732455712387635)
        ·
          refine ⟨15289653043098683568581453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10193102028732455712387635 15289653043098683568581453)
          ·
            refine ⟨5733619891162006338218045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15289653043098683568581453 5733619891162006338218045)
            ·
              refine ⟨2150107459185752376831767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5733619891162006338218045 2150107459185752376831767)
              ·
                refine ⟨3225161188778628565247651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150107459185752376831767 3225161188778628565247651)
                ·
                  refine ⟨4837741783167942847871477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225161188778628565247651 4837741783167942847871477)
                  ·
                    refine ⟨453538292171994641987951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4837741783167942847871477 453538292171994641987951)
                    ·
                      rfl

theorem cell23_2649788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_2649788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649788 prefixEnd_2649788 := by exact prefixLift 2649788
  have htrace : WordTrace (prefixWord ++ tailWord_2649788) baseStart_2649788 baseEnd_2649788 := by
    simpa [prefixWord, tailWord_2649788, baseEnd_2649788] using wordTrace_append hprefix tailTrace_2649788
  have hstable : (prefixWord ++ tailWord_2649788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649788).length < 2 ^ (prefixWord ++ tailWord_2649788).sum := by decide
  have hdescent : baseEnd_2649788 < baseStart_2649788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649825 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_2649825 : Nat := 118140960795 + 2649825 * 2 ^ 59
def prefixEnd_2649825 : Nat := 4983230072969 + 3 ^ 40 * 2649825 * 2
def baseEnd_2649825 : Nat := 1360633875300200281201183

theorem tailTrace_2649825 : CollatzResearch.WordTrace tailWord_2649825 prefixEnd_2649825 1360633875300200281201183 := by
  unfold tailWord_2649825
  simp only [CollatzResearch.WordTrace]
  refine ⟨96647057625144053925438929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64431371750096035950292619 96647057625144053925438929)
  ·
    refine ⟨72485293218858040444079197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96647057625144053925438929 72485293218858040444079197)
    ·
      refine ⟨27181984957071765166529699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72485293218858040444079197 27181984957071765166529699)
      ·
        refine ⟨40772977435607647749794549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27181984957071765166529699 40772977435607647749794549)
        ·
          refine ⟨3822466634588216976543239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40772977435607647749794549 3822466634588216976543239)
          ·
            refine ⟨5733699951882325464814859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822466634588216976543239 5733699951882325464814859)
            ·
              refine ⟨8600549927823488197222289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5733699951882325464814859 8600549927823488197222289)
              ·
                refine ⟨6450412445867616147916717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8600549927823488197222289 6450412445867616147916717)
                ·
                  refine ⟨2418904667200356055468769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6450412445867616147916717 2418904667200356055468769)
                  ·
                    refine ⟨1814178500400267041601577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418904667200356055468769 1814178500400267041601577)
                    ·
                      refine ⟨1360633875300200281201183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814178500400267041601577 1360633875300200281201183)
                      ·
                        rfl

theorem cell23_2649825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_2649825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649825 prefixEnd_2649825 := by exact prefixLift 2649825
  have htrace : WordTrace (prefixWord ++ tailWord_2649825) baseStart_2649825 baseEnd_2649825 := by
    simpa [prefixWord, tailWord_2649825, baseEnd_2649825] using wordTrace_append hprefix tailTrace_2649825
  have hstable : (prefixWord ++ tailWord_2649825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649825).length < 2 ^ (prefixWord ++ tailWord_2649825).sum := by decide
  have hdescent : baseEnd_2649825 < baseStart_2649825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649841 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_2649841 : Nat := 118140960795 + 2649841 * 2 ^ 59
def prefixEnd_2649841 : Nat := 4983230072969 + 3 ^ 40 * 2649841 * 2
def baseEnd_2649841 : Nat := 1360642090990672218601109

theorem tailTrace_2649841 : CollatzResearch.WordTrace tailWord_2649841 prefixEnd_2649841 1360642090990672218601109 := by
  unfold tailWord_2649841
  simp only [CollatzResearch.WordTrace]
  refine ⟨96647641193086088658021377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 64431760795390725772014251 96647641193086088658021377)
  ·
    refine ⟨72485730894814566493516033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96647641193086088658021377 72485730894814566493516033)
    ·
      refine ⟨54364298171110924870137025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72485730894814566493516033 54364298171110924870137025)
      ·
        refine ⟨40773223628333193652602769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54364298171110924870137025 40773223628333193652602769)
        ·
          refine ⟨30579917721249895239452077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40773223628333193652602769 30579917721249895239452077)
          ·
            refine ⟨11467469145468710714794529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30579917721249895239452077 11467469145468710714794529)
            ·
              refine ⟨8600601859101533036095897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11467469145468710714794529 8600601859101533036095897)
              ·
                refine ⟨6450451394326149777071923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8600601859101533036095897 6450451394326149777071923)
                ·
                  refine ⟨9675677091489224665607885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6450451394326149777071923 9675677091489224665607885)
                  ·
                    refine ⟨3628378909308459249602957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9675677091489224665607885 3628378909308459249602957)
                    ·
                      refine ⟨1360642090990672218601109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3628378909308459249602957 1360642090990672218601109)
                      ·
                        rfl

theorem cell23_2649841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_2649841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649841 prefixEnd_2649841 := by exact prefixLift 2649841
  have htrace : WordTrace (prefixWord ++ tailWord_2649841) baseStart_2649841 baseEnd_2649841 := by
    simpa [prefixWord, tailWord_2649841, baseEnd_2649841] using wordTrace_append hprefix tailTrace_2649841
  have hstable : (prefixWord ++ tailWord_2649841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649841).length < 2 ^ (prefixWord ++ tailWord_2649841).sum := by decide
  have hdescent : baseEnd_2649841 < baseStart_2649841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2649842 : List Nat := [3, 2, 1, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_2649842 : Nat := 118140960795 + 2649842 * 2 ^ 59
def prefixEnd_2649842 : Nat := 4983230072969 + 3 ^ 40 * 2649842 * 2
def baseEnd_2649842 : Nat := 1360642604471326714688605

theorem tailTrace_2649842 : CollatzResearch.WordTrace tailWord_2649842 prefixEnd_2649842 1360642604471326714688605 := by
  unfold tailWord_2649842
  simp only [CollatzResearch.WordTrace]
  refine ⟨24161919416520616457201945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 64431785110721643885871853 24161919416520616457201945)
  ·
    refine ⟨18121439562390462342901459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24161919416520616457201945 18121439562390462342901459)
    ·
      refine ⟨27182159343585693514352189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18121439562390462342901459 27182159343585693514352189)
      ·
        refine ⟨10193309753844635067882071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27182159343585693514352189 10193309753844635067882071)
        ·
          refine ⟨15289964630766952601823107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10193309753844635067882071 15289964630766952601823107)
          ·
            refine ⟨22934946946150428902734661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15289964630766952601823107 22934946946150428902734661)
            ·
              refine ⟨4300302552403205419262749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22934946946150428902734661 4300302552403205419262749)
              ·
                refine ⟨1612613457151202032223531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4300302552403205419262749 1612613457151202032223531)
                ·
                  refine ⟨2418920185726803048335297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612613457151202032223531 2418920185726803048335297)
                  ·
                    refine ⟨1814190139295102286251473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418920185726803048335297 1814190139295102286251473)
                    ·
                      refine ⟨1360642604471326714688605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1814190139295102286251473 1360642604471326714688605)
                      ·
                        rfl

theorem cell23_2649842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_2649842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2649842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2649842 prefixEnd_2649842 := by exact prefixLift 2649842
  have htrace : WordTrace (prefixWord ++ tailWord_2649842) baseStart_2649842 baseEnd_2649842 := by
    simpa [prefixWord, tailWord_2649842, baseEnd_2649842] using wordTrace_append hprefix tailTrace_2649842
  have hstable : (prefixWord ++ tailWord_2649842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2649842).length < 2 ^ (prefixWord ++ tailWord_2649842).sum := by decide
  have hdescent : baseEnd_2649842 < baseStart_2649842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2649842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
