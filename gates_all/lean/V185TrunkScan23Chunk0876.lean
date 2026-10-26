import V185TrunkScan23Chunk0875

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5184586 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_5184586 : Nat := 118140960795 + 5184586 * 2 ^ 59
def prefixEnd_5184586 : Nat := 4983230072969 + 3 ^ 40 * 5184586 * 2
def baseEnd_5184586 : Nat := 2662184612571357517131529

theorem tailTrace_5184586 : CollatzResearch.WordTrace tailWord_5184586 prefixEnd_5184586 2662184612571357517131529 := by
  unfold tailWord_5184586
  simp only [CollatzResearch.WordTrace]
  refine ⟨47274346598784463409773403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126064924263425235759395741 47274346598784463409773403)
  ·
    refine ⟨70911519898176695114660105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47274346598784463409773403 70911519898176695114660105)
    ·
      refine ⟨53183639923632521335995079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70911519898176695114660105 53183639923632521335995079)
      ·
        refine ⟨79775459885448782003992619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53183639923632521335995079 79775459885448782003992619)
        ·
          refine ⟨119663189828173173005988929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79775459885448782003992619 119663189828173173005988929)
          ·
            refine ⟨89747392371129879754491697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119663189828173173005988929 89747392371129879754491697)
            ·
              refine ⟨67310544278347409815868773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89747392371129879754491697 67310544278347409815868773)
              ·
                refine ⟨12620727052190139340475395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67310544278347409815868773 12620727052190139340475395)
                ·
                  refine ⟨18931090578285209010713093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12620727052190139340475395 18931090578285209010713093)
                  ·
                    refine ⟨3549579483428476689508705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18931090578285209010713093 3549579483428476689508705)
                    ·
                      refine ⟨2662184612571357517131529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549579483428476689508705 2662184612571357517131529)
                      ·
                        rfl

theorem cell23_5184586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_5184586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184586 prefixEnd_5184586 := by exact prefixLift 5184586
  have htrace : WordTrace (prefixWord ++ tailWord_5184586) baseStart_5184586 baseEnd_5184586 := by
    simpa [prefixWord, tailWord_5184586, baseEnd_5184586] using wordTrace_append hprefix tailTrace_5184586
  have hstable : (prefixWord ++ tailWord_5184586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184586).length < 2 ^ (prefixWord ++ tailWord_5184586).sum := by decide
  have hdescent : baseEnd_5184586 < baseStart_5184586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184592 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 9]
def baseStart_5184592 : Nat := 118140960795 + 5184592 * 2 ^ 59
def prefixEnd_5184592 : Nat := 4983230072969 + 3 ^ 40 * 5184592 * 2
def baseEnd_5184592 : Nat := 295798632606142721517389

theorem tailTrace_5184592 : CollatzResearch.WordTrace tailWord_5184592 prefixEnd_5184592 295798632606142721517389 := by
  unfold tailWord_5184592
  simp only [CollatzResearch.WordTrace]
  refine ⟨94548802616558058331906015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126065070155410744442541353 94548802616558058331906015)
  ·
    refine ⟨141823203924837087497859023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94548802616558058331906015 141823203924837087497859023)
    ·
      refine ⟨212734805887255631246788535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141823203924837087497859023 212734805887255631246788535)
      ·
        refine ⟨319102208830883446870182803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212734805887255631246788535 319102208830883446870182803)
        ·
          refine ⟨478653313246325170305274205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319102208830883446870182803 478653313246325170305274205)
          ·
            refine ⟨179494992467371938864477827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478653313246325170305274205 179494992467371938864477827)
            ·
              refine ⟨269242488701057908296716741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179494992467371938864477827 269242488701057908296716741)
              ·
                refine ⟨50482966631448357805634389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269242488701057908296716741 50482966631448357805634389)
                ·
                  refine ⟨295798632606142721517389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50482966631448357805634389 295798632606142721517389)
                  ·
                    rfl

theorem cell23_5184592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 9].length) (baseStart_5184592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184592 prefixEnd_5184592 := by exact prefixLift 5184592
  have htrace : WordTrace (prefixWord ++ tailWord_5184592) baseStart_5184592 baseEnd_5184592 := by
    simpa [prefixWord, tailWord_5184592, baseEnd_5184592] using wordTrace_append hprefix tailTrace_5184592
  have hstable : (prefixWord ++ tailWord_5184592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184592).length < 2 ^ (prefixWord ++ tailWord_5184592).sum := by decide
  have hdescent : baseEnd_5184592 < baseStart_5184592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184609 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 7]
def baseStart_5184609 : Nat := 118140960795 + 5184609 * 2 ^ 59
def prefixEnd_5184609 : Nat := 4983230072969 + 3 ^ 40 * 5184609 * 2
def baseEnd_5184609 : Nat := 295799602514045658571547

theorem tailTrace_5184609 : CollatzResearch.WordTrace tailWord_5184609 prefixEnd_5184609 295799602514045658571547 := by
  unfold tailWord_5184609
  simp only [CollatzResearch.WordTrace]
  refine ⟨189098225274054528567180881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126065483516036352378120587 189098225274054528567180881)
  ·
    refine ⟨141823668955540896425385661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189098225274054528567180881 141823668955540896425385661)
    ·
      refine ⟨53183875858327836159519623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141823668955540896425385661 53183875858327836159519623)
      ·
        refine ⟨79775813787491754239279435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53183875858327836159519623 79775813787491754239279435)
        ·
          refine ⟨119663720681237631358919153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79775813787491754239279435 119663720681237631358919153)
          ·
            refine ⟨89747790510928223519189365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119663720681237631358919153 89747790510928223519189365)
            ·
              refine ⟨8413855360399520954924003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89747790510928223519189365 8413855360399520954924003)
              ·
                refine ⟨12620783040599281432386005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8413855360399520954924003 12620783040599281432386005)
                ·
                  refine ⟨295799602514045658571547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12620783040599281432386005 295799602514045658571547)
                  ·
                    rfl

theorem cell23_5184609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 7].length) (baseStart_5184609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184609 prefixEnd_5184609 := by exact prefixLift 5184609
  have htrace : WordTrace (prefixWord ++ tailWord_5184609) baseStart_5184609 baseEnd_5184609 := by
    simpa [prefixWord, tailWord_5184609, baseEnd_5184609] using wordTrace_append hprefix tailTrace_5184609
  have hstable : (prefixWord ++ tailWord_5184609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184609).length < 2 ^ (prefixWord ++ tailWord_5184609).sum := by decide
  have hdescent : baseEnd_5184609 < baseStart_5184609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184649 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_5184649 : Nat := 118140960795 + 5184649 * 2 ^ 59
def prefixEnd_5184649 : Nat := 4983230072969 + 3 ^ 40 * 5184649 * 2
def baseEnd_5184649 : Nat := 2662216961852590770643739

theorem tailTrace_5184649 : CollatzResearch.WordTrace tailWord_5184649 prefixEnd_5184649 2662216961852590770643739 := by
  unfold tailWord_5184649
  simp only [CollatzResearch.WordTrace]
  refine ⟨189099684193909615398637001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126066456129273076932424667 189099684193909615398637001)
  ·
    refine ⟨141824763145432211548977751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189099684193909615398637001 141824763145432211548977751)
    ·
      refine ⟨212737144718148317323466627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141824763145432211548977751 212737144718148317323466627)
      ·
        refine ⟨319105717077222475985199941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212737144718148317323466627 319105717077222475985199941)
        ·
          refine ⟨59832321951979214247224989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319105717077222475985199941 59832321951979214247224989)
          ·
            refine ⟨22437120731992205342709371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59832321951979214247224989 22437120731992205342709371)
            ·
              refine ⟨33655681097988308014064057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22437120731992205342709371 33655681097988308014064057)
              ·
                refine ⟨25241760823491231010548043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33655681097988308014064057 25241760823491231010548043)
                ·
                  refine ⟨37862641235236846515822065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25241760823491231010548043 37862641235236846515822065)
                  ·
                    refine ⟨28396980926427634886866549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37862641235236846515822065 28396980926427634886866549)
                    ·
                      refine ⟨2662216961852590770643739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28396980926427634886866549 2662216961852590770643739)
                      ·
                        rfl

theorem cell23_5184649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_5184649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184649 prefixEnd_5184649 := by exact prefixLift 5184649
  have htrace : WordTrace (prefixWord ++ tailWord_5184649) baseStart_5184649 baseEnd_5184649 := by
    simpa [prefixWord, tailWord_5184649, baseEnd_5184649] using wordTrace_append hprefix tailTrace_5184649
  have hstable : (prefixWord ++ tailWord_5184649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184649).length < 2 ^ (prefixWord ++ tailWord_5184649).sum := by decide
  have hdescent : baseEnd_5184649 < baseStart_5184649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184666 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5184666 : Nat := 118140960795 + 5184666 * 2 ^ 59
def prefixEnd_5184666 : Nat := 4983230072969 + 3 ^ 40 * 5184666 * 2
def baseEnd_5184666 : Nat := 2662225691023717204131161

theorem tailTrace_5184666 : CollatzResearch.WordTrace tailWord_5184666 prefixEnd_5184666 2662225691023717204131161 := by
  unfold tailWord_5184666
  simp only [CollatzResearch.WordTrace]
  refine ⟨47275076058712006825501463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126066869489898684868003901 47275076058712006825501463)
  ·
    refine ⟨70912614088068010238252195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47275076058712006825501463 70912614088068010238252195)
    ·
      refine ⟨106368921132102015357378293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70912614088068010238252195 106368921132102015357378293)
      ·
        refine ⟨9972086356134563939754215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106368921132102015357378293 9972086356134563939754215)
        ·
          refine ⟨14958129534201845909631323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9972086356134563939754215 14958129534201845909631323)
          ·
            refine ⟨22437194301302768864446985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14958129534201845909631323 22437194301302768864446985)
            ·
              refine ⟨16827895725977076648335239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22437194301302768864446985 16827895725977076648335239)
              ·
                refine ⟨25241843588965614972502859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16827895725977076648335239 25241843588965614972502859)
                ·
                  refine ⟨37862765383448422458754289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25241843588965614972502859 37862765383448422458754289)
                  ·
                    refine ⟨28397074037586316844065717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37862765383448422458754289 28397074037586316844065717)
                    ·
                      refine ⟨2662225691023717204131161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28397074037586316844065717 2662225691023717204131161)
                      ·
                        rfl

theorem cell23_5184666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5184666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184666 prefixEnd_5184666 := by exact prefixLift 5184666
  have htrace : WordTrace (prefixWord ++ tailWord_5184666) baseStart_5184666 baseEnd_5184666 := by
    simpa [prefixWord, tailWord_5184666, baseEnd_5184666] using wordTrace_append hprefix tailTrace_5184666
  have hstable : (prefixWord ++ tailWord_5184666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184666).length < 2 ^ (prefixWord ++ tailWord_5184666).sum := by decide
  have hdescent : baseEnd_5184666 < baseStart_5184666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184696 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_5184696 : Nat := 118140960795 + 5184696 * 2 ^ 59
def prefixEnd_5184696 : Nat := 4983230072969 + 3 ^ 40 * 5184696 * 2
def baseEnd_5184696 : Nat := 2662241095443352086756023

theorem tailTrace_5184696 : CollatzResearch.WordTrace tailWord_5184696 prefixEnd_5184696 2662241095443352086756023 := by
  unfold tailWord_5184696
  simp only [CollatzResearch.WordTrace]
  refine ⟨94550699212369671212798971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126067598949826228283731961 94550699212369671212798971)
  ·
    refine ⟨141826048818554506819198457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94550699212369671212798971 141826048818554506819198457)
    ·
      refine ⟨106369536613915880114398843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141826048818554506819198457 106369536613915880114398843)
      ·
        refine ⟨159554304920873820171598265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106369536613915880114398843 159554304920873820171598265)
        ·
          refine ⟨119665728690655365128698699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159554304920873820171598265 119665728690655365128698699)
          ·
            refine ⟨179498593035983047693048049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119665728690655365128698699 179498593035983047693048049)
            ·
              refine ⟨134623944776987285769786037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179498593035983047693048049 134623944776987285769786037)
              ·
                refine ⟨12620994822842558040917441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134623944776987285769786037 12620994822842558040917441)
                ·
                  refine ⟨9465746117131918530688081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12620994822842558040917441 9465746117131918530688081)
                  ·
                    refine ⟨7099309587848938898016061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9465746117131918530688081 7099309587848938898016061)
                    ·
                      refine ⟨2662241095443352086756023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7099309587848938898016061 2662241095443352086756023)
                      ·
                        rfl

theorem cell23_5184696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_5184696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184696 prefixEnd_5184696 := by exact prefixLift 5184696
  have htrace : WordTrace (prefixWord ++ tailWord_5184696) baseStart_5184696 baseEnd_5184696 := by
    simpa [prefixWord, tailWord_5184696, baseEnd_5184696] using wordTrace_append hprefix tailTrace_5184696
  have hstable : (prefixWord ++ tailWord_5184696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184696).length < 2 ^ (prefixWord ++ tailWord_5184696).sum := by decide
  have hdescent : baseEnd_5184696 < baseStart_5184696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184703 : List Nat := [1, 1, 2, 2, 2, 2, 3, 5, 1, 4]
def baseStart_5184703 : Nat := 118140960795 + 5184703 * 2 ^ 59
def prefixEnd_5184703 : Nat := 4983230072969 + 3 ^ 40 * 5184703 * 2
def baseEnd_5184703 : Nat := 887414896602644519789497

theorem tailTrace_5184703 : CollatzResearch.WordTrace tailWord_5184703 prefixEnd_5184703 887414896602644519789497 := by
  unfold tailWord_5184703
  simp only [CollatzResearch.WordTrace]
  refine ⟨189101653735713982621102763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126067769157142655080735175 189101653735713982621102763)
  ·
    refine ⟨283652480603570973931654145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189101653735713982621102763 283652480603570973931654145)
    ·
      refine ⟨212739360452678230448740609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283652480603570973931654145 212739360452678230448740609)
      ·
        refine ⟨159554520339508672836555457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212739360452678230448740609 159554520339508672836555457)
        ·
          refine ⟨119665890254631504627416593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159554520339508672836555457 119665890254631504627416593)
          ·
            refine ⟨89749417690973628470562445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119665890254631504627416593 89749417690973628470562445)
            ·
              refine ⟨33656031634115110676460917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89749417690973628470562445 33656031634115110676460917)
              ·
                refine ⟨3155252965698291625918211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33656031634115110676460917 3155252965698291625918211)
                ·
                  refine ⟨4732879448547437438877317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155252965698291625918211 4732879448547437438877317)
                  ·
                    refine ⟨887414896602644519789497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732879448547437438877317 887414896602644519789497)
                    ·
                      rfl

theorem cell23_5184703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 4].length) (baseStart_5184703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184703 prefixEnd_5184703 := by exact prefixLift 5184703
  have htrace : WordTrace (prefixWord ++ tailWord_5184703) baseStart_5184703 baseEnd_5184703 := by
    simpa [prefixWord, tailWord_5184703, baseEnd_5184703] using wordTrace_append hprefix tailTrace_5184703
  have hstable : (prefixWord ++ tailWord_5184703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184703).length < 2 ^ (prefixWord ++ tailWord_5184703).sum := by decide
  have hdescent : baseEnd_5184703 < baseStart_5184703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184753 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 2, 3, 2]
def baseStart_5184753 : Nat := 118140960795 + 5184753 * 2 ^ 59
def prefixEnd_5184753 : Nat := 4983230072969 + 3 ^ 40 * 5184753 * 2
def baseEnd_5184753 : Nat := 2662270363840658363743261

theorem tailTrace_5184753 : CollatzResearch.WordTrace tailWord_5184753 prefixEnd_5184753 2662270363840658363743261 := by
  unfold tailWord_5184753
  simp only [CollatzResearch.WordTrace]
  refine ⟨189103477385532841160422913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126068984923688560773615275 189103477385532841160422913)
  ·
    refine ⟨141827608039149630870317185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189103477385532841160422913 141827608039149630870317185)
    ·
      refine ⟨106370706029362223152737889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141827608039149630870317185 106370706029362223152737889)
      ·
        refine ⟨79778029522021667364553417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106370706029362223152737889 79778029522021667364553417)
        ·
          refine ⟨59833522141516250523415063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79778029522021667364553417 59833522141516250523415063)
          ·
            refine ⟨89750283212274375785122595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59833522141516250523415063 89750283212274375785122595)
            ·
              refine ⟨134625424818411563677683893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89750283212274375785122595 134625424818411563677683893)
              ·
                refine ⟨12621133576726084094782865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134625424818411563677683893 12621133576726084094782865)
                ·
                  refine ⟨9465850182544563071087149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12621133576726084094782865 9465850182544563071087149)
                  ·
                    refine ⟨3549693818454211151657681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9465850182544563071087149 3549693818454211151657681)
                    ·
                      refine ⟨2662270363840658363743261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549693818454211151657681 2662270363840658363743261)
                      ·
                        rfl

theorem cell23_5184753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_5184753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184753 prefixEnd_5184753 := by exact prefixLift 5184753
  have htrace : WordTrace (prefixWord ++ tailWord_5184753) baseStart_5184753 baseEnd_5184753 := by
    simpa [prefixWord, tailWord_5184753, baseEnd_5184753] using wordTrace_append hprefix tailTrace_5184753
  have hstable : (prefixWord ++ tailWord_5184753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184753).length < 2 ^ (prefixWord ++ tailWord_5184753).sum := by decide
  have hdescent : baseEnd_5184753 < baseStart_5184753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184754 : List Nat := [3, 2, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_5184754 : Nat := 118140960795 + 5184754 * 2 ^ 59
def prefixEnd_5184754 : Nat := 4983230072969 + 3 ^ 40 * 5184754 * 2
def baseEnd_5184754 : Nat := 887423625773770953276919

theorem tailTrace_5184754 : CollatzResearch.WordTrace tailWord_5184754 prefixEnd_5184754 887423625773770953276919 := by
  unfold tailWord_5184754
  simp only [CollatzResearch.WordTrace]
  refine ⟨47275878464632304582802329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126069009239019478887472877 47275878464632304582802329)
  ·
    refine ⟨35456908848474228437101747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47275878464632304582802329 35456908848474228437101747)
    ·
      refine ⟨53185363272711342655652621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35456908848474228437101747 53185363272711342655652621)
      ·
        refine ⟨19944511227266753495869733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53185363272711342655652621 19944511227266753495869733)
        ·
          refine ⟨3739595855112516280475575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19944511227266753495869733 3739595855112516280475575)
          ·
            refine ⟨5609393782668774420713363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739595855112516280475575 5609393782668774420713363)
            ·
              refine ⟨8414090674003161631070045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5609393782668774420713363 8414090674003161631070045)
              ·
                refine ⟨3155284002751185611651267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8414090674003161631070045 3155284002751185611651267)
                ·
                  refine ⟨4732926004126778417476901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155284002751185611651267 4732926004126778417476901)
                  ·
                    refine ⟨887423625773770953276919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4732926004126778417476901 887423625773770953276919)
                    ·
                      rfl

theorem cell23_5184754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_5184754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184754 prefixEnd_5184754 := by exact prefixLift 5184754
  have htrace : WordTrace (prefixWord ++ tailWord_5184754) baseStart_5184754 baseEnd_5184754 := by
    simpa [prefixWord, tailWord_5184754, baseEnd_5184754] using wordTrace_append hprefix tailTrace_5184754
  have hstable : (prefixWord ++ tailWord_5184754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184754).length < 2 ^ (prefixWord ++ tailWord_5184754).sum := by decide
  have hdescent : baseEnd_5184754 < baseStart_5184754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184777 : List Nat := [1, 2, 1, 1, 3, 3, 5, 2, 1, 1, 3]
def baseStart_5184777 : Nat := 118140960795 + 5184777 * 2 ^ 59
def prefixEnd_5184777 : Nat := 4983230072969 + 3 ^ 40 * 5184777 * 2
def baseEnd_5184777 : Nat := 2662282687376366269843151

theorem tailTrace_5184777 : CollatzResearch.WordTrace tailWord_5184777 prefixEnd_5184777 2662282687376366269843151 := by
  unfold tailWord_5184777
  simp only [CollatzResearch.WordTrace]
  refine ⟨189104352737445893259296585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126069568491630595506197723 189104352737445893259296585)
  ·
    refine ⟨141828264553084419944472439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189104352737445893259296585 141828264553084419944472439)
    ·
      refine ⟨212742396829626629916708659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141828264553084419944472439 212742396829626629916708659)
      ·
        refine ⟨319113595244439944875062989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212742396829626629916708659 319113595244439944875062989)
        ·
          refine ⟨119667598216664979328148621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319113595244439944875062989 119667598216664979328148621)
          ·
            refine ⟨44875349331249367248055733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119667598216664979328148621 44875349331249367248055733)
            ·
              refine ⟨4207063999804628179505225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44875349331249367248055733 4207063999804628179505225)
              ·
                refine ⟨3155297999853471134628919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4207063999804628179505225 3155297999853471134628919)
                ·
                  refine ⟨4732946999780206701943379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155297999853471134628919 4732946999780206701943379)
                  ·
                    refine ⟨7099420499670310052915069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4732946999780206701943379 7099420499670310052915069)
                    ·
                      refine ⟨2662282687376366269843151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7099420499670310052915069 2662282687376366269843151)
                      ·
                        rfl

theorem cell23_5184777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 1, 3].length) (baseStart_5184777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184777 prefixEnd_5184777 := by exact prefixLift 5184777
  have htrace : WordTrace (prefixWord ++ tailWord_5184777) baseStart_5184777 baseEnd_5184777 := by
    simpa [prefixWord, tailWord_5184777, baseEnd_5184777] using wordTrace_append hprefix tailTrace_5184777
  have hstable : (prefixWord ++ tailWord_5184777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184777).length < 2 ^ (prefixWord ++ tailWord_5184777).sum := by decide
  have hdescent : baseEnd_5184777 < baseStart_5184777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184796 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_5184796 : Nat := 118140960795 + 5184796 * 2 ^ 59
def prefixEnd_5184796 : Nat := 4983230072969 + 3 ^ 40 * 5184796 * 2
def baseEnd_5184796 : Nat := 2662292443508801695505563

theorem tailTrace_5184796 : CollatzResearch.WordTrace tailWord_5184796 prefixEnd_5184796 2662292443508801695505563 := by
  unfold tailWord_5184796
  simp only [CollatzResearch.WordTrace]
  refine ⟨94552522862188529752119121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126070030482918039669492161 94552522862188529752119121)
  ·
    refine ⟨70914392146641397314089341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94552522862188529752119121 70914392146641397314089341)
    ·
      refine ⟨26592897054990523992783503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70914392146641397314089341 26592897054990523992783503)
      ·
        refine ⟨39889345582485785989175255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26592897054990523992783503 39889345582485785989175255)
        ·
          refine ⟨59834018373728678983762883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39889345582485785989175255 59834018373728678983762883)
          ·
            refine ⟨89751027560593018475644325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59834018373728678983762883 89751027560593018475644325)
            ·
              refine ⟨16828317667611190964183311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89751027560593018475644325 16828317667611190964183311)
              ·
                refine ⟨25242476501416786446274967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16828317667611190964183311 25242476501416786446274967)
                ·
                  refine ⟨37863714752125179669412451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25242476501416786446274967 37863714752125179669412451)
                  ·
                    refine ⟨56795572128187769504118677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37863714752125179669412451 56795572128187769504118677)
                    ·
                      refine ⟨2662292443508801695505563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56795572128187769504118677 2662292443508801695505563)
                      ·
                        rfl

theorem cell23_5184796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_5184796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184796 prefixEnd_5184796 := by exact prefixLift 5184796
  have htrace : WordTrace (prefixWord ++ tailWord_5184796) baseStart_5184796 baseEnd_5184796 := by
    simpa [prefixWord, tailWord_5184796, baseEnd_5184796] using wordTrace_append hprefix tailTrace_5184796
  have hstable : (prefixWord ++ tailWord_5184796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184796).length < 2 ^ (prefixWord ++ tailWord_5184796).sum := by decide
  have hdescent : baseEnd_5184796 < baseStart_5184796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184803 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 3]
def baseStart_5184803 : Nat := 118140960795 + 5184803 * 2 ^ 59
def prefixEnd_5184803 : Nat := 4983230072969 + 3 ^ 40 * 5184803 * 2
def baseEnd_5184803 : Nat := 2662296037873383168118031

theorem tailTrace_5184803 : CollatzResearch.WordTrace tailWord_5184803 prefixEnd_5184803 2662296037873383168118031 := by
  unfold tailWord_5184803
  simp only [CollatzResearch.WordTrace]
  refine ⟨189105301035351699699743063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126070200690234466466495375 189105301035351699699743063)
  ·
    refine ⟨283657951553027549549614595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189105301035351699699743063 283657951553027549549614595)
    ·
      refine ⟨425486927329541324324421893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283657951553027549549614595 425486927329541324324421893)
      ·
        refine ⟨79778798874288998310829105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 425486927329541324324421893 79778798874288998310829105)
        ·
          refine ⟨59834099155716748733121829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79778798874288998310829105 59834099155716748733121829)
          ·
            refine ⟨11218893591696890387460343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59834099155716748733121829 11218893591696890387460343)
            ·
              refine ⟨16828340387545335581190515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11218893591696890387460343 16828340387545335581190515)
              ·
                refine ⟨25242510581318003371785773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16828340387545335581190515 25242510581318003371785773)
                ·
                  refine ⟨9465941467994251264419665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25242510581318003371785773 9465941467994251264419665)
                  ·
                    refine ⟨7099456100995688448314749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9465941467994251264419665 7099456100995688448314749)
                    ·
                      refine ⟨2662296037873383168118031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7099456100995688448314749 2662296037873383168118031)
                      ·
                        rfl

theorem cell23_5184803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_5184803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184803 prefixEnd_5184803 := by exact prefixLift 5184803
  have htrace : WordTrace (prefixWord ++ tailWord_5184803) baseStart_5184803 baseEnd_5184803 := by
    simpa [prefixWord, tailWord_5184803, baseEnd_5184803] using wordTrace_append hprefix tailTrace_5184803
  have hstable : (prefixWord ++ tailWord_5184803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184803).length < 2 ^ (prefixWord ++ tailWord_5184803).sum := by decide
  have hdescent : baseEnd_5184803 < baseStart_5184803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184856 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_5184856 : Nat := 118140960795 + 5184856 * 2 ^ 59
def prefixEnd_5184856 : Nat := 4983230072969 + 3 ^ 40 * 5184856 * 2
def baseEnd_5184856 : Nat := 2662323252348071460755287

theorem tailTrace_5184856 : CollatzResearch.WordTrace tailWord_5184856 prefixEnd_5184856 2662323252348071460755287 := by
  unfold tailWord_5184856
  simp only [CollatzResearch.WordTrace]
  refine ⟨94553617052079844875711211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126071489402773126500948281 94553617052079844875711211)
  ·
    refine ⟨141830425578119767313566817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94553617052079844875711211 141830425578119767313566817)
    ·
      refine ⟨106372819183589825485175113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141830425578119767313566817 106372819183589825485175113)
      ·
        refine ⟨79779614387692369113881335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106372819183589825485175113 79779614387692369113881335)
        ·
          refine ⟨119669421581538553670822003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79779614387692369113881335 119669421581538553670822003)
          ·
            refine ⟨179504132372307830506233005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119669421581538553670822003 179504132372307830506233005)
            ·
              refine ⟨67314049639615436439837377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179504132372307830506233005 67314049639615436439837377)
              ·
                refine ⟨50485537229711577329878033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67314049639615436439837377 50485537229711577329878033)
                ·
                  refine ⟨37864152922283682997408525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50485537229711577329878033 37864152922283682997408525)
                  ·
                    refine ⟨14199057345856381124028197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37864152922283682997408525 14199057345856381124028197)
                    ·
                      refine ⟨2662323252348071460755287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14199057345856381124028197 2662323252348071460755287)
                      ·
                        rfl

theorem cell23_5184856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_5184856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184856 prefixEnd_5184856 := by exact prefixLift 5184856
  have htrace : WordTrace (prefixWord ++ tailWord_5184856) baseStart_5184856 baseEnd_5184856 := by
    simpa [prefixWord, tailWord_5184856, baseEnd_5184856] using wordTrace_append hprefix tailTrace_5184856
  have hstable : (prefixWord ++ tailWord_5184856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184856).length < 2 ^ (prefixWord ++ tailWord_5184856).sum := by decide
  have hdescent : baseEnd_5184856 < baseStart_5184856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184873 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 3, 4, 2]
def baseStart_5184873 : Nat := 118140960795 + 5184873 * 2 ^ 59
def prefixEnd_5184873 : Nat := 4983230072969 + 3 ^ 40 * 5184873 * 2
def baseEnd_5184873 : Nat := 2662331981519197894242709

theorem tailTrace_5184873 : CollatzResearch.WordTrace tailWord_5184873 prefixEnd_5184873 2662331981519197894242709 := by
  unfold tailWord_5184873
  simp only [CollatzResearch.WordTrace]
  refine ⟨189107854145098101654791273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126071902763398734436527515 189107854145098101654791273)
  ·
    refine ⟨141830890608823576241093455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189107854145098101654791273 141830890608823576241093455)
    ·
      refine ⟨212746335913235364361640183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141830890608823576241093455 212746335913235364361640183)
      ·
        refine ⟨319119503869853046542460275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212746335913235364361640183 319119503869853046542460275)
        ·
          refine ⟨478679255804779569813690413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319119503869853046542460275 478679255804779569813690413)
          ·
            refine ⟨179504720926792338680133905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478679255804779569813690413 179504720926792338680133905)
            ·
              refine ⟨134628540695094254010100429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179504720926792338680133905 134628540695094254010100429)
              ·
                refine ⟨50485702760660345253787661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134628540695094254010100429 50485702760660345253787661)
                ·
                  refine ⟨18932138535247629470170373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50485702760660345253787661 18932138535247629470170373)
                  ·
                    refine ⟨3549775975358930525656945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18932138535247629470170373 3549775975358930525656945)
                    ·
                      refine ⟨2662331981519197894242709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549775975358930525656945 2662331981519197894242709)
                      ·
                        rfl

theorem cell23_5184873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 4, 2].length) (baseStart_5184873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184873 prefixEnd_5184873 := by exact prefixLift 5184873
  have htrace : WordTrace (prefixWord ++ tailWord_5184873) baseStart_5184873 baseEnd_5184873 := by
    simpa [prefixWord, tailWord_5184873, baseEnd_5184873] using wordTrace_append hprefix tailTrace_5184873
  have hstable : (prefixWord ++ tailWord_5184873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184873).length < 2 ^ (prefixWord ++ tailWord_5184873).sum := by decide
  have hdescent : baseEnd_5184873 < baseStart_5184873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184877 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_5184877 : Nat := 118140960795 + 5184877 * 2 ^ 59
def prefixEnd_5184877 : Nat := 4983230072969 + 3 ^ 40 * 5184877 * 2
def baseEnd_5184877 : Nat := 2662334035441815878592691

theorem tailTrace_5184877 : CollatzResearch.WordTrace tailWord_5184877 prefixEnd_5184877 2662334035441815878592691 := by
  unfold tailWord_5184877
  simp only [CollatzResearch.WordTrace]
  refine ⟨189108000037083610337936885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126072000024722406891957923 189108000037083610337936885)
  ·
    refine ⟨17728875003476588469181583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189108000037083610337936885 17728875003476588469181583)
    ·
      refine ⟨26593312505214882703772375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17728875003476588469181583 26593312505214882703772375)
      ·
        refine ⟨39889968757822324055658563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26593312505214882703772375 39889968757822324055658563)
        ·
          refine ⟨59834953136733486083487845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39889968757822324055658563 59834953136733486083487845)
          ·
            refine ⟨11219053713137528640653971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59834953136733486083487845 11219053713137528640653971)
            ·
              refine ⟨16828580569706292960980957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11219053713137528640653971 16828580569706292960980957)
              ·
                refine ⟨6310717713639859860367859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16828580569706292960980957 6310717713639859860367859)
                ·
                  refine ⟨9466076570459789790551789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310717713639859860367859 9466076570459789790551789)
                  ·
                    refine ⟨3549778713922421171456921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9466076570459789790551789 3549778713922421171456921)
                    ·
                      refine ⟨2662334035441815878592691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549778713922421171456921 2662334035441815878592691)
                      ·
                        rfl

theorem cell23_5184877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_5184877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184877 prefixEnd_5184877 := by exact prefixLift 5184877
  have htrace : WordTrace (prefixWord ++ tailWord_5184877) baseStart_5184877 baseEnd_5184877 := by
    simpa [prefixWord, tailWord_5184877, baseEnd_5184877] using wordTrace_append hprefix tailTrace_5184877
  have hstable : (prefixWord ++ tailWord_5184877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184877).length < 2 ^ (prefixWord ++ tailWord_5184877).sum := by decide
  have hdescent : baseEnd_5184877 < baseStart_5184877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184890 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2]
def baseStart_5184890 : Nat := 118140960795 + 5184890 * 2 ^ 59
def prefixEnd_5184890 : Nat := 4983230072969 + 3 ^ 40 * 5184890 * 2
def baseEnd_5184890 : Nat := 2662340710690324327730131

theorem tailTrace_5184890 : CollatzResearch.WordTrace tailWord_5184890 prefixEnd_5184890 2662340710690324327730131 := by
  unfold tailWord_5184890
  simp only [CollatzResearch.WordTrace]
  refine ⟨47277118546509128389540031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126072316124024342372106749 47277118546509128389540031)
  ·
    refine ⟨70915677819763692584310047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47277118546509128389540031 70915677819763692584310047)
    ·
      refine ⟨106373516729645538876465071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70915677819763692584310047 106373516729645538876465071)
      ·
        refine ⟨159560275094468308314697607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106373516729645538876465071 159560275094468308314697607)
        ·
          refine ⟨239340412641702462472046411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159560275094468308314697607 239340412641702462472046411)
          ·
            refine ⟨359010618962553693708069617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239340412641702462472046411 359010618962553693708069617)
            ·
              refine ⟨269257964221915270281052213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359010618962553693708069617 269257964221915270281052213)
              ·
                refine ⟨25242934145804556588848645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 269257964221915270281052213 25242934145804556588848645)
                ·
                  refine ⟨4733050152338354360409121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25242934145804556588848645 4733050152338354360409121)
                  ·
                    refine ⟨3549787614253765770306841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4733050152338354360409121 3549787614253765770306841)
                    ·
                      refine ⟨2662340710690324327730131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549787614253765770306841 2662340710690324327730131)
                      ·
                        rfl

theorem cell23_5184890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_5184890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184890 prefixEnd_5184890 := by exact prefixLift 5184890
  have htrace : WordTrace (prefixWord ++ tailWord_5184890) baseStart_5184890 baseEnd_5184890 := by
    simpa [prefixWord, tailWord_5184890, baseEnd_5184890] using wordTrace_append hprefix tailTrace_5184890
  have hstable : (prefixWord ++ tailWord_5184890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184890).length < 2 ^ (prefixWord ++ tailWord_5184890).sum := by decide
  have hdescent : baseEnd_5184890 < baseStart_5184890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184903 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_5184903 : Nat := 118140960795 + 5184903 * 2 ^ 59
def prefixEnd_5184903 : Nat := 4983230072969 + 3 ^ 40 * 5184903 * 2
def baseEnd_5184903 : Nat := 2662347385938832776867571

theorem tailTrace_5184903 : CollatzResearch.WordTrace tailWord_5184903 prefixEnd_5184903 2662347385938832776867571 := by
  unfold tailWord_5184903
  simp only [CollatzResearch.WordTrace]
  refine ⟨189108948334989416778383363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126072632223326277852255575 189108948334989416778383363)
  ·
    refine ⟨283663422502484125167575045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189108948334989416778383363 283663422502484125167575045)
    ·
      refine ⟨53186891719215773468920321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283663422502484125167575045 53186891719215773468920321)
      ·
        refine ⟨39890168789411830101690241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53186891719215773468920321 39890168789411830101690241)
        ·
          refine ⟨29917626592058872576267681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39890168789411830101690241 29917626592058872576267681)
          ·
            refine ⟨22438219944044154432200761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29917626592058872576267681 22438219944044154432200761)
            ·
              refine ⟨16828664958033115824150571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22438219944044154432200761 16828664958033115824150571)
              ·
                refine ⟨25242997437049673736225857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16828664958033115824150571 25242997437049673736225857)
                ·
                  refine ⟨18932248077787255302169393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25242997437049673736225857 18932248077787255302169393)
                  ·
                    refine ⟨14199186058340441476627045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18932248077787255302169393 14199186058340441476627045)
                    ·
                      refine ⟨2662347385938832776867571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14199186058340441476627045 2662347385938832776867571)
                      ·
                        rfl

theorem cell23_5184903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_5184903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184903 prefixEnd_5184903 := by exact prefixLift 5184903
  have htrace : WordTrace (prefixWord ++ tailWord_5184903) baseStart_5184903 baseEnd_5184903 := by
    simpa [prefixWord, tailWord_5184903, baseEnd_5184903] using wordTrace_append hprefix tailTrace_5184903
  have hstable : (prefixWord ++ tailWord_5184903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184903).length < 2 ^ (prefixWord ++ tailWord_5184903).sum := by decide
  have hdescent : baseEnd_5184903 < baseStart_5184903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184962 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5184962 : Nat := 118140960795 + 5184962 * 2 ^ 59
def prefixEnd_5184962 : Nat := 4983230072969 + 3 ^ 40 * 5184962 * 2
def baseEnd_5184962 : Nat := 2662377681297448046029801

theorem tailTrace_5184962 : CollatzResearch.WordTrace tailWord_5184962 prefixEnd_5184962 2662377681297448046029801 := by
  unfold tailWord_5184962
  simp only [CollatzResearch.WordTrace]
  refine ⟨47277775060443917463695285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126074066827850446569854093 47277775060443917463695285)
  ·
    refine ⟨4432291411916617262221433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47277775060443917463695285 4432291411916617262221433)
    ·
      refine ⟨3324218558937462946666075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4432291411916617262221433 3324218558937462946666075)
      ·
        refine ⟨4986327838406194419999113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3324218558937462946666075 4986327838406194419999113)
        ·
          refine ⟨3739745878804645814999335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4986327838406194419999113 3739745878804645814999335)
          ·
            refine ⟨5609618818206968722499003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739745878804645814999335 5609618818206968722499003)
            ·
              refine ⟨8414428227310453083748505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5609618818206968722499003 8414428227310453083748505)
              ·
                refine ⟨6310821170482839812811379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8414428227310453083748505 6310821170482839812811379)
                ·
                  refine ⟨9466231755724259719217069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310821170482839812811379 9466231755724259719217069)
                  ·
                    refine ⟨3549836908396597394706401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9466231755724259719217069 3549836908396597394706401)
                    ·
                      refine ⟨2662377681297448046029801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549836908396597394706401 2662377681297448046029801)
                      ·
                        rfl

theorem cell23_5184962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5184962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184962 prefixEnd_5184962 := by exact prefixLift 5184962
  have htrace : WordTrace (prefixWord ++ tailWord_5184962) baseStart_5184962 baseEnd_5184962 := by
    simpa [prefixWord, tailWord_5184962, baseEnd_5184962] using wordTrace_append hprefix tailTrace_5184962
  have hstable : (prefixWord ++ tailWord_5184962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184962).length < 2 ^ (prefixWord ++ tailWord_5184962).sum := by decide
  have hdescent : baseEnd_5184962 < baseStart_5184962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5184983 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_5184983 : Nat := 118140960795 + 5184983 * 2 ^ 59
def prefixEnd_5184983 : Nat := 4983230072969 + 3 ^ 40 * 5184983 * 2
def baseEnd_5184983 : Nat := 2662388464391192463867203

theorem tailTrace_5184983 : CollatzResearch.WordTrace tailWord_5184983 prefixEnd_5184983 2662388464391192463867203 := by
  unfold tailWord_5184983
  simp only [CollatzResearch.WordTrace]
  refine ⟨189111866174699590441295603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126074577449799726960863735 189111866174699590441295603)
  ·
    refine ⟨283667799262049385661943405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189111866174699590441295603 283667799262049385661943405)
    ·
      refine ⟨106375424723268519623228777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283667799262049385661943405 106375424723268519623228777)
      ·
        refine ⟨79781568542451389717421583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106375424723268519623228777 79781568542451389717421583)
        ·
          refine ⟨119672352813677084576132375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79781568542451389717421583 119672352813677084576132375)
          ·
            refine ⟨179508529220515626864198563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119672352813677084576132375 179508529220515626864198563)
            ·
              refine ⟨269262793830773440296297845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179508529220515626864198563 269262793830773440296297845)
              ·
                refine ⟨25243386921635010027777923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 269262793830773440296297845 25243386921635010027777923)
                ·
                  refine ⟨37865080382452515041666885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25243386921635010027777923 37865080382452515041666885)
                  ·
                    refine ⟨7099702571709846570312541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37865080382452515041666885 7099702571709846570312541)
                    ·
                      refine ⟨2662388464391192463867203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7099702571709846570312541 2662388464391192463867203)
                      ·
                        rfl

theorem cell23_5184983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_5184983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5184983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5184983 prefixEnd_5184983 := by exact prefixLift 5184983
  have htrace : WordTrace (prefixWord ++ tailWord_5184983) baseStart_5184983 baseEnd_5184983 := by
    simpa [prefixWord, tailWord_5184983, baseEnd_5184983] using wordTrace_append hprefix tailTrace_5184983
  have hstable : (prefixWord ++ tailWord_5184983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5184983).length < 2 ^ (prefixWord ++ tailWord_5184983).sum := by decide
  have hdescent : baseEnd_5184983 < baseStart_5184983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5184983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185000 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_5185000 : Nat := 118140960795 + 5185000 * 2 ^ 59
def prefixEnd_5185000 : Nat := 4983230072969 + 3 ^ 40 * 5185000 * 2
def baseEnd_5185000 : Nat := 2662397193562318897354625

theorem tailTrace_5185000 : CollatzResearch.WordTrace tailWord_5185000 prefixEnd_5185000 2662397193562318897354625 := by
  unfold tailWord_5185000
  simp only [CollatzResearch.WordTrace]
  refine ⟨94556243107819001172332227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126074990810425334896442969 94556243107819001172332227)
  ·
    refine ⟨141834364661728501758498341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94556243107819001172332227 141834364661728501758498341)
    ·
      refine ⟨26593943374074094079718439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141834364661728501758498341 26593943374074094079718439)
      ·
        refine ⟨39890915061111141119577659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26593943374074094079718439 39890915061111141119577659)
        ·
          refine ⟨59836372591666711679366489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39890915061111141119577659 59836372591666711679366489)
          ·
            refine ⟨44877279443750033759524867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59836372591666711679366489 44877279443750033759524867)
            ·
              refine ⟨67315919165625050639287301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44877279443750033759524867 67315919165625050639287301)
              ·
                refine ⟨12621734843554696994866369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67315919165625050639287301 12621734843554696994866369)
                ·
                  refine ⟨9466301132666022746149777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12621734843554696994866369 9466301132666022746149777)
                  ·
                    refine ⟨7099725849499517059612333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9466301132666022746149777 7099725849499517059612333)
                    ·
                      refine ⟨2662397193562318897354625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7099725849499517059612333 2662397193562318897354625)
                      ·
                        rfl

theorem cell23_5185000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_5185000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185000 prefixEnd_5185000 := by exact prefixLift 5185000
  have htrace : WordTrace (prefixWord ++ tailWord_5185000) baseStart_5185000 baseEnd_5185000 := by
    simpa [prefixWord, tailWord_5185000, baseEnd_5185000] using wordTrace_append hprefix tailTrace_5185000
  have hstable : (prefixWord ++ tailWord_5185000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185000).length < 2 ^ (prefixWord ++ tailWord_5185000).sum := by decide
  have hdescent : baseEnd_5185000 < baseStart_5185000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185033 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 3, 5]
def baseStart_5185033 : Nat := 118140960795 + 5185033 * 2 ^ 59
def prefixEnd_5185033 : Nat := 4983230072969 + 3 ^ 40 * 5185033 * 2
def baseEnd_5185033 : Nat := 887471379474639089413991

theorem tailTrace_5185033 : CollatzResearch.WordTrace tailWord_5185033 prefixEnd_5185033 887471379474639089413991 := by
  unfold tailWord_5185033
  simp only [CollatzResearch.WordTrace]
  refine ⟨189113689824518448980615753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126075793216345632653743835 189113689824518448980615753)
  ·
    refine ⟨141835267368388836735461815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189113689824518448980615753 141835267368388836735461815)
    ·
      refine ⟨212752901052583255103192723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141835267368388836735461815 212752901052583255103192723)
      ·
        refine ⟨319129351578874882654789085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212752901052583255103192723 319129351578874882654789085)
        ·
          refine ⟨119673506842078080995545907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319129351578874882654789085 119673506842078080995545907)
          ·
            refine ⟨179510260263117121493318861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119673506842078080995545907 179510260263117121493318861)
            ·
              refine ⟨67316347598668920559994573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179510260263117121493318861 67316347598668920559994573)
              ·
                refine ⟨25243630349500845209997965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67316347598668920559994573 25243630349500845209997965)
                ·
                  refine ⟨9466361381062816953749237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25243630349500845209997965 9466361381062816953749237)
                  ·
                    refine ⟨887471379474639089413991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9466361381062816953749237 887471379474639089413991)
                    ·
                      rfl

theorem cell23_5185033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_5185033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185033 prefixEnd_5185033 := by exact prefixLift 5185033
  have htrace : WordTrace (prefixWord ++ tailWord_5185033) baseStart_5185033 baseEnd_5185033 := by
    simpa [prefixWord, tailWord_5185033, baseEnd_5185033] using wordTrace_append hprefix tailTrace_5185033
  have hstable : (prefixWord ++ tailWord_5185033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185033).length < 2 ^ (prefixWord ++ tailWord_5185033).sum := by decide
  have hdescent : baseEnd_5185033 < baseStart_5185033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185080 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 1, 6]
def baseStart_5185080 : Nat := 118140960795 + 5185080 * 2 ^ 59
def prefixEnd_5185080 : Nat := 4983230072969 + 3 ^ 40 * 5185080 * 2
def baseEnd_5185080 : Nat := 887479424004892861451419

theorem tailTrace_5185080 : CollatzResearch.WordTrace tailWord_5185080 prefixEnd_5185080 887479424004892861451419 := by
  unfold tailWord_5185080
  simp only [CollatzResearch.WordTrace]
  refine ⟨94557702027674088003788347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126076936036898784005051129 94557702027674088003788347)
  ·
    refine ⟨141836553041511132005682521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94557702027674088003788347 141836553041511132005682521)
    ·
      refine ⟨106377414781133349004261891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141836553041511132005682521 106377414781133349004261891)
      ·
        refine ⟨159566122171700023506392837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106377414781133349004261891 159566122171700023506392837)
        ·
          refine ⟨29918647907193754407448657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159566122171700023506392837 29918647907193754407448657)
          ·
            refine ⟨22438985930395315805586493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29918647907193754407448657 22438985930395315805586493)
            ·
              refine ⟨8414619723898243427094935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22438985930395315805586493 8414619723898243427094935)
              ·
                refine ⟨12621929585847365140642403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8414619723898243427094935 12621929585847365140642403)
                ·
                  refine ⟨18932894378771047710963605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12621929585847365140642403 18932894378771047710963605)
                  ·
                    refine ⟨887479424004892861451419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18932894378771047710963605 887479424004892861451419)
                    ·
                      rfl

theorem cell23_5185080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_5185080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185080 prefixEnd_5185080 := by exact prefixLift 5185080
  have htrace : WordTrace (prefixWord ++ tailWord_5185080) baseStart_5185080 baseEnd_5185080 := by
    simpa [prefixWord, tailWord_5185080, baseEnd_5185080] using wordTrace_append hprefix tailTrace_5185080
  have hstable : (prefixWord ++ tailWord_5185080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185080).length < 2 ^ (prefixWord ++ tailWord_5185080).sum := by decide
  have hdescent : baseEnd_5185080 < baseStart_5185080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185087 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 4]
def baseStart_5185087 : Nat := 118140960795 + 5185087 * 2 ^ 59
def prefixEnd_5185087 : Nat := 4983230072969 + 3 ^ 40 * 5185087 * 2
def baseEnd_5185087 : Nat := 2662441866379260056966725

theorem tailTrace_5185087 : CollatzResearch.WordTrace tailWord_5185087 prefixEnd_5185087 2662441866379260056966725 := by
  unfold tailWord_5185087
  simp only [CollatzResearch.WordTrace]
  refine ⟨189115659366322816203081515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126077106244215210802054343 189115659366322816203081515)
  ·
    refine ⟨283673489049484224304622273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189115659366322816203081515 283673489049484224304622273)
    ·
      refine ⟨212755116787113168228466705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283673489049484224304622273 212755116787113168228466705)
      ·
        refine ⟨159566337590334876171350029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212755116787113168228466705 159566337590334876171350029)
        ·
          refine ⟨59837376596375578564256261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159566337590334876171350029 59837376596375578564256261)
          ·
            refine ⟨11219508111820420980798049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59837376596375578564256261 11219508111820420980798049)
            ·
              refine ⟨8414631083865315735598537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11219508111820420980798049 8414631083865315735598537)
              ·
                refine ⟨6310973312898986801698903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8414631083865315735598537 6310973312898986801698903)
                ·
                  refine ⟨9466459969348480202548355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6310973312898986801698903 9466459969348480202548355)
                  ·
                    refine ⟨14199689954022720303822533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9466459969348480202548355 14199689954022720303822533)
                    ·
                      refine ⟨2662441866379260056966725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14199689954022720303822533 2662441866379260056966725)
                      ·
                        rfl

theorem cell23_5185087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_5185087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185087 prefixEnd_5185087 := by exact prefixLift 5185087
  have htrace : WordTrace (prefixWord ++ tailWord_5185087) baseStart_5185087 baseEnd_5185087 := by
    simpa [prefixWord, tailWord_5185087, baseEnd_5185087] using wordTrace_append hprefix tailTrace_5185087
  have hstable : (prefixWord ++ tailWord_5185087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185087).length < 2 ^ (prefixWord ++ tailWord_5185087).sum := by decide
  have hdescent : baseEnd_5185087 < baseStart_5185087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185093 : List Nat := [1, 3, 1, 1, 1, 4, 3, 9]
def baseStart_5185093 : Nat := 118140960795 + 5185093 * 2 ^ 59
def prefixEnd_5185093 : Nat := 4983230072969 + 3 ^ 40 * 5185093 * 2
def baseEnd_5185093 : Nat := 98609072120858779018211

theorem tailTrace_5185093 : CollatzResearch.WordTrace tailWord_5185093 prefixEnd_5185093 98609072120858779018211 := by
  unfold tailWord_5185093
  simp only [CollatzResearch.WordTrace]
  refine ⟨189115878204301079227799933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126077252136200719485199955 189115878204301079227799933)
  ·
    refine ⟨70918454326612904710424975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189115878204301079227799933 70918454326612904710424975)
    ·
      refine ⟨106377681489919357065637463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70918454326612904710424975 106377681489919357065637463)
      ·
        refine ⟨159566522234879035598456195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106377681489919357065637463 159566522234879035598456195)
        ·
          refine ⟨239349783352318553397684293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159566522234879035598456195 239349783352318553397684293)
          ·
            refine ⟨44878084378559728762065805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239349783352318553397684293 44878084378559728762065805)
            ·
              refine ⟨16829281641959898285774677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44878084378559728762065805 16829281641959898285774677)
              ·
                refine ⟨98609072120858779018211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16829281641959898285774677 98609072120858779018211)
                ·
                  rfl

theorem cell23_5185093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 9].length) (baseStart_5185093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185093 prefixEnd_5185093 := by exact prefixLift 5185093
  have htrace : WordTrace (prefixWord ++ tailWord_5185093) baseStart_5185093 baseEnd_5185093 := by
    simpa [prefixWord, tailWord_5185093, baseEnd_5185093] using wordTrace_append hprefix tailTrace_5185093
  have hstable : (prefixWord ++ tailWord_5185093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185093).length < 2 ^ (prefixWord ++ tailWord_5185093).sum := by decide
  have hdescent : baseEnd_5185093 < baseStart_5185093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185141 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5185141 : Nat := 118140960795 + 5185141 * 2 ^ 59
def prefixEnd_5185141 : Nat := 4983230072969 + 3 ^ 40 * 5185141 * 2
def baseEnd_5185141 : Nat := 2662469594334602845691477

theorem tailTrace_5185141 : CollatzResearch.WordTrace tailWord_5185141 prefixEnd_5185141 2662469594334602845691477 := by
  unfold tailWord_5185141
  simp only [CollatzResearch.WordTrace]
  refine ⟨189117628908127183425547277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126078419272084788950364851 189117628908127183425547277)
  ·
    refine ⟨70919110840547693784580229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189117628908127183425547277 70919110840547693784580229)
    ·
      refine ⟨13297333282602692584608793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70919110840547693784580229 13297333282602692584608793)
      ·
        refine ⟨9972999961952019438456595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13297333282602692584608793 9972999961952019438456595)
        ·
          refine ⟨14959499942928029157684893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9972999961952019438456595 14959499942928029157684893)
          ·
            refine ⟨5609812478598010934131835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14959499942928029157684893 5609812478598010934131835)
            ·
              refine ⟨8414718717897016401197753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5609812478598010934131835 8414718717897016401197753)
              ·
                refine ⟨6311039038422762300898315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8414718717897016401197753 6311039038422762300898315)
                ·
                  refine ⟨9466558557634143451347473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6311039038422762300898315 9466558557634143451347473)
                  ·
                    refine ⟨7099918918225607588510605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9466558557634143451347473 7099918918225607588510605)
                    ·
                      refine ⟨2662469594334602845691477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7099918918225607588510605 2662469594334602845691477)
                      ·
                        rfl

theorem cell23_5185141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5185141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185141 prefixEnd_5185141 := by exact prefixLift 5185141
  have htrace : WordTrace (prefixWord ++ tailWord_5185141) baseStart_5185141 baseEnd_5185141 := by
    simpa [prefixWord, tailWord_5185141, baseEnd_5185141] using wordTrace_append hprefix tailTrace_5185141
  have hstable : (prefixWord ++ tailWord_5185141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185141).length < 2 ^ (prefixWord ++ tailWord_5185141).sum := by decide
  have hdescent : baseEnd_5185141 < baseStart_5185141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185143 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_5185143 : Nat := 118140960795 + 5185143 * 2 ^ 59
def prefixEnd_5185143 : Nat := 4983230072969 + 3 ^ 40 * 5185143 * 2
def baseEnd_5185143 : Nat := 2662470621295911837866467

theorem tailTrace_5185143 : CollatzResearch.WordTrace tailWord_5185143 prefixEnd_5185143 2662470621295911837866467 := by
  unfold tailWord_5185143
  simp only [CollatzResearch.WordTrace]
  refine ⟨189117701854119937767120083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126078467902746625178080055 189117701854119937767120083)
  ·
    refine ⟨283676552781179906650680125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189117701854119937767120083 283676552781179906650680125)
    ·
      refine ⟨106378707292942464994005047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283676552781179906650680125 106378707292942464994005047)
      ·
        refine ⟨159568060939413697491007571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106378707292942464994005047 159568060939413697491007571)
        ·
          refine ⟨239352091409120546236511357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159568060939413697491007571 239352091409120546236511357)
          ·
            refine ⟨89757034278420204838691759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239352091409120546236511357 89757034278420204838691759)
            ·
              refine ⟨134635551417630307258037639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89757034278420204838691759 134635551417630307258037639)
              ·
                refine ⟨201953327126445460887056459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134635551417630307258037639 201953327126445460887056459)
                ·
                  refine ⟨302929990689668191330584689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201953327126445460887056459 302929990689668191330584689)
                  ·
                    refine ⟨227197493017251143497938517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302929990689668191330584689 227197493017251143497938517)
                    ·
                      refine ⟨2662470621295911837866467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 227197493017251143497938517 2662470621295911837866467)
                      ·
                        rfl

theorem cell23_5185143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_5185143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185143 prefixEnd_5185143 := by exact prefixLift 5185143
  have htrace : WordTrace (prefixWord ++ tailWord_5185143) baseStart_5185143 baseEnd_5185143 := by
    simpa [prefixWord, tailWord_5185143, baseEnd_5185143] using wordTrace_append hprefix tailTrace_5185143
  have hstable : (prefixWord ++ tailWord_5185143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185143).length < 2 ^ (prefixWord ++ tailWord_5185143).sum := by decide
  have hdescent : baseEnd_5185143 < baseStart_5185143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185147 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 3, 3, 2]
def baseStart_5185147 : Nat := 118140960795 + 5185147 * 2 ^ 59
def prefixEnd_5185147 : Nat := 4983230072969 + 3 ^ 40 * 5185147 * 2
def baseEnd_5185147 : Nat := 2662472675218529822216449

theorem tailTrace_5185147 : CollatzResearch.WordTrace tailWord_5185147 prefixEnd_5185147 2662472675218529822216449 := by
  unfold tailWord_5185147
  simp only [CollatzResearch.WordTrace]
  refine ⟨189117847746105446450265695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126078565164070297633510463 189117847746105446450265695)
  ·
    refine ⟨283676771619158169675398543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189117847746105446450265695 283676771619158169675398543)
    ·
      refine ⟨425515157428737254513097815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283676771619158169675398543 425515157428737254513097815)
      ·
        refine ⟨638272736143105881769646723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425515157428737254513097815 638272736143105881769646723)
        ·
          refine ⟨957409104214658822654470085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638272736143105881769646723 957409104214658822654470085)
          ·
            refine ⟨179514207040248529247713141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 957409104214658822654470085 179514207040248529247713141)
            ·
              refine ⟨16829456910023299616973107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179514207040248529247713141 16829456910023299616973107)
              ·
                refine ⟨25244185365034949425459661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16829456910023299616973107 25244185365034949425459661)
                ·
                  refine ⟨9466569511888106034547373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25244185365034949425459661 9466569511888106034547373)
                  ·
                    refine ⟨3549963566958039762955265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9466569511888106034547373 3549963566958039762955265)
                    ·
                      refine ⟨2662472675218529822216449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549963566958039762955265 2662472675218529822216449)
                      ·
                        rfl

theorem cell23_5185147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 3, 2].length) (baseStart_5185147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185147 prefixEnd_5185147 := by exact prefixLift 5185147
  have htrace : WordTrace (prefixWord ++ tailWord_5185147) baseStart_5185147 baseEnd_5185147 := by
    simpa [prefixWord, tailWord_5185147, baseEnd_5185147] using wordTrace_append hprefix tailTrace_5185147
  have hstable : (prefixWord ++ tailWord_5185147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185147).length < 2 ^ (prefixWord ++ tailWord_5185147).sum := by decide
  have hdescent : baseEnd_5185147 < baseStart_5185147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185172 : List Nat := [2, 4, 2, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_5185172 : Nat := 118140960795 + 5185172 * 2 ^ 59
def prefixEnd_5185172 : Nat := 4983230072969 + 3 ^ 40 * 5185172 * 2
def baseEnd_5185172 : Nat := 2662485512234892224403835

theorem tailTrace_5185172 : CollatzResearch.WordTrace tailWord_5185172 prefixEnd_5185172 2662485512234892224403835 := by
  unfold tailWord_5185172
  simp only [CollatzResearch.WordTrace]
  refine ⟨94559379785507437859962885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126079173047343250479950513 94559379785507437859962885)
  ·
    refine ⟨17729883709782644598743041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94559379785507437859962885 17729883709782644598743041)
    ·
      refine ⟨13297412782336983449057281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17729883709782644598743041 13297412782336983449057281)
      ·
        refine ⟨9973059586752737586792961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13297412782336983449057281 9973059586752737586792961)
        ·
          refine ⟨7479794690064553190094721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9973059586752737586792961 7479794690064553190094721)
          ·
            refine ⟨5609846017548414892571041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7479794690064553190094721 5609846017548414892571041)
            ·
              refine ⟨4207384513161311169428281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5609846017548414892571041 4207384513161311169428281)
              ·
                refine ⟨3155538384870983377071211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4207384513161311169428281 3155538384870983377071211)
                ·
                  refine ⟨4733307577306475065606817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155538384870983377071211 4733307577306475065606817)
                  ·
                    refine ⟨3549980682979856299205113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4733307577306475065606817 3549980682979856299205113)
                    ·
                      refine ⟨2662485512234892224403835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3549980682979856299205113 2662485512234892224403835)
                      ·
                        rfl

theorem cell23_5185172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_5185172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185172 prefixEnd_5185172 := by exact prefixLift 5185172
  have htrace : WordTrace (prefixWord ++ tailWord_5185172) baseStart_5185172 baseEnd_5185172 := by
    simpa [prefixWord, tailWord_5185172, baseEnd_5185172] using wordTrace_append hprefix tailTrace_5185172
  have hstable : (prefixWord ++ tailWord_5185172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185172).length < 2 ^ (prefixWord ++ tailWord_5185172).sum := by decide
  have hdescent : baseEnd_5185172 < baseStart_5185172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185197 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_5185197 : Nat := 118140960795 + 5185197 * 2 ^ 59
def prefixEnd_5185197 : Nat := 4983230072969 + 3 ^ 40 * 5185197 * 2
def baseEnd_5185197 : Nat := 2662498349251254626591219

theorem tailTrace_5185197 : CollatzResearch.WordTrace tailWord_5185197 prefixEnd_5185197 2662498349251254626591219 := by
  unfold tailWord_5185197
  simp only [CollatzResearch.WordTrace]
  refine ⟨189119671395924304989585845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126079780930616203326390563 189119671395924304989585845)
  ·
    refine ⟨17729969193367903592773673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189119671395924304989585845 17729969193367903592773673)
    ·
      refine ⟨13297476895025927694580255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17729969193367903592773673 13297476895025927694580255)
      ·
        refine ⟨19946215342538891541870383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13297476895025927694580255 19946215342538891541870383)
        ·
          refine ⟨29919323013808337312805575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19946215342538891541870383 29919323013808337312805575)
          ·
            refine ⟨44878984520712505969208363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29919323013808337312805575 44878984520712505969208363)
            ·
              refine ⟨67318476781068758953812545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44878984520712505969208363 67318476781068758953812545)
              ·
                refine ⟨50488857585801569215359409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67318476781068758953812545 50488857585801569215359409)
                ·
                  refine ⟨37866643189351176911519557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50488857585801569215359409 37866643189351176911519557)
                  ·
                    refine ⟨7099995598003345670909917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37866643189351176911519557 7099995598003345670909917)
                    ·
                      refine ⟨2662498349251254626591219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7099995598003345670909917 2662498349251254626591219)
                      ·
                        rfl

theorem cell23_5185197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_5185197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185197 prefixEnd_5185197 := by exact prefixLift 5185197
  have htrace : WordTrace (prefixWord ++ tailWord_5185197) baseStart_5185197 baseEnd_5185197 := by
    simpa [prefixWord, tailWord_5185197, baseEnd_5185197] using wordTrace_append hprefix tailTrace_5185197
  have hstable : (prefixWord ++ tailWord_5185197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185197).length < 2 ^ (prefixWord ++ tailWord_5185197).sum := by decide
  have hdescent : baseEnd_5185197 < baseStart_5185197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185234 : List Nat := [3, 2, 2, 2, 2, 1, 2, 4, 5]
def baseStart_5185234 : Nat := 118140960795 + 5185234 * 2 ^ 59
def prefixEnd_5185234 : Nat := 4983230072969 + 3 ^ 40 * 5185234 * 2
def baseEnd_5185234 : Nat := 295835260892830109092061

theorem tailTrace_5185234 : CollatzResearch.WordTrace tailWord_5185234 prefixEnd_5185234 295835260892830109092061 := by
  unfold tailWord_5185234
  simp only [CollatzResearch.WordTrace]
  refine ⟨47280255224197565077170689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126080680597860173539121837 47280255224197565077170689)
  ·
    refine ⟨35460191418148173807878017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47280255224197565077170689 35460191418148173807878017)
    ·
      refine ⟨26595143563611130355908513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35460191418148173807878017 26595143563611130355908513)
      ·
        refine ⟨19946357672708347766931385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26595143563611130355908513 19946357672708347766931385)
        ·
          refine ⟨14959768254531260825198539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19946357672708347766931385 14959768254531260825198539)
          ·
            refine ⟨22439652381796891237797809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14959768254531260825198539 22439652381796891237797809)
            ·
              refine ⟨16829739286347668428348357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22439652381796891237797809 16829739286347668428348357)
              ·
                refine ⟨3155576116190187830315317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16829739286347668428348357 3155576116190187830315317)
                ·
                  refine ⟨295835260892830109092061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3155576116190187830315317 295835260892830109092061)
                  ·
                    rfl

theorem cell23_5185234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_5185234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185234 prefixEnd_5185234 := by exact prefixLift 5185234
  have htrace : WordTrace (prefixWord ++ tailWord_5185234) baseStart_5185234 baseEnd_5185234 := by
    simpa [prefixWord, tailWord_5185234, baseEnd_5185234] using wordTrace_append hprefix tailTrace_5185234
  have hstable : (prefixWord ++ tailWord_5185234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185234).length < 2 ^ (prefixWord ++ tailWord_5185234).sum := by decide
  have hdescent : baseEnd_5185234 < baseStart_5185234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185240 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_5185240 : Nat := 118140960795 + 5185240 * 2 ^ 59
def prefixEnd_5185240 : Nat := 4983230072969 + 3 ^ 40 * 5185240 * 2
def baseEnd_5185240 : Nat := 2662520428919397958353521

theorem tailTrace_5185240 : CollatzResearch.WordTrace tailWord_5185240 prefixEnd_5185240 2662520428919397958353521 := by
  unfold tailWord_5185240
  simp only [CollatzResearch.WordTrace]
  refine ⟨94560619867384261666700587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126080826489845682222267449 94560619867384261666700587)
  ·
    refine ⟨141840929801076392500050881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94560619867384261666700587 141840929801076392500050881)
    ·
      refine ⟨106380697350807294375038161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141840929801076392500050881 106380697350807294375038161)
      ·
        refine ⟨79785523013105470781278621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106380697350807294375038161 79785523013105470781278621)
        ·
          refine ⟨29919571129914551542979483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79785523013105470781278621 29919571129914551542979483)
          ·
            refine ⟨44879356694871827314469225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29919571129914551542979483 44879356694871827314469225)
            ·
              refine ⟨33659517521153870485851919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44879356694871827314469225 33659517521153870485851919)
              ·
                refine ⟨50489276281730805728777879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33659517521153870485851919 50489276281730805728777879)
                ·
                  refine ⟨75733914422596208593166819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50489276281730805728777879 75733914422596208593166819)
                  ·
                    refine ⟨113600871633894312889750229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75733914422596208593166819 113600871633894312889750229)
                    ·
                      refine ⟨2662520428919397958353521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113600871633894312889750229 2662520428919397958353521)
                      ·
                        rfl

theorem cell23_5185240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_5185240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185240 prefixEnd_5185240 := by exact prefixLift 5185240
  have htrace : WordTrace (prefixWord ++ tailWord_5185240) baseStart_5185240 baseEnd_5185240 := by
    simpa [prefixWord, tailWord_5185240, baseEnd_5185240] using wordTrace_append hprefix tailTrace_5185240
  have hstable : (prefixWord ++ tailWord_5185240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185240).length < 2 ^ (prefixWord ++ tailWord_5185240).sum := by decide
  have hdescent : baseEnd_5185240 < baseStart_5185240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185245 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5185245 : Nat := 118140960795 + 5185245 * 2 ^ 59
def prefixEnd_5185245 : Nat := 4983230072969 + 3 ^ 40 * 5185245 * 2
def baseEnd_5185245 : Nat := 2662522996322670438790999

theorem tailTrace_5185245 : CollatzResearch.WordTrace tailWord_5185245 prefixEnd_5185245 2662522996322670438790999 := by
  unfold tailWord_5185245
  simp only [CollatzResearch.WordTrace]
  refine ⟨189121422099750409187333189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126080948066500272791555459 189121422099750409187333189)
  ·
    refine ⟨35460266643703201722624973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189121422099750409187333189 35460266643703201722624973)
    ·
      refine ⟨13297599991388700645984365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35460266643703201722624973 13297599991388700645984365)
      ·
        refine ⟨4986599996770762742244137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13297599991388700645984365 4986599996770762742244137)
        ·
          refine ⟨3739949997578072056683103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4986599996770762742244137 3739949997578072056683103)
          ·
            refine ⟨5609924996367108085024655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739949997578072056683103 5609924996367108085024655)
            ·
              refine ⟨8414887494550662127536983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5609924996367108085024655 8414887494550662127536983)
              ·
                refine ⟨12622331241825993191305475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8414887494550662127536983 12622331241825993191305475)
                ·
                  refine ⟨18933496862738989786958213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12622331241825993191305475 18933496862738989786958213)
                  ·
                    refine ⟨3550030661763560585054665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18933496862738989786958213 3550030661763560585054665)
                    ·
                      refine ⟨2662522996322670438790999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550030661763560585054665 2662522996322670438790999)
                      ·
                        rfl

theorem cell23_5185245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5185245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185245 prefixEnd_5185245 := by exact prefixLift 5185245
  have htrace : WordTrace (prefixWord ++ tailWord_5185245) baseStart_5185245 baseEnd_5185245 := by
    simpa [prefixWord, tailWord_5185245, baseEnd_5185245] using wordTrace_append hprefix tailTrace_5185245
  have hstable : (prefixWord ++ tailWord_5185245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185245).length < 2 ^ (prefixWord ++ tailWord_5185245).sum := by decide
  have hdescent : baseEnd_5185245 < baseStart_5185245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185267 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 1, 6, 2]
def baseStart_5185267 : Nat := 118140960795 + 5185267 * 2 ^ 59
def prefixEnd_5185267 : Nat := 4983230072969 + 3 ^ 40 * 5185267 * 2
def baseEnd_5185267 : Nat := 2662534292897069352715897

theorem tailTrace_5185267 : CollatzResearch.WordTrace tailWord_5185267 prefixEnd_5185267 2662534292897069352715897 := by
  unfold tailWord_5185267
  simp only [CollatzResearch.WordTrace]
  refine ⟨189122224505670706944634055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126081483003780471296422703 189122224505670706944634055)
  ·
    refine ⟨283683336758506060416951083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189122224505670706944634055 283683336758506060416951083)
    ·
      refine ⟨425525005137759090625426625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283683336758506060416951083 425525005137759090625426625)
      ·
        refine ⟨319143753853319317969069969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425525005137759090625426625 319143753853319317969069969)
        ·
          refine ⟨239357815389989488476802477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319143753853319317969069969 239357815389989488476802477)
          ·
            refine ⟨89759180771246058178800929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239357815389989488476802477 89759180771246058178800929)
            ·
              refine ⟨67319385578434543634100697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89759180771246058178800929 67319385578434543634100697)
              ·
                refine ⟨50489539183825907725575523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67319385578434543634100697 50489539183825907725575523)
                ·
                  refine ⟨75734308775738861588363285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50489539183825907725575523 75734308775738861588363285)
                  ·
                    refine ⟨3550045723862759136954529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75734308775738861588363285 3550045723862759136954529)
                    ·
                      refine ⟨2662534292897069352715897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550045723862759136954529 2662534292897069352715897)
                      ·
                        rfl

theorem cell23_5185267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 6, 2].length) (baseStart_5185267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185267 prefixEnd_5185267 := by exact prefixLift 5185267
  have htrace : WordTrace (prefixWord ++ tailWord_5185267) baseStart_5185267 baseEnd_5185267 := by
    simpa [prefixWord, tailWord_5185267, baseEnd_5185267] using wordTrace_append hprefix tailTrace_5185267
  have hstable : (prefixWord ++ tailWord_5185267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185267).length < 2 ^ (prefixWord ++ tailWord_5185267).sum := by decide
  have hdescent : baseEnd_5185267 < baseStart_5185267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185268 : List Nat := [2, 6, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5185268 : Nat := 118140960795 + 5185268 * 2 ^ 59
def prefixEnd_5185268 : Nat := 4983230072969 + 3 ^ 40 * 5185268 * 2
def baseEnd_5185268 : Nat := 295837200708635983200377

theorem tailTrace_5185268 : CollatzResearch.WordTrace tailWord_5185268 prefixEnd_5185268 295837200708635983200377 := by
  unfold tailWord_5185268
  simp only [CollatzResearch.WordTrace]
  refine ⟨94561130489333542057710229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126081507319111389410280305 94561130489333542057710229)
  ·
    refine ⟨4432552991687509783955167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 94561130489333542057710229 4432552991687509783955167)
    ·
      refine ⟨6648829487531264675932751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4432552991687509783955167 6648829487531264675932751)
      ·
        refine ⟨9973244231296897013899127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6648829487531264675932751 9973244231296897013899127)
        ·
          refine ⟨14959866346945345520848691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9973244231296897013899127 14959866346945345520848691)
          ·
            refine ⟨22439799520418018281273037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14959866346945345520848691 22439799520418018281273037)
            ·
              refine ⟨8414924820156756855477389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22439799520418018281273037 8414924820156756855477389)
              ·
                refine ⟨3155596807558783820804021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8414924820156756855477389 3155596807558783820804021)
                ·
                  refine ⟨295837200708635983200377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3155596807558783820804021 295837200708635983200377)
                  ·
                    rfl

theorem cell23_5185268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5185268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185268 prefixEnd_5185268 := by exact prefixLift 5185268
  have htrace : WordTrace (prefixWord ++ tailWord_5185268) baseStart_5185268 baseEnd_5185268 := by
    simpa [prefixWord, tailWord_5185268, baseEnd_5185268] using wordTrace_append hprefix tailTrace_5185268
  have hstable : (prefixWord ++ tailWord_5185268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185268).length < 2 ^ (prefixWord ++ tailWord_5185268).sum := by decide
  have hdescent : baseEnd_5185268 < baseStart_5185268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185280 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_5185280 : Nat := 118140960795 + 5185280 * 2 ^ 59
def prefixEnd_5185280 : Nat := 4983230072969 + 3 ^ 40 * 5185280 * 2
def baseEnd_5185280 : Nat := 2662540968145577801853337

theorem tailTrace_5185280 : CollatzResearch.WordTrace tailWord_5185280 prefixEnd_5185280 2662540968145577801853337 := by
  unfold tailWord_5185280
  simp only [CollatzResearch.WordTrace]
  refine ⟨94561349327311805082428647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126081799103082406776571529 94561349327311805082428647)
  ·
    refine ⟨141842023990967707623642971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94561349327311805082428647 141842023990967707623642971)
    ·
      refine ⟨212763035986451561435464457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141842023990967707623642971 212763035986451561435464457)
      ·
        refine ⟨159572276989838671076598343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212763035986451561435464457 159572276989838671076598343)
        ·
          refine ⟨239358415484758006614897515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159572276989838671076598343 239358415484758006614897515)
          ·
            refine ⟨359037623227137009922346273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239358415484758006614897515 359037623227137009922346273)
            ·
              refine ⟨269278217420352757441759705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359037623227137009922346273 269278217420352757441759705)
              ·
                refine ⟨201958663065264568081319779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269278217420352757441759705 201958663065264568081319779)
                ·
                  refine ⟨302937994597896852121979669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201958663065264568081319779 302937994597896852121979669)
                  ·
                    refine ⟨14200218496776414943217797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 302937994597896852121979669 14200218496776414943217797)
                    ·
                      refine ⟨2662540968145577801853337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14200218496776414943217797 2662540968145577801853337)
                      ·
                        rfl

theorem cell23_5185280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_5185280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185280 prefixEnd_5185280 := by exact prefixLift 5185280
  have htrace : WordTrace (prefixWord ++ tailWord_5185280) baseStart_5185280 baseEnd_5185280 := by
    simpa [prefixWord, tailWord_5185280, baseEnd_5185280] using wordTrace_append hprefix tailTrace_5185280
  have hstable : (prefixWord ++ tailWord_5185280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185280).length < 2 ^ (prefixWord ++ tailWord_5185280).sum := by decide
  have hdescent : baseEnd_5185280 < baseStart_5185280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185284 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_5185284 : Nat := 118140960795 + 5185284 * 2 ^ 59
def prefixEnd_5185284 : Nat := 4983230072969 + 3 ^ 40 * 5185284 * 2
def baseEnd_5185284 : Nat := 2662543022068195786203319

theorem tailTrace_5185284 : CollatzResearch.WordTrace tailWord_5185284 prefixEnd_5185284 2662543022068195786203319 := by
  unfold tailWord_5185284
  simp only [CollatzResearch.WordTrace]
  refine ⟨94561422273304559424001453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126081896364406079232001937 94561422273304559424001453)
  ·
    refine ⟨35460533352489209784000545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94561422273304559424001453 35460533352489209784000545)
    ·
      refine ⟨26595400014366907338000409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35460533352489209784000545 26595400014366907338000409)
      ·
        refine ⟨19946550010775180503500307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26595400014366907338000409 19946550010775180503500307)
        ·
          refine ⟨29919825016162770755250461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19946550010775180503500307 29919825016162770755250461)
          ·
            refine ⟨11219934381061039033218923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29919825016162770755250461 11219934381061039033218923)
            ·
              refine ⟨16829901571591558549828385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11219934381061039033218923 16829901571591558549828385)
              ·
                refine ⟨12622426178693668912371289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16829901571591558549828385 12622426178693668912371289)
                ·
                  refine ⟨9466819634020251684278467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12622426178693668912371289 9466819634020251684278467)
                  ·
                    refine ⟨14200229451030377526417701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9466819634020251684278467 14200229451030377526417701)
                    ·
                      refine ⟨2662543022068195786203319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14200229451030377526417701 2662543022068195786203319)
                      ·
                        rfl

theorem cell23_5185284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_5185284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185284 prefixEnd_5185284 := by exact prefixLift 5185284
  have htrace : WordTrace (prefixWord ++ tailWord_5185284) baseStart_5185284 baseEnd_5185284 := by
    simpa [prefixWord, tailWord_5185284, baseEnd_5185284] using wordTrace_append hprefix tailTrace_5185284
  have hstable : (prefixWord ++ tailWord_5185284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185284).length < 2 ^ (prefixWord ++ tailWord_5185284).sum := by decide
  have hdescent : baseEnd_5185284 < baseStart_5185284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185294 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_5185294 : Nat := 118140960795 + 5185294 * 2 ^ 59
def prefixEnd_5185294 : Nat := 4983230072969 + 3 ^ 40 * 5185294 * 2
def baseEnd_5185294 : Nat := 887516052291580249026091

theorem tailTrace_5185294 : CollatzResearch.WordTrace tailWord_5185294 prefixEnd_5185294 887516052291580249026091 := by
  unfold tailWord_5185294
  simp only [CollatzResearch.WordTrace]
  refine ⟨23640401159571611319483367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126082139517715260370577957 23640401159571611319483367)
  ·
    refine ⟨35460601739357416979225051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23640401159571611319483367 35460601739357416979225051)
    ·
      refine ⟨53190902609036125468837577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35460601739357416979225051 53190902609036125468837577)
      ·
        refine ⟨39893176956777094101628183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53190902609036125468837577 39893176956777094101628183)
        ·
          refine ⟨59839765435165641152442275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39893176956777094101628183 59839765435165641152442275)
          ·
            refine ⟨89759648152748461728663413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59839765435165641152442275 89759648152748461728663413)
            ·
              refine ⟨8414967014320168287062195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89759648152748461728663413 8414967014320168287062195)
              ·
                refine ⟨12622450521480252430593293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8414967014320168287062195 12622450521480252430593293)
                ·
                  refine ⟨4733418945555094661472485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12622450521480252430593293 4733418945555094661472485)
                  ·
                    refine ⟨887516052291580249026091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4733418945555094661472485 887516052291580249026091)
                    ·
                      rfl

theorem cell23_5185294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_5185294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185294 prefixEnd_5185294 := by exact prefixLift 5185294
  have htrace : WordTrace (prefixWord ++ tailWord_5185294) baseStart_5185294 baseEnd_5185294 := by
    simpa [prefixWord, tailWord_5185294, baseEnd_5185294] using wordTrace_append hprefix tailTrace_5185294
  have hstable : (prefixWord ++ tailWord_5185294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185294).length < 2 ^ (prefixWord ++ tailWord_5185294).sum := by decide
  have hdescent : baseEnd_5185294 < baseStart_5185294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185378 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_5185378 : Nat := 118140960795 + 5185378 * 2 ^ 59
def prefixEnd_5185378 : Nat := 4983230072969 + 3 ^ 40 * 5185378 * 2
def baseEnd_5185378 : Nat := 2662591289249718418427887

theorem tailTrace_5185378 : CollatzResearch.WordTrace tailWord_5185378 prefixEnd_5185378 2662591289249718418427887 := by
  unfold tailWord_5185378
  simp only [CollatzResearch.WordTrace]
  refine ⟨47281568252067143225481197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126084182005512381934616525 47281568252067143225481197)
  ·
    refine ⟨17730588094525178709555449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47281568252067143225481197 17730588094525178709555449)
    ·
      refine ⟨13297941070893884032166587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17730588094525178709555449 13297941070893884032166587)
      ·
        refine ⟨19946911606340826048249881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13297941070893884032166587 19946911606340826048249881)
        ·
          refine ⟨14960183704755619536187411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19946911606340826048249881 14960183704755619536187411)
          ·
            refine ⟨22440275557133429304281117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14960183704755619536187411 22440275557133429304281117)
            ·
              refine ⟨8415103333925035989105419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22440275557133429304281117 8415103333925035989105419)
              ·
                refine ⟨12622655000887553983658129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8415103333925035989105419 12622655000887553983658129)
                ·
                  refine ⟨9466991250665665487743597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12622655000887553983658129 9466991250665665487743597)
                  ·
                    refine ⟨3550121718999624557903849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9466991250665665487743597 3550121718999624557903849)
                    ·
                      refine ⟨2662591289249718418427887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550121718999624557903849 2662591289249718418427887)
                      ·
                        rfl

theorem cell23_5185378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_5185378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185378 prefixEnd_5185378 := by exact prefixLift 5185378
  have htrace : WordTrace (prefixWord ++ tailWord_5185378) baseStart_5185378 baseEnd_5185378 := by
    simpa [prefixWord, tailWord_5185378, baseEnd_5185378] using wordTrace_append hprefix tailTrace_5185378
  have hstable : (prefixWord ++ tailWord_5185378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185378).length < 2 ^ (prefixWord ++ tailWord_5185378).sum := by decide
  have hdescent : baseEnd_5185378 < baseStart_5185378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185384 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 4, 4]
def baseStart_5185384 : Nat := 118140960795 + 5185384 * 2 ^ 59
def prefixEnd_5185384 : Nat := 4983230072969 + 3 ^ 40 * 5185384 * 2
def baseEnd_5185384 : Nat := 887531456711215131650953

theorem tailTrace_5185384 : CollatzResearch.WordTrace tailWord_5185384 prefixEnd_5185384 887531456711215131650953 := by
  unfold tailWord_5185384
  simp only [CollatzResearch.WordTrace]
  refine ⟨94563245923123417963321603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126084327897497890617762137 94563245923123417963321603)
  ·
    refine ⟨141844868884685126944982405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94563245923123417963321603 141844868884685126944982405)
    ·
      refine ⟨26595912915878461302184201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141844868884685126944982405 26595912915878461302184201)
      ·
        refine ⟨19946934686908845976638151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26595912915878461302184201 19946934686908845976638151)
        ·
          refine ⟨29920402030363268964957227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19946934686908845976638151 29920402030363268964957227)
          ·
            refine ⟨44880603045544903447435841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29920402030363268964957227 44880603045544903447435841)
            ·
              refine ⟨33660452284158677585576881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44880603045544903447435841 33660452284158677585576881)
              ·
                refine ⟨25245339213119008189182661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33660452284158677585576881 25245339213119008189182661)
                ·
                  refine ⟨4733501102459814035471749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25245339213119008189182661 4733501102459814035471749)
                  ·
                    refine ⟨887531456711215131650953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4733501102459814035471749 887531456711215131650953)
                    ·
                      rfl

theorem cell23_5185384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_5185384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185384 prefixEnd_5185384 := by exact prefixLift 5185384
  have htrace : WordTrace (prefixWord ++ tailWord_5185384) baseStart_5185384 baseEnd_5185384 := by
    simpa [prefixWord, tailWord_5185384, baseEnd_5185384] using wordTrace_append hprefix tailTrace_5185384
  have hstable : (prefixWord ++ tailWord_5185384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185384).length < 2 ^ (prefixWord ++ tailWord_5185384).sum := by decide
  have hdescent : baseEnd_5185384 < baseStart_5185384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185397 : List Nat := [1, 3, 4, 1, 1, 1, 12]
def baseStart_5185397 : Nat := 118140960795 + 5185397 * 2 ^ 59
def prefixEnd_5185397 : Nat := 4983230072969 + 3 ^ 40 * 5185397 * 2
def baseEnd_5185397 : Nat := 32871617844224121531979

theorem tailTrace_5185397 : CollatzResearch.WordTrace tailWord_5185397 prefixEnd_5185397 32871617844224121531979 := by
  unfold tailWord_5185397
  simp only [CollatzResearch.WordTrace]
  refine ⟨189126965995199739146866445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126084643996799826097910963 189126965995199739146866445)
  ·
    refine ⟨70922612248199902180074917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189126965995199739146866445 70922612248199902180074917)
    ·
      refine ⟨13297989796537481658764047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70922612248199902180074917 13297989796537481658764047)
      ·
        refine ⟨19946984694806222488146071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13297989796537481658764047 19946984694806222488146071)
        ·
          refine ⟨29920477042209333732219107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19946984694806222488146071 29920477042209333732219107)
          ·
            refine ⟨44880715563314000598328661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29920477042209333732219107 44880715563314000598328661)
            ·
              refine ⟨32871617844224121531979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44880715563314000598328661 32871617844224121531979)
              ·
                rfl

theorem cell23_5185397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 12].length) (baseStart_5185397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185397 prefixEnd_5185397 := by exact prefixLift 5185397
  have htrace : WordTrace (prefixWord ++ tailWord_5185397) baseStart_5185397 baseEnd_5185397 := by
    simpa [prefixWord, tailWord_5185397, baseEnd_5185397] using wordTrace_append hprefix tailTrace_5185397
  have hstable : (prefixWord ++ tailWord_5185397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185397).length < 2 ^ (prefixWord ++ tailWord_5185397).sum := by decide
  have hdescent : baseEnd_5185397 < baseStart_5185397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185408 : List Nat := [2, 1, 1, 2, 1, 2, 3, 6, 1, 2, 2]
def baseStart_5185408 : Nat := 118140960795 + 5185408 * 2 ^ 59
def prefixEnd_5185408 : Nat := 4983230072969 + 3 ^ 40 * 5185408 * 2
def baseEnd_5185408 : Nat := 2662606693669353301052749

theorem tailTrace_5185408 : CollatzResearch.WordTrace tailWord_5185408 prefixEnd_5185408 2662606693669353301052749 := by
  unfold tailWord_5185408
  simp only [CollatzResearch.WordTrace]
  refine ⟨94563683599079944012758439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126084911465439925350344585 94563683599079944012758439)
  ·
    refine ⟨141845525398619916019137659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94563683599079944012758439 141845525398619916019137659)
    ·
      refine ⟨212768288097929874028706489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141845525398619916019137659 212768288097929874028706489)
      ·
        refine ⟨159576216073447405521529867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212768288097929874028706489 159576216073447405521529867)
        ·
          refine ⟨239364324110171108282294801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159576216073447405521529867 239364324110171108282294801)
          ·
            refine ⟨179523243082628331211721101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239364324110171108282294801 179523243082628331211721101)
            ·
              refine ⟨67321216155985624204395413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179523243082628331211721101 67321216155985624204395413)
              ·
                refine ⟨3155682007311826134581035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67321216155985624204395413 3155682007311826134581035)
                ·
                  refine ⟨4733523010967739201871553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3155682007311826134581035 4733523010967739201871553)
                  ·
                    refine ⟨3550142258225804401403665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4733523010967739201871553 3550142258225804401403665)
                    ·
                      refine ⟨2662606693669353301052749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550142258225804401403665 2662606693669353301052749)
                      ·
                        rfl

theorem cell23_5185408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_5185408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185408 prefixEnd_5185408 := by exact prefixLift 5185408
  have htrace : WordTrace (prefixWord ++ tailWord_5185408) baseStart_5185408 baseEnd_5185408 := by
    simpa [prefixWord, tailWord_5185408, baseEnd_5185408] using wordTrace_append hprefix tailTrace_5185408
  have hstable : (prefixWord ++ tailWord_5185408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185408).length < 2 ^ (prefixWord ++ tailWord_5185408).sum := by decide
  have hdescent : baseEnd_5185408 < baseStart_5185408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185418 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_5185418 : Nat := 118140960795 + 5185418 * 2 ^ 59
def prefixEnd_5185418 : Nat := 4983230072969 + 3 ^ 40 * 5185418 * 2
def baseEnd_5185418 : Nat := 887537276158632753975901

theorem tailTrace_5185418 : CollatzResearch.WordTrace tailWord_5185418 prefixEnd_5185418 887537276158632753975901 := by
  unfold tailWord_5185418
  simp only [CollatzResearch.WordTrace]
  refine ⟨47281932982030914933345227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126085154618749106488920605 47281932982030914933345227)
  ·
    refine ⟨70922899473046372400017841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47281932982030914933345227 70922899473046372400017841)
    ·
      refine ⟨53192174604784779300013381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70922899473046372400017841 53192174604784779300013381)
      ·
        refine ⟨9973532738397146118752509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53192174604784779300013381 9973532738397146118752509)
        ·
          refine ⟨3740074776898929794532191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9973532738397146118752509 3740074776898929794532191)
          ·
            refine ⟨5610112165348394691798287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740074776898929794532191 5610112165348394691798287)
            ·
              refine ⟨8415168248022592037697431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610112165348394691798287 8415168248022592037697431)
              ·
                refine ⟨12622752372033888056546147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8415168248022592037697431 12622752372033888056546147)
                ·
                  refine ⟨18934128558050832084819221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12622752372033888056546147 18934128558050832084819221)
                  ·
                    refine ⟨887537276158632753975901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18934128558050832084819221 887537276158632753975901)
                    ·
                      rfl

theorem cell23_5185418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_5185418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185418 prefixEnd_5185418 := by exact prefixLift 5185418
  have htrace : WordTrace (prefixWord ++ tailWord_5185418) baseStart_5185418 baseEnd_5185418 := by
    simpa [prefixWord, tailWord_5185418, baseEnd_5185418] using wordTrace_append hprefix tailTrace_5185418
  have hstable : (prefixWord ++ tailWord_5185418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185418).length < 2 ^ (prefixWord ++ tailWord_5185418).sum := by decide
  have hdescent : baseEnd_5185418 < baseStart_5185418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185424 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 6, 1, 3]
def baseStart_5185424 : Nat := 118140960795 + 5185424 * 2 ^ 59
def prefixEnd_5185424 : Nat := 4983230072969 + 3 ^ 40 * 5185424 * 2
def baseEnd_5185424 : Nat := 2662614909359825238452675

theorem tailTrace_5185424 : CollatzResearch.WordTrace tailWord_5185424 prefixEnd_5185424 2662614909359825238452675 := by
  unfold tailWord_5185424
  simp only [CollatzResearch.WordTrace]
  refine ⟨94563975383050961379049663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126085300510734615172066217 94563975383050961379049663)
  ·
    refine ⟨141845963074576442068574495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94563975383050961379049663 141845963074576442068574495)
    ·
      refine ⟨212768944611864663102861743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141845963074576442068574495 212768944611864663102861743)
      ·
        refine ⟨319153416917796994654292615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212768944611864663102861743 319153416917796994654292615)
        ·
          refine ⟨478730125376695491981438923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319153416917796994654292615 478730125376695491981438923)
          ·
            refine ⟨718095188065043237972158385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478730125376695491981438923 718095188065043237972158385)
            ·
              refine ⟨538571391048782428479118789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718095188065043237972158385 538571391048782428479118789)
              ·
                refine ⟨100982135821646705339834773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538571391048782428479118789 100982135821646705339834773)
                ·
                  refine ⟨4733537616639689312804755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100982135821646705339834773 4733537616639689312804755)
                  ·
                    refine ⟨7100306424959533969207133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4733537616639689312804755 7100306424959533969207133)
                    ·
                      refine ⟨2662614909359825238452675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7100306424959533969207133 2662614909359825238452675)
                      ·
                        rfl

theorem cell23_5185424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 1, 3].length) (baseStart_5185424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185424 prefixEnd_5185424 := by exact prefixLift 5185424
  have htrace : WordTrace (prefixWord ++ tailWord_5185424) baseStart_5185424 baseEnd_5185424 := by
    simpa [prefixWord, tailWord_5185424, baseEnd_5185424] using wordTrace_append hprefix tailTrace_5185424
  have hstable : (prefixWord ++ tailWord_5185424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185424).length < 2 ^ (prefixWord ++ tailWord_5185424).sum := by decide
  have hdescent : baseEnd_5185424 < baseStart_5185424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185428 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_5185428 : Nat := 118140960795 + 5185428 * 2 ^ 59
def prefixEnd_5185428 : Nat := 4983230072969 + 3 ^ 40 * 5185428 * 2
def baseEnd_5185428 : Nat := 2662616963282443222802657

theorem tailTrace_5185428 : CollatzResearch.WordTrace tailWord_5185428 prefixEnd_5185428 2662616963282443222802657 := by
  unfold tailWord_5185428
  simp only [CollatzResearch.WordTrace]
  refine ⟨94564048329043715720622469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126085397772058287627496625 94564048329043715720622469)
  ·
    refine ⟨17730759061695696697616713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94564048329043715720622469 17730759061695696697616713)
    ·
      refine ⟨13298069296271772523212535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17730759061695696697616713 13298069296271772523212535)
      ·
        refine ⟨19947103944407658784818803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13298069296271772523212535 19947103944407658784818803)
        ·
          refine ⟨29920655916611488177228205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19947103944407658784818803 29920655916611488177228205)
          ·
            refine ⟨11220245968729308066460577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29920655916611488177228205 11220245968729308066460577)
            ·
              refine ⟨8415184476546981049845433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11220245968729308066460577 8415184476546981049845433)
              ·
                refine ⟨6311388357410235787384075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8415184476546981049845433 6311388357410235787384075)
                ·
                  refine ⟨9467082536115353681076113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6311388357410235787384075 9467082536115353681076113)
                  ·
                    refine ⟨7100311902086515260807085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9467082536115353681076113 7100311902086515260807085)
                    ·
                      refine ⟨2662616963282443222802657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7100311902086515260807085 2662616963282443222802657)
                      ·
                        rfl

theorem cell23_5185428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_5185428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185428 prefixEnd_5185428 := by exact prefixLift 5185428
  have htrace : WordTrace (prefixWord ++ tailWord_5185428) baseStart_5185428 baseEnd_5185428 := by
    simpa [prefixWord, tailWord_5185428, baseEnd_5185428] using wordTrace_append hprefix tailTrace_5185428
  have hstable : (prefixWord ++ tailWord_5185428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185428).length < 2 ^ (prefixWord ++ tailWord_5185428).sum := by decide
  have hdescent : baseEnd_5185428 < baseStart_5185428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185448 : List Nat := [2, 1, 6, 2, 2, 1, 9]
def baseStart_5185448 : Nat := 118140960795 + 5185448 * 2 ^ 59
def prefixEnd_5185448 : Nat := 4983230072969 + 3 ^ 40 * 5185448 * 2
def baseEnd_5185448 : Nat := 32871941146858433883365

theorem tailTrace_5185448 : CollatzResearch.WordTrace tailWord_5185448 prefixEnd_5185448 32871941146858433883365 := by
  unfold tailWord_5185448
  simp only [CollatzResearch.WordTrace]
  refine ⟨94564413059007487428486499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126085884078676649904648665 94564413059007487428486499)
  ·
    refine ⟨141846619588511231142729749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94564413059007487428486499 141846619588511231142729749)
    ·
      refine ⟨6649060293211463959815457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 141846619588511231142729749 6649060293211463959815457)
      ·
        refine ⟨4986795219908597969861593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6649060293211463959815457 4986795219908597969861593)
        ·
          refine ⟨3740096414931448477396195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4986795219908597969861593 3740096414931448477396195)
          ·
            refine ⟨5610144622397172716094293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740096414931448477396195 5610144622397172716094293)
            ·
              refine ⟨32871941146858433883365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5610144622397172716094293 32871941146858433883365)
              ·
                rfl

theorem cell23_5185448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 9].length) (baseStart_5185448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185448 prefixEnd_5185448 := by exact prefixLift 5185448
  have htrace : WordTrace (prefixWord ++ tailWord_5185448) baseStart_5185448 baseEnd_5185448 := by
    simpa [prefixWord, tailWord_5185448, baseEnd_5185448] using wordTrace_append hprefix tailTrace_5185448
  have hstable : (prefixWord ++ tailWord_5185448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185448).length < 2 ^ (prefixWord ++ tailWord_5185448).sum := by decide
  have hdescent : baseEnd_5185448 < baseStart_5185448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185467 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 5]
def baseStart_5185467 : Nat := 118140960795 + 5185467 * 2 ^ 59
def prefixEnd_5185467 : Nat := 4983230072969 + 3 ^ 40 * 5185467 * 2
def baseEnd_5185467 : Nat := 2662636989027968570214977

theorem tailTrace_5185467 : CollatzResearch.WordTrace tailWord_5185467 prefixEnd_5185467 2662636989027968570214977 := by
  unfold tailWord_5185467
  simp only [CollatzResearch.WordTrace]
  refine ⟨189129519104946141101914655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126086346069964094067943103 189129519104946141101914655)
  ·
    refine ⟨283694278657419211652871983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189129519104946141101914655 283694278657419211652871983)
    ·
      refine ⟨425541417986128817479307975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283694278657419211652871983 425541417986128817479307975)
      ·
        refine ⟨638312126979193226218961963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425541417986128817479307975 638312126979193226218961963)
        ·
          refine ⟨957468190468789839328442945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638312126979193226218961963 957468190468789839328442945)
          ·
            refine ⟨718101142851592379496332209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957468190468789839328442945 718101142851592379496332209)
            ·
              refine ⟨538575857138694284622249157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718101142851592379496332209 538575857138694284622249157)
              ·
                refine ⟨100982973213505178366671717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538575857138694284622249157 100982973213505178366671717)
                ·
                  refine ⟨18934307477532220943750947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100982973213505178366671717 18934307477532220943750947)
                  ·
                    refine ⟨28401461216298331415626421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18934307477532220943750947 28401461216298331415626421)
                    ·
                      refine ⟨2662636989027968570214977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28401461216298331415626421 2662636989027968570214977)
                      ·
                        rfl

theorem cell23_5185467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_5185467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185467 prefixEnd_5185467 := by exact prefixLift 5185467
  have htrace : WordTrace (prefixWord ++ tailWord_5185467) baseStart_5185467 baseEnd_5185467 := by
    simpa [prefixWord, tailWord_5185467, baseEnd_5185467] using wordTrace_append hprefix tailTrace_5185467
  have hstable : (prefixWord ++ tailWord_5185467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185467).length < 2 ^ (prefixWord ++ tailWord_5185467).sum := by decide
  have hdescent : baseEnd_5185467 < baseStart_5185467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185484 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5185484 : Nat := 118140960795 + 5185484 * 2 ^ 59
def prefixEnd_5185484 : Nat := 4983230072969 + 3 ^ 40 * 5185484 * 2
def baseEnd_5185484 : Nat := 2662645718199095003702399

theorem tailTrace_5185484 : CollatzResearch.WordTrace tailWord_5185484 prefixEnd_5185484 2662645718199095003702399 := by
  unfold tailWord_5185484
  simp only [CollatzResearch.WordTrace]
  refine ⟨94565069572942276502641753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126086759430589702003522337 94565069572942276502641753)
  ·
    refine ⟨70923802179706707376981315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94565069572942276502641753 70923802179706707376981315)
    ·
      refine ⟨106385703269560061065471973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70923802179706707376981315 106385703269560061065471973)
      ·
        refine ⟨19947319363042511449775995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106385703269560061065471973 19947319363042511449775995)
        ·
          refine ⟨29920979044563767174663993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19947319363042511449775995 29920979044563767174663993)
          ·
            refine ⟨22440734283422825380997995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29920979044563767174663993 22440734283422825380997995)
            ·
              refine ⟨33661101425134238071496993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22440734283422825380997995 33661101425134238071496993)
              ·
                refine ⟨25245826068850678553622745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33661101425134238071496993 25245826068850678553622745)
                ·
                  refine ⟨18934369551638008915217059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25245826068850678553622745 18934369551638008915217059)
                  ·
                    refine ⟨28401554327457013372825589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18934369551638008915217059 28401554327457013372825589)
                    ·
                      refine ⟨2662645718199095003702399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28401554327457013372825589 2662645718199095003702399)
                      ·
                        rfl

theorem cell23_5185484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5185484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185484 prefixEnd_5185484 := by exact prefixLift 5185484
  have htrace : WordTrace (prefixWord ++ tailWord_5185484) baseStart_5185484 baseEnd_5185484 := by
    simpa [prefixWord, tailWord_5185484, baseEnd_5185484] using wordTrace_append hprefix tailTrace_5185484
  have hstable : (prefixWord ++ tailWord_5185484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185484).length < 2 ^ (prefixWord ++ tailWord_5185484).sum := by decide
  have hdescent : baseEnd_5185484 < baseStart_5185484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185487 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 9]
def baseStart_5185487 : Nat := 118140960795 + 5185487 * 2 ^ 59
def prefixEnd_5185487 : Nat := 4983230072969 + 3 ^ 40 * 5185487 * 2
def baseEnd_5185487 : Nat := 295849695404562054662765

theorem tailTrace_5185487 : CollatzResearch.WordTrace tailWord_5185487 prefixEnd_5185487 295849695404562054662765 := by
  unfold tailWord_5185487
  simp only [CollatzResearch.WordTrace]
  refine ⟨189130248564873684517642715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126086832376582456345095143 189130248564873684517642715)
  ·
    refine ⟨283695372847310526776464073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189130248564873684517642715 283695372847310526776464073)
    ·
      refine ⟨212771529635482895082348055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283695372847310526776464073 212771529635482895082348055)
      ·
        refine ⟨319157294453224342623522083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212771529635482895082348055 319157294453224342623522083)
        ·
          refine ⟨478735941679836513935283125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319157294453224342623522083 478735941679836513935283125)
          ·
            refine ⟨44881494532484673181432793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 478735941679836513935283125 44881494532484673181432793)
            ·
              refine ⟨33661120899363504886074595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44881494532484673181432793 33661120899363504886074595)
              ·
                refine ⟨50491681349045257329111893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33661120899363504886074595 50491681349045257329111893)
                ·
                  refine ⟨295849695404562054662765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50491681349045257329111893 295849695404562054662765)
                  ·
                    rfl

theorem cell23_5185487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 9].length) (baseStart_5185487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185487 prefixEnd_5185487 := by exact prefixLift 5185487
  have htrace : WordTrace (prefixWord ++ tailWord_5185487) baseStart_5185487 baseEnd_5185487 := by
    simpa [prefixWord, tailWord_5185487, baseEnd_5185487] using wordTrace_append hprefix tailTrace_5185487
  have hstable : (prefixWord ++ tailWord_5185487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185487).length < 2 ^ (prefixWord ++ tailWord_5185487).sum := by decide
  have hdescent : baseEnd_5185487 < baseStart_5185487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185498 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2]
def baseStart_5185498 : Nat := 118140960795 + 5185498 * 2 ^ 59
def prefixEnd_5185498 : Nat := 4983230072969 + 3 ^ 40 * 5185498 * 2
def baseEnd_5185498 : Nat := 2662652906928257948927335

theorem tailTrace_5185498 : CollatzResearch.WordTrace tailWord_5185498 prefixEnd_5185498 2662652906928257948927335 := by
  unfold tailWord_5185498
  simp only [CollatzResearch.WordTrace]
  refine ⟨47282662441958458349073287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126087099845222555597528765 47282662441958458349073287)
  ·
    refine ⟨70923993662937687523609931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47282662441958458349073287 70923993662937687523609931)
    ·
      refine ⟨106385990494406531285414897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70923993662937687523609931 106385990494406531285414897)
      ·
        refine ⟨79789492870804898464061173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106385990494406531285414897 79789492870804898464061173)
        ·
          refine ⟨7480264956637959231005735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79789492870804898464061173 7480264956637959231005735)
          ·
            refine ⟨11220397434956938846508603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7480264956637959231005735 11220397434956938846508603)
            ·
              refine ⟨16830596152435408269762905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11220397434956938846508603 16830596152435408269762905)
              ·
                refine ⟨12622947114326556202322179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16830596152435408269762905 12622947114326556202322179)
                ·
                  refine ⟨18934420671489834303483269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12622947114326556202322179 18934420671489834303483269)
                  ·
                    refine ⟨3550203875904343931903113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18934420671489834303483269 3550203875904343931903113)
                    ·
                      refine ⟨2662652906928257948927335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550203875904343931903113 2662652906928257948927335)
                      ·
                        rfl

theorem cell23_5185498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_5185498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185498 prefixEnd_5185498 := by exact prefixLift 5185498
  have htrace : WordTrace (prefixWord ++ tailWord_5185498) baseStart_5185498 baseEnd_5185498 := by
    simpa [prefixWord, tailWord_5185498, baseEnd_5185498] using wordTrace_append hprefix tailTrace_5185498
  have hstable : (prefixWord ++ tailWord_5185498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185498).length < 2 ^ (prefixWord ++ tailWord_5185498).sum := by decide
  have hdescent : baseEnd_5185498 < baseStart_5185498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185571 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 4, 4, 2]
def baseStart_5185571 : Nat := 118140960795 + 5185571 * 2 ^ 59
def prefixEnd_5185571 : Nat := 4983230072969 + 3 ^ 40 * 5185571 * 2
def baseEnd_5185571 : Nat := 2662690391016036163314499

theorem tailTrace_5185571 : CollatzResearch.WordTrace tailWord_5185571 prefixEnd_5185571 2662690391016036163314499 := by
  unfold tailWord_5185571
  simp only [CollatzResearch.WordTrace]
  refine ⟨189133312296569366863700567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126088874864379577909133711 189133312296569366863700567)
  ·
    refine ⟨283699968444854050295550851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189133312296569366863700567 283699968444854050295550851)
    ·
      refine ⟨425549952667281075443326277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283699968444854050295550851 425549952667281075443326277)
      ·
        refine ⟨79790616125115201645623677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 425549952667281075443326277 79790616125115201645623677)
        ·
          refine ⟨29921481046918200617108879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79790616125115201645623677 29921481046918200617108879)
          ·
            refine ⟨44882221570377300925663319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29921481046918200617108879 44882221570377300925663319)
            ·
              refine ⟨67323332355565951388494979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44882221570377300925663319 67323332355565951388494979)
              ·
                refine ⟨100984998533348927082742469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67323332355565951388494979 100984998533348927082742469)
                ·
                  refine ⟨18934687225002923828014213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100984998533348927082742469 18934687225002923828014213)
                  ·
                    refine ⟨3550253854688048217752665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18934687225002923828014213 3550253854688048217752665)
                    ·
                      refine ⟨2662690391016036163314499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550253854688048217752665 2662690391016036163314499)
                      ·
                        rfl

theorem cell23_5185571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_5185571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185571 prefixEnd_5185571 := by exact prefixLift 5185571
  have htrace : WordTrace (prefixWord ++ tailWord_5185571) baseStart_5185571 baseEnd_5185571 := by
    simpa [prefixWord, tailWord_5185571, baseEnd_5185571] using wordTrace_append hprefix tailTrace_5185571
  have hstable : (prefixWord ++ tailWord_5185571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185571).length < 2 ^ (prefixWord ++ tailWord_5185571).sum := by decide
  have hdescent : baseEnd_5185571 < baseStart_5185571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185631 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 3, 5, 2]
def baseStart_5185631 : Nat := 118140960795 + 5185631 * 2 ^ 59
def prefixEnd_5185631 : Nat := 4983230072969 + 3 ^ 40 * 5185631 * 2
def baseEnd_5185631 : Nat := 2662721199855305928564223

theorem tailTrace_5185631 : CollatzResearch.WordTrace tailWord_5185631 prefixEnd_5185631 2662721199855305928564223 := by
  unfold tailWord_5185631
  simp only [CollatzResearch.WordTrace]
  refine ⟨189135500676351997110884747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126090333784234664740589831 189135500676351997110884747)
  ·
    refine ⟨283703251014527995666327121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189135500676351997110884747 283703251014527995666327121)
    ·
      refine ⟨212777438260895996749745341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283703251014527995666327121 212777438260895996749745341)
      ·
        refine ⟨79791539347835998781154503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212777438260895996749745341 79791539347835998781154503)
        ·
          refine ⟨119687309021753998171731755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79791539347835998781154503 119687309021753998171731755)
          ·
            refine ⟨179530963532630997257597633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119687309021753998171731755 179530963532630997257597633)
            ·
              refine ⟨134648222649473247943198225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179530963532630997257597633 134648222649473247943198225)
              ·
                refine ⟨100986166987104935957398669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134648222649473247943198225 100986166987104935957398669)
                ·
                  refine ⟨37869812620164350984024501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100986166987104935957398669 37869812620164350984024501)
                  ·
                    refine ⟨3550294933140407904752297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37869812620164350984024501 3550294933140407904752297)
                    ·
                      refine ⟨2662721199855305928564223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550294933140407904752297 2662721199855305928564223)
                      ·
                        rfl

theorem cell23_5185631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_5185631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185631 prefixEnd_5185631 := by exact prefixLift 5185631
  have htrace : WordTrace (prefixWord ++ tailWord_5185631) baseStart_5185631 baseEnd_5185631 := by
    simpa [prefixWord, tailWord_5185631, baseEnd_5185631] using wordTrace_append hprefix tailTrace_5185631
  have hstable : (prefixWord ++ tailWord_5185631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185631).length < 2 ^ (prefixWord ++ tailWord_5185631).sum := by decide
  have hdescent : baseEnd_5185631 < baseStart_5185631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185671 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 6, 4]
def baseStart_5185671 : Nat := 118140960795 + 5185671 * 2 ^ 59
def prefixEnd_5185671 : Nat := 4983230072969 + 3 ^ 40 * 5185671 * 2
def baseEnd_5185671 : Nat := 887580579693828590688013

theorem tailTrace_5185671 : CollatzResearch.WordTrace tailWord_5185671 prefixEnd_5185671 887580579693828590688013 := by
  unfold tailWord_5185671
  simp only [CollatzResearch.WordTrace]
  refine ⟨189136959596207083942340867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126091306397471389294893911 189136959596207083942340867)
  ·
    refine ⟨283705439394310625913511301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189136959596207083942340867 283705439394310625913511301)
    ·
      refine ⟨53194769886433242358783369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283705439394310625913511301 53194769886433242358783369)
      ·
        refine ⟨39896077414824931769087527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53194769886433242358783369 39896077414824931769087527)
        ·
          refine ⟨59844116122237397653631291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39896077414824931769087527 59844116122237397653631291)
          ·
            refine ⟨89766174183356096480446937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59844116122237397653631291 89766174183356096480446937)
            ·
              refine ⟨67324630637517072360335203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89766174183356096480446937 67324630637517072360335203)
              ·
                refine ⟨100986945956275608540502805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67324630637517072360335203 100986945956275608540502805)
                ·
                  refine ⟨4733763091700419150336069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100986945956275608540502805 4733763091700419150336069)
                  ·
                    refine ⟨887580579693828590688013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4733763091700419150336069 887580579693828590688013)
                    ·
                      rfl

theorem cell23_5185671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_5185671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185671 prefixEnd_5185671 := by exact prefixLift 5185671
  have htrace : WordTrace (prefixWord ++ tailWord_5185671) baseStart_5185671 baseEnd_5185671 := by
    simpa [prefixWord, tailWord_5185671, baseEnd_5185671] using wordTrace_append hprefix tailTrace_5185671
  have hstable : (prefixWord ++ tailWord_5185671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185671).length < 2 ^ (prefixWord ++ tailWord_5185671).sum := by decide
  have hdescent : baseEnd_5185671 < baseStart_5185671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185728 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 3]
def baseStart_5185728 : Nat := 118140960795 + 5185728 * 2 ^ 59
def prefixEnd_5185728 : Nat := 4983230072969 + 3 ^ 40 * 5185728 * 2
def baseEnd_5185728 : Nat := 2662771007478792049051277

theorem tailTrace_5185728 : CollatzResearch.WordTrace tailWord_5185728 prefixEnd_5185728 2662771007478792049051277 := by
  unfold tailWord_5185728
  simp only [CollatzResearch.WordTrace]
  refine ⟨94569519278500291338582919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126092692371333721784777225 94569519278500291338582919)
  ·
    refine ⟨141854278917750437007874379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94569519278500291338582919 141854278917750437007874379)
    ·
      refine ⟨212781418376625655511811569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141854278917750437007874379 212781418376625655511811569)
      ·
        refine ⟨159586063782469241633858677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212781418376625655511811569 159586063782469241633858677)
        ·
          refine ⟨14961193479606491403174251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159586063782469241633858677 14961193479606491403174251)
          ·
            refine ⟨22441790219409737104761377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14961193479606491403174251 22441790219409737104761377)
            ·
              refine ⟨16831342664557302828571033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22441790219409737104761377 16831342664557302828571033)
              ·
                refine ⟨12623506998417977121428275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16831342664557302828571033 12623506998417977121428275)
                ·
                  refine ⟨18935260497626965682142413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12623506998417977121428275 18935260497626965682142413)
                  ·
                    refine ⟨7100722686610112130803405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18935260497626965682142413 7100722686610112130803405)
                    ·
                      refine ⟨2662771007478792049051277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7100722686610112130803405 2662771007478792049051277)
                      ·
                        rfl

theorem cell23_5185728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_5185728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185728 prefixEnd_5185728 := by exact prefixLift 5185728
  have htrace : WordTrace (prefixWord ++ tailWord_5185728) baseStart_5185728 baseEnd_5185728 := by
    simpa [prefixWord, tailWord_5185728, baseEnd_5185728] using wordTrace_append hprefix tailTrace_5185728
  have hstable : (prefixWord ++ tailWord_5185728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185728).length < 2 ^ (prefixWord ++ tailWord_5185728).sum := by decide
  have hdescent : baseEnd_5185728 < baseStart_5185728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185729 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5185729 : Nat := 118140960795 + 5185729 * 2 ^ 59
def prefixEnd_5185729 : Nat := 4983230072969 + 3 ^ 40 * 5185729 * 2
def baseEnd_5185729 : Nat := 2662771520959446545138773

theorem tailTrace_5185729 : CollatzResearch.WordTrace tailWord_5185729 prefixEnd_5185729 2662771520959446545138773 := by
  unfold tailWord_5185729
  simp only [CollatzResearch.WordTrace]
  refine ⟨189139075029996959847952241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126092716686664639898634827 189139075029996959847952241)
  ·
    refine ⟨141854306272497719885964181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189139075029996959847952241 141854306272497719885964181)
    ·
      refine ⟨6649420606523330619654571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 141854306272497719885964181 6649420606523330619654571)
      ·
        refine ⟨9974130909784995929481857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6649420606523330619654571 9974130909784995929481857)
        ·
          refine ⟨7480598182338746947111393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9974130909784995929481857 7480598182338746947111393)
          ·
            refine ⟨5610448636754060210333545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7480598182338746947111393 5610448636754060210333545)
            ·
              refine ⟨4207836477565545157750159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5610448636754060210333545 4207836477565545157750159)
              ·
                refine ⟨6311754716348317736625239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4207836477565545157750159 6311754716348317736625239)
                ·
                  refine ⟨9467632074522476604937859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6311754716348317736625239 9467632074522476604937859)
                  ·
                    refine ⟨14201448111783714907406789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9467632074522476604937859 14201448111783714907406789)
                    ·
                      refine ⟨2662771520959446545138773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14201448111783714907406789 2662771520959446545138773)
                      ·
                        rfl

theorem cell23_5185729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5185729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185729 prefixEnd_5185729 := by exact prefixLift 5185729
  have htrace : WordTrace (prefixWord ++ tailWord_5185729) baseStart_5185729 baseEnd_5185729 := by
    simpa [prefixWord, tailWord_5185729, baseEnd_5185729] using wordTrace_append hprefix tailTrace_5185729
  have hstable : (prefixWord ++ tailWord_5185729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185729).length < 2 ^ (prefixWord ++ tailWord_5185729).sum := by decide
  have hdescent : baseEnd_5185729 < baseStart_5185729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185732 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_5185732 : Nat := 118140960795 + 5185732 * 2 ^ 59
def prefixEnd_5185732 : Nat := 4983230072969 + 3 ^ 40 * 5185732 * 2
def baseEnd_5185732 : Nat := 2662773061401410033401259

theorem tailTrace_5185732 : CollatzResearch.WordTrace tailWord_5185732 prefixEnd_5185732 2662773061401410033401259 := by
  unfold tailWord_5185732
  simp only [CollatzResearch.WordTrace]
  refine ⟨94569592224493045680155725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126092789632657394240207633 94569592224493045680155725)
  ·
    refine ⟨35463597084184892130058397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94569592224493045680155725 35463597084184892130058397)
    ·
      refine ⟨13298848906569334548771899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35463597084184892130058397 13298848906569334548771899)
      ·
        refine ⟨19948273359854001823157849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13298848906569334548771899 19948273359854001823157849)
        ·
          refine ⟨14961205019890501367368387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19948273359854001823157849 14961205019890501367368387)
          ·
            refine ⟨22441807529835752051052581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14961205019890501367368387 22441807529835752051052581)
            ·
              refine ⟨4207838911844203509572359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22441807529835752051052581 4207838911844203509572359)
              ·
                refine ⟨6311758367766305264358539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4207838911844203509572359 6311758367766305264358539)
                ·
                  refine ⟨9467637551649457896537809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6311758367766305264358539 9467637551649457896537809)
                  ·
                    refine ⟨7100728163737093422403357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9467637551649457896537809 7100728163737093422403357)
                    ·
                      refine ⟨2662773061401410033401259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7100728163737093422403357 2662773061401410033401259)
                      ·
                        rfl

theorem cell23_5185732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_5185732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185732 prefixEnd_5185732 := by exact prefixLift 5185732
  have htrace : WordTrace (prefixWord ++ tailWord_5185732) baseStart_5185732 baseEnd_5185732 := by
    simpa [prefixWord, tailWord_5185732, baseEnd_5185732] using wordTrace_append hprefix tailTrace_5185732
  have hstable : (prefixWord ++ tailWord_5185732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185732).length < 2 ^ (prefixWord ++ tailWord_5185732).sum := by decide
  have hdescent : baseEnd_5185732 < baseStart_5185732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185745 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_5185745 : Nat := 118140960795 + 5185745 * 2 ^ 59
def prefixEnd_5185745 : Nat := 4983230072969 + 3 ^ 40 * 5185745 * 2
def baseEnd_5185745 : Nat := 2662779736649918482538699

theorem tailTrace_5185745 : CollatzResearch.WordTrace tailWord_5185745 prefixEnd_5185745 2662779736649918482538699 := by
  unfold tailWord_5185745
  simp only [CollatzResearch.WordTrace]
  refine ⟨189139658597938994580534689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126093105731959329720356459 189139658597938994580534689)
  ·
    refine ⟨141854743948454245935401017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189139658597938994580534689 141854743948454245935401017)
    ·
      refine ⟨106391057961340684451550763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141854743948454245935401017 106391057961340684451550763)
      ·
        refine ⟨159586586942011026677326145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106391057961340684451550763 159586586942011026677326145)
        ·
          refine ⟨119689940206508270007994609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159586586942011026677326145 119689940206508270007994609)
          ·
            refine ⟨89767455154881202505995957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119689940206508270007994609 89767455154881202505995957)
            ·
              refine ⟨8415698920770112734937121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89767455154881202505995957 8415698920770112734937121)
              ·
                refine ⟨6311774190577584551202841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8415698920770112734937121 6311774190577584551202841)
                ·
                  refine ⟨4733830642933188413402131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6311774190577584551202841 4733830642933188413402131)
                  ·
                    refine ⟨7100745964399782620103197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4733830642933188413402131 7100745964399782620103197)
                    ·
                      refine ⟨2662779736649918482538699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7100745964399782620103197 2662779736649918482538699)
                      ·
                        rfl

theorem cell23_5185745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_5185745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185745 prefixEnd_5185745 := by exact prefixLift 5185745
  have htrace : WordTrace (prefixWord ++ tailWord_5185745) baseStart_5185745 baseEnd_5185745 := by
    simpa [prefixWord, tailWord_5185745, baseEnd_5185745] using wordTrace_append hprefix tailTrace_5185745
  have hstable : (prefixWord ++ tailWord_5185745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185745).length < 2 ^ (prefixWord ++ tailWord_5185745).sum := by decide
  have hdescent : baseEnd_5185745 < baseStart_5185745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185761 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 2, 6]
def baseStart_5185761 : Nat := 118140960795 + 5185761 * 2 ^ 59
def prefixEnd_5185761 : Nat := 4983230072969 + 3 ^ 40 * 5185761 * 2
def baseEnd_5185761 : Nat := 887595984113463473312875

theorem tailTrace_5185761 : CollatzResearch.WordTrace tailWord_5185761 prefixEnd_5185761 887595984113463473312875 := by
  unfold tailWord_5185761
  simp only [CollatzResearch.WordTrace]
  refine ⟨189140242165881029313117137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126093494777254019542078091 189140242165881029313117137)
  ·
    refine ⟨141855181624410771984837853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189140242165881029313117137 141855181624410771984837853)
    ·
      refine ⟨53195693109154039494314195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141855181624410771984837853 53195693109154039494314195)
      ·
        refine ⟨79793539663731059241471293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53195693109154039494314195 79793539663731059241471293)
        ·
          refine ⟨29922577373899147215551735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79793539663731059241471293 29922577373899147215551735)
          ·
            refine ⟨44883866060848720823327603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29922577373899147215551735 44883866060848720823327603)
            ·
              refine ⟨67325799091273081234991405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44883866060848720823327603 67325799091273081234991405)
              ·
                refine ⟨25247174659227405463121777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67325799091273081234991405 25247174659227405463121777)
                ·
                  refine ⟨18935380994420554097341333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25247174659227405463121777 18935380994420554097341333)
                  ·
                    refine ⟨887595984113463473312875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18935380994420554097341333 887595984113463473312875)
                    ·
                      rfl

theorem cell23_5185761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_5185761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185761 prefixEnd_5185761 := by exact prefixLift 5185761
  have htrace : WordTrace (prefixWord ++ tailWord_5185761) baseStart_5185761 baseEnd_5185761 := by
    simpa [prefixWord, tailWord_5185761, baseEnd_5185761] using wordTrace_append hprefix tailTrace_5185761
  have hstable : (prefixWord ++ tailWord_5185761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185761).length < 2 ^ (prefixWord ++ tailWord_5185761).sum := by decide
  have hdescent : baseEnd_5185761 < baseStart_5185761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185771 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 5]
def baseStart_5185771 : Nat := 118140960795 + 5185771 * 2 ^ 59
def prefixEnd_5185771 : Nat := 4983230072969 + 3 ^ 40 * 5185771 * 2
def baseEnd_5185771 : Nat := 2662793087146935380813579

theorem tailTrace_5185771 : CollatzResearch.WordTrace tailWord_5185771 prefixEnd_5185771 2662793087146935380813579 := by
  unfold tailWord_5185771
  simp only [CollatzResearch.WordTrace]
  refine ⟨189140606895844801020981167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126093737930563200680654111 189140606895844801020981167)
  ·
    refine ⟨283710910343767201531471751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189140606895844801020981167 283710910343767201531471751)
    ·
      refine ⟨425566365515650802297207627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283710910343767201531471751 425566365515650802297207627)
      ·
        refine ⟨638349548273476203445811441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425566365515650802297207627 638349548273476203445811441)
        ·
          refine ⟨478762161205107152584358581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638349548273476203445811441 478762161205107152584358581)
          ·
            refine ⟨44883952612978795554783617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 478762161205107152584358581 44883952612978795554783617)
            ·
              refine ⟨33662964459734096666087713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44883952612978795554783617 33662964459734096666087713)
              ·
                refine ⟨25247223344800572499565785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33662964459734096666087713 25247223344800572499565785)
                ·
                  refine ⟨18935417508600429374674339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25247223344800572499565785 18935417508600429374674339)
                  ·
                    refine ⟨28403126262900644062011509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18935417508600429374674339 28403126262900644062011509)
                    ·
                      refine ⟨2662793087146935380813579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28403126262900644062011509 2662793087146935380813579)
                      ·
                        rfl

theorem cell23_5185771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_5185771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185771 prefixEnd_5185771 := by exact prefixLift 5185771
  have htrace : WordTrace (prefixWord ++ tailWord_5185771) baseStart_5185771 baseEnd_5185771 := by
    simpa [prefixWord, tailWord_5185771, baseEnd_5185771] using wordTrace_append hprefix tailTrace_5185771
  have hstable : (prefixWord ++ tailWord_5185771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185771).length < 2 ^ (prefixWord ++ tailWord_5185771).sum := by decide
  have hdescent : baseEnd_5185771 < baseStart_5185771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185788 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_5185788 : Nat := 118140960795 + 5185788 * 2 ^ 59
def prefixEnd_5185788 : Nat := 4983230072969 + 3 ^ 40 * 5185788 * 2
def baseEnd_5185788 : Nat := 2662801816318061814301001

theorem tailTrace_5185788 : CollatzResearch.WordTrace tailWord_5185788 prefixEnd_5185788 2662801816318061814301001 := by
  unfold tailWord_5185788
  simp only [CollatzResearch.WordTrace]
  refine ⟨94570613468391606462175009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126094151291188808616233345 94570613468391606462175009)
  ·
    refine ⟨70927960101293704846631257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94570613468391606462175009 70927960101293704846631257)
    ·
      refine ⟨53195970075970278634973443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70927960101293704846631257 53195970075970278634973443)
      ·
        refine ⟨79793955113955417952460165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53195970075970278634973443 79793955113955417952460165)
        ·
          refine ⟨14961366583866640866086281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79793955113955417952460165 14961366583866640866086281)
          ·
            refine ⟨11221024937899980649564711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14961366583866640866086281 11221024937899980649564711)
            ·
              refine ⟨16831537406849970974347067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11221024937899980649564711 16831537406849970974347067)
              ·
                refine ⟨25247306110274956461520601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16831537406849970974347067 25247306110274956461520601)
                ·
                  refine ⟨18935479582706217346140451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25247306110274956461520601 18935479582706217346140451)
                  ·
                    refine ⟨28403219374059326019210677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18935479582706217346140451 28403219374059326019210677)
                    ·
                      refine ⟨2662801816318061814301001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28403219374059326019210677 2662801816318061814301001)
                      ·
                        rfl

theorem cell23_5185788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_5185788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185788 prefixEnd_5185788 := by exact prefixLift 5185788
  have htrace : WordTrace (prefixWord ++ tailWord_5185788) baseStart_5185788 baseEnd_5185788 := by
    simpa [prefixWord, tailWord_5185788, baseEnd_5185788] using wordTrace_append hprefix tailTrace_5185788
  have hstable : (prefixWord ++ tailWord_5185788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185788).length < 2 ^ (prefixWord ++ tailWord_5185788).sum := by decide
  have hdescent : baseEnd_5185788 < baseStart_5185788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185871 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_5185871 : Nat := 118140960795 + 5185871 * 2 ^ 59
def prefixEnd_5185871 : Nat := 4983230072969 + 3 ^ 40 * 5185871 * 2
def baseEnd_5185871 : Nat := 2662844435212384989563119

theorem tailTrace_5185871 : CollatzResearch.WordTrace tailWord_5185871 prefixEnd_5185871 2662844435212384989563119 := by
  unfold tailWord_5185871
  simp only [CollatzResearch.WordTrace]
  refine ⟨189144254195482518099621467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126096169463655012066414311 189144254195482518099621467)
  ·
    refine ⟨283716381293223777149432201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189144254195482518099621467 283716381293223777149432201)
    ·
      refine ⟨212787285969917832862074151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283716381293223777149432201 212787285969917832862074151)
      ·
        refine ⟨319180928954876749293111227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212787285969917832862074151 319180928954876749293111227)
        ·
          refine ⟨478771393432315123939666841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319180928954876749293111227 478771393432315123939666841)
          ·
            refine ⟨359078545074236342954750131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478771393432315123939666841 359078545074236342954750131)
            ·
              refine ⟨538617817611354514432125197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359078545074236342954750131 538617817611354514432125197)
              ·
                refine ⟨201981681604257942912046949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538617817611354514432125197 201981681604257942912046949)
                ·
                  refine ⟨37871565300798364296008803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201981681604257942912046949 37871565300798364296008803)
                  ·
                    refine ⟨56807347951197546444013205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37871565300798364296008803 56807347951197546444013205)
                    ·
                      refine ⟨2662844435212384989563119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56807347951197546444013205 2662844435212384989563119)
                      ·
                        rfl

theorem cell23_5185871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_5185871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185871 prefixEnd_5185871 := by exact prefixLift 5185871
  have htrace : WordTrace (prefixWord ++ tailWord_5185871) baseStart_5185871 baseEnd_5185871 := by
    simpa [prefixWord, tailWord_5185871, baseEnd_5185871] using wordTrace_append hprefix tailTrace_5185871
  have hstable : (prefixWord ++ tailWord_5185871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185871).length < 2 ^ (prefixWord ++ tailWord_5185871).sum := by decide
  have hdescent : baseEnd_5185871 < baseStart_5185871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185881 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 10]
def baseStart_5185881 : Nat := 118140960795 + 5185881 * 2 ^ 59
def prefixEnd_5185881 : Nat := 4983230072969 + 3 ^ 40 * 5185881 * 2
def baseEnd_5185881 : Nat := 295872174446547772270897

theorem tailTrace_5185881 : CollatzResearch.WordTrace tailWord_5185881 prefixEnd_5185881 295872174446547772270897 := by
  unfold tailWord_5185881
  simp only [CollatzResearch.WordTrace]
  refine ⟨189144618925446289807485497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126096412616964193204990331 189144618925446289807485497)
  ·
    refine ⟨141858464194084717355614123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189144618925446289807485497 141858464194084717355614123)
    ·
      refine ⟨212787696291127076033421185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141858464194084717355614123 212787696291127076033421185)
      ·
        refine ⟨159590772218345307025065889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212787696291127076033421185 159590772218345307025065889)
        ·
          refine ⟨119693079163758980268799417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159590772218345307025065889 119693079163758980268799417)
          ·
            refine ⟨89769809372819235201599563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119693079163758980268799417 89769809372819235201599563)
            ·
              refine ⟨134654714059228852802399345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89769809372819235201599563 134654714059228852802399345)
              ·
                refine ⟨100991035544421639601799509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134654714059228852802399345 100991035544421639601799509)
                ·
                  refine ⟨295872174446547772270897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 100991035544421639601799509 295872174446547772270897)
                  ·
                    rfl

theorem cell23_5185881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 10].length) (baseStart_5185881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185881 prefixEnd_5185881 := by exact prefixLift 5185881
  have htrace : WordTrace (prefixWord ++ tailWord_5185881) baseStart_5185881 baseEnd_5185881 := by
    simpa [prefixWord, tailWord_5185881, baseEnd_5185881] using wordTrace_append hprefix tailTrace_5185881
  have hstable : (prefixWord ++ tailWord_5185881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185881).length < 2 ^ (prefixWord ++ tailWord_5185881).sum := by decide
  have hdescent : baseEnd_5185881 < baseStart_5185881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185895 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_5185895 : Nat := 118140960795 + 5185895 * 2 ^ 59
def prefixEnd_5185895 : Nat := 4983230072969 + 3 ^ 40 * 5185895 * 2
def baseEnd_5185895 : Nat := 2662856758748092895663009

theorem tailTrace_5185895 : CollatzResearch.WordTrace tailWord_5185895 prefixEnd_5185895 2662856758748092895663009 := by
  unfold tailWord_5185895
  simp only [CollatzResearch.WordTrace]
  refine ⟨189145129547395570198495139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126096753031597046798996759 189145129547395570198495139)
  ·
    refine ⟨283717694321093355297742709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189145129547395570198495139 283717694321093355297742709)
    ·
      refine ⟨26598533842602502059163379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 283717694321093355297742709 26598533842602502059163379)
      ·
        refine ⟨39897800763903753088745069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26598533842602502059163379 39897800763903753088745069)
        ·
          refine ⟨14961675286463907408279401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39897800763903753088745069 14961675286463907408279401)
          ·
            refine ⟨11221256464847930556209551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14961675286463907408279401 11221256464847930556209551)
            ·
              refine ⟨16831884697271895834314327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11221256464847930556209551 16831884697271895834314327)
              ·
                refine ⟨25247827045907843751471491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16831884697271895834314327 25247827045907843751471491)
                ·
                  refine ⟨37871740568861765627207237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25247827045907843751471491 37871740568861765627207237)
                  ·
                    refine ⟨7100951356661581055101357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37871740568861765627207237 7100951356661581055101357)
                    ·
                      refine ⟨2662856758748092895663009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7100951356661581055101357 2662856758748092895663009)
                      ·
                        rfl

theorem cell23_5185895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_5185895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185895 prefixEnd_5185895 := by exact prefixLift 5185895
  have htrace : WordTrace (prefixWord ++ tailWord_5185895) baseStart_5185895 baseEnd_5185895 := by
    simpa [prefixWord, tailWord_5185895, baseEnd_5185895] using wordTrace_append hprefix tailTrace_5185895
  have hstable : (prefixWord ++ tailWord_5185895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185895).length < 2 ^ (prefixWord ++ tailWord_5185895).sum := by decide
  have hdescent : baseEnd_5185895 < baseStart_5185895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185915 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 6]
def baseStart_5185915 : Nat := 118140960795 + 5185915 * 2 ^ 59
def prefixEnd_5185915 : Nat := 4983230072969 + 3 ^ 40 * 5185915 * 2
def baseEnd_5185915 : Nat := 295874114262353646379213

theorem tailTrace_5185915 : CollatzResearch.WordTrace tailWord_5185915 prefixEnd_5185915 295874114262353646379213 := by
  unfold tailWord_5185915
  simp only [CollatzResearch.WordTrace]
  refine ⟨189145859007323113614223199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126097239338215409076148799 189145859007323113614223199)
  ·
    refine ⟨283718788510984670421334799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189145859007323113614223199 283718788510984670421334799)
    ·
      refine ⟨425578182766477005632002199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283718788510984670421334799 425578182766477005632002199)
      ·
        refine ⟨638367274149715508448003299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425578182766477005632002199 638367274149715508448003299)
        ·
          refine ⟨957550911224573262672004949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638367274149715508448003299 957550911224573262672004949)
          ·
            refine ⟨5610649870456483960968779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 957550911224573262672004949 5610649870456483960968779)
            ·
              refine ⟨8415974805684725941453169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610649870456483960968779 8415974805684725941453169)
              ·
                refine ⟨6311981104263544456089877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8415974805684725941453169 6311981104263544456089877)
                ·
                  refine ⟨295874114262353646379213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6311981104263544456089877 295874114262353646379213)
                  ·
                    rfl

theorem cell23_5185915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 6].length) (baseStart_5185915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185915 prefixEnd_5185915 := by exact prefixLift 5185915
  have htrace : WordTrace (prefixWord ++ tailWord_5185915) baseStart_5185915 baseEnd_5185915 := by
    simpa [prefixWord, tailWord_5185915, baseEnd_5185915] using wordTrace_append hprefix tailTrace_5185915
  have hstable : (prefixWord ++ tailWord_5185915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185915).length < 2 ^ (prefixWord ++ tailWord_5185915).sum := by decide
  have hdescent : baseEnd_5185915 < baseStart_5185915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185945 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 1, 5]
def baseStart_5185945 : Nat := 118140960795 + 5185945 * 2 ^ 59
def prefixEnd_5185945 : Nat := 4983230072969 + 3 ^ 40 * 5185945 * 2
def baseEnd_5185945 : Nat := 887627477593605900012593

theorem tailTrace_5185945 : CollatzResearch.WordTrace tailWord_5185945 prefixEnd_5185945 887627477593605900012593 := by
  unfold tailWord_5185945
  simp only [CollatzResearch.WordTrace]
  refine ⟨189146953197214428737815289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126097968798142952491876859 189146953197214428737815289)
  ·
    refine ⟨141860214897910821553361467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189146953197214428737815289 141860214897910821553361467)
    ·
      refine ⟨212790322346866232330042201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141860214897910821553361467 212790322346866232330042201)
      ·
        refine ⟨159592741760149674247531651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212790322346866232330042201 159592741760149674247531651)
        ·
          refine ⟨239389112640224511371297477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159592741760149674247531651 239389112640224511371297477)
          ·
            refine ⟨44885458620042095882118277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239389112640224511371297477 44885458620042095882118277)
            ·
              refine ⟨8416023491257892977897177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44885458620042095882118277 8416023491257892977897177)
              ·
                refine ⟨6312017618443419733422883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8416023491257892977897177 6312017618443419733422883)
                ·
                  refine ⟨9468026427665129600134325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6312017618443419733422883 9468026427665129600134325)
                  ·
                    refine ⟨887627477593605900012593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9468026427665129600134325 887627477593605900012593)
                    ·
                      rfl

theorem cell23_5185945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_5185945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185945 prefixEnd_5185945 := by exact prefixLift 5185945
  have htrace : WordTrace (prefixWord ++ tailWord_5185945) baseStart_5185945 baseEnd_5185945 := by
    simpa [prefixWord, tailWord_5185945, baseEnd_5185945] using wordTrace_append hprefix tailTrace_5185945
  have hstable : (prefixWord ++ tailWord_5185945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185945).length < 2 ^ (prefixWord ++ tailWord_5185945).sum := by decide
  have hdescent : baseEnd_5185945 < baseStart_5185945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185953 : List Nat := [1, 2, 3, 5, 2, 1, 1, 3, 1, 4]
def baseStart_5185953 : Nat := 118140960795 + 5185953 * 2 ^ 59
def prefixEnd_5185953 : Nat := 4983230072969 + 3 ^ 40 * 5185953 * 2
def baseEnd_5185953 : Nat := 887628846875351222912581

theorem tailTrace_5185953 : CollatzResearch.WordTrace tailWord_5185953 prefixEnd_5185953 887628846875351222912581 := by
  unfold tailWord_5185953
  simp only [CollatzResearch.WordTrace]
  refine ⟨189147244981185446104106513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126098163320790297402737675 189147244981185446104106513)
  ·
    refine ⟨141860433735889084578079885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189147244981185446104106513 141860433735889084578079885)
    ·
      refine ⟨53197662650958406716779957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141860433735889084578079885 53197662650958406716779957)
      ·
        refine ⟨4987280873527350629698121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53197662650958406716779957 4987280873527350629698121)
        ·
          refine ⟨3740460655145512972273591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4987280873527350629698121 3740460655145512972273591)
          ·
            refine ⟨5610690982718269458410387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740460655145512972273591 5610690982718269458410387)
            ·
              refine ⟨8416036474077404187615581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610690982718269458410387 8416036474077404187615581)
              ·
                refine ⟨3156013677779026570355843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8416036474077404187615581 3156013677779026570355843)
                ·
                  refine ⟨4734020516668539855533765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156013677779026570355843 4734020516668539855533765)
                  ·
                    refine ⟨887628846875351222912581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734020516668539855533765 887628846875351222912581)
                    ·
                      rfl

theorem cell23_5185953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_5185953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185953 prefixEnd_5185953 := by exact prefixLift 5185953
  have htrace : WordTrace (prefixWord ++ tailWord_5185953) baseStart_5185953 baseEnd_5185953 := by
    simpa [prefixWord, tailWord_5185953, baseEnd_5185953] using wordTrace_append hprefix tailTrace_5185953
  have hstable : (prefixWord ++ tailWord_5185953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185953).length < 2 ^ (prefixWord ++ tailWord_5185953).sum := by decide
  have hdescent : baseEnd_5185953 < baseStart_5185953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185968 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 3]
def baseStart_5185968 : Nat := 118140960795 + 5185968 * 2 ^ 59
def prefixEnd_5185968 : Nat := 4983230072969 + 3 ^ 40 * 5185968 * 2
def baseEnd_5185968 : Nat := 2662894242835871110050173

theorem tailTrace_5185968 : CollatzResearch.WordTrace tailWord_5185968 prefixEnd_5185968 2662894242835871110050173 := by
  unfold tailWord_5185968
  simp only [CollatzResearch.WordTrace]
  refine ⟨94573896038065551832951279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126098528050754069110601705 94573896038065551832951279)
  ·
    refine ⟨141860844057098327749426919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94573896038065551832951279 141860844057098327749426919)
    ·
      refine ⟨212791266085647491624140379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141860844057098327749426919 212791266085647491624140379)
      ·
        refine ⟨319186899128471237436210569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212791266085647491624140379 319186899128471237436210569)
        ·
          refine ⟨239390174346353428077157927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319186899128471237436210569 239390174346353428077157927)
          ·
            refine ⟨359085261519530142115736891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239390174346353428077157927 359085261519530142115736891)
            ·
              refine ⟨538627892279295213173605337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359085261519530142115736891 538627892279295213173605337)
              ·
                refine ⟨403970919209471409880204003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538627892279295213173605337 403970919209471409880204003)
                ·
                  refine ⟨605956378814207114820306005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403970919209471409880204003 605956378814207114820306005)
                  ·
                    refine ⟨7101051314228989626800461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 605956378814207114820306005 7101051314228989626800461)
                    ·
                      refine ⟨2662894242835871110050173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7101051314228989626800461 2662894242835871110050173)
                      ·
                        rfl

theorem cell23_5185968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_5185968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185968 prefixEnd_5185968 := by exact prefixLift 5185968
  have htrace : WordTrace (prefixWord ++ tailWord_5185968) baseStart_5185968 baseEnd_5185968 := by
    simpa [prefixWord, tailWord_5185968, baseEnd_5185968] using wordTrace_append hprefix tailTrace_5185968
  have hstable : (prefixWord ++ tailWord_5185968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185968).length < 2 ^ (prefixWord ++ tailWord_5185968).sum := by decide
  have hdescent : baseEnd_5185968 < baseStart_5185968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185975 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 4, 4]
def baseStart_5185975 : Nat := 118140960795 + 5185975 * 2 ^ 59
def prefixEnd_5185975 : Nat := 4983230072969 + 3 ^ 40 * 5185975 * 2
def baseEnd_5185975 : Nat := 887632612400150860887547

theorem tailTrace_5185975 : CollatzResearch.WordTrace tailWord_5185975 prefixEnd_5185975 887632612400150860887547 := by
  unfold tailWord_5185975
  simp only [CollatzResearch.WordTrace]
  refine ⟨189148047387105743861407379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126098698258070495907604919 189148047387105743861407379)
  ·
    refine ⟨283722071080658615792111069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189148047387105743861407379 283722071080658615792111069)
    ·
      refine ⟨106395776655246980922041651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283722071080658615792111069 106395776655246980922041651)
      ·
        refine ⟨159593664982870471383062477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106395776655246980922041651 159593664982870471383062477)
        ·
          refine ⟨59847624368576426768648429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159593664982870471383062477 59847624368576426768648429)
          ·
            refine ⟨22442859138216160038243161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59847624368576426768648429 22442859138216160038243161)
            ·
              refine ⟨16832144353662120028682371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22442859138216160038243161 16832144353662120028682371)
              ·
                refine ⟨25248216530493180043023557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16832144353662120028682371 25248216530493180043023557)
                ·
                  refine ⟨4734040599467471258066917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25248216530493180043023557 4734040599467471258066917)
                  ·
                    refine ⟨887632612400150860887547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734040599467471258066917 887632612400150860887547)
                    ·
                      rfl

theorem cell23_5185975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_5185975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185975 prefixEnd_5185975 := by exact prefixLift 5185975
  have htrace : WordTrace (prefixWord ++ tailWord_5185975) baseStart_5185975 baseEnd_5185975 := by
    simpa [prefixWord, tailWord_5185975, baseEnd_5185975] using wordTrace_append hprefix tailTrace_5185975
  have hstable : (prefixWord ++ tailWord_5185975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185975).length < 2 ^ (prefixWord ++ tailWord_5185975).sum := by decide
  have hdescent : baseEnd_5185975 < baseStart_5185975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5185992 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 2, 4]
def baseStart_5185992 : Nat := 118140960795 + 5185992 * 2 ^ 59
def prefixEnd_5185992 : Nat := 4983230072969 + 3 ^ 40 * 5185992 * 2
def baseEnd_5185992 : Nat := 887635522123859672050021

theorem tailTrace_5185992 : CollatzResearch.WordTrace tailWord_5185992 prefixEnd_5185992 887635522123859672050021 := by
  unfold tailWord_5185992
  simp only [CollatzResearch.WordTrace]
  refine ⟨94574333714022077882388115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126099111618696103843184153 94574333714022077882388115)
  ·
    refine ⟨141861500571033116823582173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94574333714022077882388115 141861500571033116823582173)
    ·
      refine ⟨53198062714137418808843315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141861500571033116823582173 53198062714137418808843315)
      ·
        refine ⟨79797094071206128213264973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53198062714137418808843315 79797094071206128213264973)
        ·
          refine ⟨29923910276702298079974365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79797094071206128213264973 29923910276702298079974365)
          ·
            refine ⟨11221466353763361779990387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29923910276702298079974365 11221466353763361779990387)
            ·
              refine ⟨16832199530645042669985581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11221466353763361779990387 16832199530645042669985581)
              ·
                refine ⟨6312074823991891001244593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16832199530645042669985581 6312074823991891001244593)
                ·
                  refine ⟨4734056117993918250933445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312074823991891001244593 4734056117993918250933445)
                  ·
                    refine ⟨887635522123859672050021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734056117993918250933445 887635522123859672050021)
                    ·
                      rfl

theorem cell23_5185992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_5185992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5185992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5185992 prefixEnd_5185992 := by exact prefixLift 5185992
  have htrace : WordTrace (prefixWord ++ tailWord_5185992) baseStart_5185992 baseEnd_5185992 := by
    simpa [prefixWord, tailWord_5185992, baseEnd_5185992] using wordTrace_append hprefix tailTrace_5185992
  have hstable : (prefixWord ++ tailWord_5185992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5185992).length < 2 ^ (prefixWord ++ tailWord_5185992).sum := by decide
  have hdescent : baseEnd_5185992 < baseStart_5185992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5185992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186015 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 3]
def baseStart_5186015 : Nat := 118140960795 + 5186015 * 2 ^ 59
def prefixEnd_5186015 : Nat := 4983230072969 + 3 ^ 40 * 5186015 * 2
def baseEnd_5186015 : Nat := 2662918376426632426162457

theorem tailTrace_5186015 : CollatzResearch.WordTrace tailWord_5186015 prefixEnd_5186015 2662918376426632426162457 := by
  unfold tailWord_5186015
  simp only [CollatzResearch.WordTrace]
  refine ⟨189149506306960830692863499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126099670871307220461908999 189149506306960830692863499)
  ·
    refine ⟨283724259460441246039295249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189149506306960830692863499 283724259460441246039295249)
    ·
      refine ⟨212793194595330934529471437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283724259460441246039295249 212793194595330934529471437)
      ·
        refine ⟨79797447973249100448551789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212793194595330934529471437 79797447973249100448551789)
        ·
          refine ⟨29924042989968412668206921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79797447973249100448551789 29924042989968412668206921)
          ·
            refine ⟨22443032242476309501155191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29924042989968412668206921 22443032242476309501155191)
            ·
              refine ⟨33664548363714464251732787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22443032242476309501155191 33664548363714464251732787)
              ·
                refine ⟨50496822545571696377599181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33664548363714464251732787 50496822545571696377599181)
                ·
                  refine ⟨18936308454589386141599693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50496822545571696377599181 18936308454589386141599693)
                  ·
                    refine ⟨7101115670471019803099885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18936308454589386141599693 7101115670471019803099885)
                    ·
                      refine ⟨2662918376426632426162457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7101115670471019803099885 2662918376426632426162457)
                      ·
                        rfl

theorem cell23_5186015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_5186015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186015 prefixEnd_5186015 := by exact prefixLift 5186015
  have htrace : WordTrace (prefixWord ++ tailWord_5186015) baseStart_5186015 baseEnd_5186015 := by
    simpa [prefixWord, tailWord_5186015, baseEnd_5186015] using wordTrace_append hprefix tailTrace_5186015
  have hstable : (prefixWord ++ tailWord_5186015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186015).length < 2 ^ (prefixWord ++ tailWord_5186015).sum := by decide
  have hdescent : baseEnd_5186015 < baseStart_5186015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186019 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 1, 1, 5]
def baseStart_5186019 : Nat := 118140960795 + 5186019 * 2 ^ 59
def prefixEnd_5186019 : Nat := 4983230072969 + 3 ^ 40 * 5186019 * 2
def baseEnd_5186019 : Nat := 2662920430349250410512439

theorem tailTrace_5186019 : CollatzResearch.WordTrace tailWord_5186019 prefixEnd_5186019 2662920430349250410512439 := by
  unfold tailWord_5186019
  simp only [CollatzResearch.WordTrace]
  refine ⟨189149652198946339376009111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126099768132630892917339407 189149652198946339376009111)
  ·
    refine ⟨283724478298419509064013667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189149652198946339376009111 283724478298419509064013667)
    ·
      refine ⟨425586717447629263596020501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283724478298419509064013667 425586717447629263596020501)
      ·
        refine ⟨19949377380357621731063461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 425586717447629263596020501 19949377380357621731063461)
        ·
          refine ⟨3740508258817054074574399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19949377380357621731063461 3740508258817054074574399)
          ·
            refine ⟨5610762388225581111861599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740508258817054074574399 5610762388225581111861599)
            ·
              refine ⟨8416143582338371667792399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610762388225581111861599 8416143582338371667792399)
              ·
                refine ⟨12624215373507557501688599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416143582338371667792399 12624215373507557501688599)
                ·
                  refine ⟨18936323060261336252532899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12624215373507557501688599 18936323060261336252532899)
                  ·
                    refine ⟨28404484590392004378799349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18936323060261336252532899 28404484590392004378799349)
                    ·
                      refine ⟨2662920430349250410512439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28404484590392004378799349 2662920430349250410512439)
                      ·
                        rfl

theorem cell23_5186019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_5186019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186019 prefixEnd_5186019 := by exact prefixLift 5186019
  have htrace : WordTrace (prefixWord ++ tailWord_5186019) baseStart_5186019 baseEnd_5186019 := by
    simpa [prefixWord, tailWord_5186019, baseEnd_5186019] using wordTrace_append hprefix tailTrace_5186019
  have hstable : (prefixWord ++ tailWord_5186019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186019).length < 2 ^ (prefixWord ++ tailWord_5186019).sum := by decide
  have hdescent : baseEnd_5186019 < baseStart_5186019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186049 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_5186049 : Nat := 118140960795 + 5186049 * 2 ^ 59
def prefixEnd_5186049 : Nat := 4983230072969 + 3 ^ 40 * 5186049 * 2
def baseEnd_5186049 : Nat := 2662935834768885293137301

theorem tailTrace_5186049 : CollatzResearch.WordTrace tailWord_5186049 prefixEnd_5186049 2662935834768885293137301 := by
  unfold tailWord_5186049
  simp only [CollatzResearch.WordTrace]
  refine ⟨189150746388837654499601201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126100497592558436333067467 189150746388837654499601201)
  ·
    refine ⟨141863059791628240874700901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189150746388837654499601201 141863059791628240874700901)
    ·
      refine ⟨26599323710930295164006419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141863059791628240874700901 26599323710930295164006419)
      ·
        refine ⟨39898985566395442746009629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26599323710930295164006419 39898985566395442746009629)
        ·
          refine ⟨14962119587398291029753611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39898985566395442746009629 14962119587398291029753611)
          ·
            refine ⟨22443179381097436544630417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14962119587398291029753611 22443179381097436544630417)
            ·
              refine ⟨16832384535823077408472813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22443179381097436544630417 16832384535823077408472813)
              ·
                refine ⟨6312144200933654028177305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16832384535823077408472813 6312144200933654028177305)
                ·
                  refine ⟨4734108150700240521132979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312144200933654028177305 4734108150700240521132979)
                  ·
                    refine ⟨7101162226050360781699469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4734108150700240521132979 7101162226050360781699469)
                    ·
                      refine ⟨2662935834768885293137301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7101162226050360781699469 2662935834768885293137301)
                      ·
                        rfl

theorem cell23_5186049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_5186049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186049 prefixEnd_5186049 := by exact prefixLift 5186049
  have htrace : WordTrace (prefixWord ++ tailWord_5186049) baseStart_5186049 baseEnd_5186049 := by
    simpa [prefixWord, tailWord_5186049, baseEnd_5186049] using wordTrace_append hprefix tailTrace_5186049
  have hstable : (prefixWord ++ tailWord_5186049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186049).length < 2 ^ (prefixWord ++ tailWord_5186049).sum := by decide
  have hdescent : baseEnd_5186049 < baseStart_5186049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186076 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_5186076 : Nat := 118140960795 + 5186076 * 2 ^ 59
def prefixEnd_5186076 : Nat := 4983230072969 + 3 ^ 40 * 5186076 * 2
def baseEnd_5186076 : Nat := 2662949698746556687499677

theorem tailTrace_5186076 : CollatzResearch.WordTrace tailWord_5186076 prefixEnd_5186076 2662949698746556687499677 := by
  unfold tailWord_5186076
  simp only [CollatzResearch.WordTrace]
  refine ⟨94575865579869919055417041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126101154106493225407222721 94575865579869919055417041)
  ·
    refine ⟨70931899184902439291562781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94575865579869919055417041 70931899184902439291562781)
    ·
      refine ⟨26599462194338414734336043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70931899184902439291562781 26599462194338414734336043)
      ·
        refine ⟨39899193291507622101504065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26599462194338414734336043 39899193291507622101504065)
        ·
          refine ⟨29924394968630716576128049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39899193291507622101504065 29924394968630716576128049)
          ·
            refine ⟨22443296226473037432096037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29924394968630716576128049 22443296226473037432096037)
            ·
              refine ⟨4208118042463694518518007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22443296226473037432096037 4208118042463694518518007)
              ·
                refine ⟨6312177063695541777777011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208118042463694518518007 6312177063695541777777011)
                ·
                  refine ⟨9468265595543312666665517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6312177063695541777777011 9468265595543312666665517)
                  ·
                    refine ⟨3550599598328742249999569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9468265595543312666665517 3550599598328742249999569)
                    ·
                      refine ⟨2662949698746556687499677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550599598328742249999569 2662949698746556687499677)
                      ·
                        rfl

theorem cell23_5186076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_5186076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186076 prefixEnd_5186076 := by exact prefixLift 5186076
  have htrace : WordTrace (prefixWord ++ tailWord_5186076) baseStart_5186076 baseEnd_5186076 := by
    simpa [prefixWord, tailWord_5186076, baseEnd_5186076] using wordTrace_append hprefix tailTrace_5186076
  have hstable : (prefixWord ++ tailWord_5186076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186076).length < 2 ^ (prefixWord ++ tailWord_5186076).sum := by decide
  have hdescent : baseEnd_5186076 < baseStart_5186076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186085 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_5186085 : Nat := 118140960795 + 5186085 * 2 ^ 59
def prefixEnd_5186085 : Nat := 4983230072969 + 3 ^ 40 * 5186085 * 2
def baseEnd_5186085 : Nat := 2662954320072447152287135

theorem tailTrace_5186085 : CollatzResearch.WordTrace tailWord_5186085 prefixEnd_5186085 2662954320072447152287135 := by
  unfold tailWord_5186085
  simp only [CollatzResearch.WordTrace]
  refine ⟨189152059416707232647911709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126101372944471488431941139 189152059416707232647911709)
  ·
    refine ⟨70932022281265212242966891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189152059416707232647911709 70932022281265212242966891)
    ·
      refine ⟨106398033421897818364450337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70932022281265212242966891 106398033421897818364450337)
      ·
        refine ⟨79798525066423363773337753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106398033421897818364450337 79798525066423363773337753)
        ·
          refine ⟨59848893799817522830003315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79798525066423363773337753 59848893799817522830003315)
          ·
            refine ⟨89773340699726284245004973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59848893799817522830003315 89773340699726284245004973)
            ·
              refine ⟨33665002762397356591876865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89773340699726284245004973 33665002762397356591876865)
              ·
                refine ⟨25248752071798017443907649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33665002762397356591876865 25248752071798017443907649)
                ·
                  refine ⟨18936564053848513082930737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25248752071798017443907649 18936564053848513082930737)
                  ·
                    refine ⟨14202423040386384812198053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18936564053848513082930737 14202423040386384812198053)
                    ·
                      refine ⟨2662954320072447152287135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14202423040386384812198053 2662954320072447152287135)
                      ·
                        rfl

theorem cell23_5186085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_5186085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186085 prefixEnd_5186085 := by exact prefixLift 5186085
  have htrace : WordTrace (prefixWord ++ tailWord_5186085) baseStart_5186085 baseEnd_5186085 := by
    simpa [prefixWord, tailWord_5186085, baseEnd_5186085] using wordTrace_append hprefix tailTrace_5186085
  have hstable : (prefixWord ++ tailWord_5186085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186085).length < 2 ^ (prefixWord ++ tailWord_5186085).sum := by decide
  have hdescent : baseEnd_5186085 < baseStart_5186085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186100 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5186100 : Nat := 118140960795 + 5186100 * 2 ^ 59
def prefixEnd_5186100 : Nat := 4983230072969 + 3 ^ 40 * 5186100 * 2
def baseEnd_5186100 : Nat := 2662962022282264593599567

theorem tailTrace_5186100 : CollatzResearch.WordTrace tailWord_5186100 prefixEnd_5186100 2662962022282264593599567 := by
  unfold tailWord_5186100
  simp only [CollatzResearch.WordTrace]
  refine ⟨94576303255826445104853877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126101737674435260139805169 94576303255826445104853877)
  ·
    refine ⟨8866528430233729228580051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94576303255826445104853877 8866528430233729228580051)
    ·
      refine ⟨13299792645350593842870077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8866528430233729228580051 13299792645350593842870077)
      ·
        refine ⟨4987422242006472691076279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13299792645350593842870077 4987422242006472691076279)
        ·
          refine ⟨7481133363009709036614419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4987422242006472691076279 7481133363009709036614419)
          ·
            refine ⟨11221700044514563554921629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7481133363009709036614419 11221700044514563554921629)
            ·
              refine ⟨4208137516692961333095611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11221700044514563554921629 4208137516692961333095611)
              ·
                refine ⟨6312206275039441999643417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208137516692961333095611 6312206275039441999643417)
                ·
                  refine ⟨4734154706279581499732563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312206275039441999643417 4734154706279581499732563)
                  ·
                    refine ⟨7101232059419372249598845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4734154706279581499732563 7101232059419372249598845)
                    ·
                      refine ⟨2662962022282264593599567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7101232059419372249598845 2662962022282264593599567)
                      ·
                        rfl

theorem cell23_5186100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5186100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186100 prefixEnd_5186100 := by exact prefixLift 5186100
  have htrace : WordTrace (prefixWord ++ tailWord_5186100) baseStart_5186100 baseEnd_5186100 := by
    simpa [prefixWord, tailWord_5186100, baseEnd_5186100] using wordTrace_append hprefix tailTrace_5186100
  have hstable : (prefixWord ++ tailWord_5186100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186100).length < 2 ^ (prefixWord ++ tailWord_5186100).sum := by decide
  have hdescent : baseEnd_5186100 < baseStart_5186100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186129 : List Nat := [1, 2, 2, 1, 3, 5, 1, 3, 5]
def baseStart_5186129 : Nat := 118140960795 + 5186129 * 2 ^ 59
def prefixEnd_5186129 : Nat := 4983230072969 + 3 ^ 40 * 5186129 * 2
def baseEnd_5186129 : Nat := 295886323691249442237437

theorem tailTrace_5186129 : CollatzResearch.WordTrace tailWord_5186129 prefixEnd_5186129 295886323691249442237437 := by
  unfold tailWord_5186129
  simp only [CollatzResearch.WordTrace]
  refine ⟨189153664228547828162513441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126102442819031885441675627 189153664228547828162513441)
  ·
    refine ⟨141865248171410871121885081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189153664228547828162513441 141865248171410871121885081)
    ·
      refine ⟨106398936128558153341413811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141865248171410871121885081 106398936128558153341413811)
      ·
        refine ⟨159598404192837230012120717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106398936128558153341413811 159598404192837230012120717)
        ·
          refine ⟨59849401572313961254545269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159598404192837230012120717 59849401572313961254545269)
          ·
            refine ⟨5610881397404433867613619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59849401572313961254545269 5610881397404433867613619)
            ·
              refine ⟨8416322096106650801420429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610881397404433867613619 8416322096106650801420429)
              ·
                refine ⟨3156120786039994050532661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8416322096106650801420429 3156120786039994050532661)
                ·
                  refine ⟨295886323691249442237437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3156120786039994050532661 295886323691249442237437)
                  ·
                    rfl

theorem cell23_5186129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 5].length) (baseStart_5186129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186129 prefixEnd_5186129 := by exact prefixLift 5186129
  have htrace : WordTrace (prefixWord ++ tailWord_5186129) baseStart_5186129 baseEnd_5186129 := by
    simpa [prefixWord, tailWord_5186129, baseEnd_5186129] using wordTrace_append hprefix tailTrace_5186129
  have hstable : (prefixWord ++ tailWord_5186129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186129).length < 2 ^ (prefixWord ++ tailWord_5186129).sum := by decide
  have hdescent : baseEnd_5186129 < baseStart_5186129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186135 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_5186135 : Nat := 118140960795 + 5186135 * 2 ^ 59
def prefixEnd_5186135 : Nat := 4983230072969 + 3 ^ 40 * 5186135 * 2
def baseEnd_5186135 : Nat := 2662979994105171956661905

theorem tailTrace_5186135 : CollatzResearch.WordTrace tailWord_5186135 prefixEnd_5186135 2662979994105171956661905 := by
  unfold tailWord_5186135
  simp only [CollatzResearch.WordTrace]
  refine ⟨189153883066526091187231859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126102588711017394124821239 189153883066526091187231859)
  ·
    refine ⟨283730824599789136780847789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189153883066526091187231859 283730824599789136780847789)
    ·
      refine ⟨106399059224920926292817921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283730824599789136780847789 106399059224920926292817921)
      ·
        refine ⟨79799294418690694719613441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106399059224920926292817921 79799294418690694719613441)
        ·
          refine ⟨59849470814018021039710081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79799294418690694719613441 59849470814018021039710081)
          ·
            refine ⟨44887103110513515779782561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59849470814018021039710081 44887103110513515779782561)
            ·
              refine ⟨33665327332885136834836921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44887103110513515779782561 33665327332885136834836921)
              ·
                refine ⟨25248995499663852626127691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33665327332885136834836921 25248995499663852626127691)
                ·
                  refine ⟨37873493249495778939191537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25248995499663852626127691 37873493249495778939191537)
                  ·
                    refine ⟨28405119937121834204393653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37873493249495778939191537 28405119937121834204393653)
                    ·
                      refine ⟨2662979994105171956661905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28405119937121834204393653 2662979994105171956661905)
                      ·
                        rfl

theorem cell23_5186135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_5186135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186135 prefixEnd_5186135 := by exact prefixLift 5186135
  have htrace : WordTrace (prefixWord ++ tailWord_5186135) baseStart_5186135 baseEnd_5186135 := by
    simpa [prefixWord, tailWord_5186135, baseEnd_5186135] using wordTrace_append hprefix tailTrace_5186135
  have hstable : (prefixWord ++ tailWord_5186135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186135).length < 2 ^ (prefixWord ++ tailWord_5186135).sum := by decide
  have hdescent : baseEnd_5186135 < baseStart_5186135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186146 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 7]
def baseStart_5186146 : Nat := 118140960795 + 5186146 * 2 ^ 59
def prefixEnd_5186146 : Nat := 4983230072969 + 3 ^ 40 * 5186146 * 2
def baseEnd_5186146 : Nat := 295887293599152379291595

theorem tailTrace_5186146 : CollatzResearch.WordTrace tailWord_5186146 prefixEnd_5186146 295887293599152379291595 := by
  unfold tailWord_5186146
  simp only [CollatzResearch.WordTrace]
  refine ⟨47288571067371560016470573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126102856179657493377254861 47288571067371560016470573)
  ·
    refine ⟨17733214150264335006176465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47288571067371560016470573 17733214150264335006176465)
    ·
      refine ⟨13299910612698251254632349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17733214150264335006176465 13299910612698251254632349)
      ·
        refine ⟨4987466479761844220487131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13299910612698251254632349 4987466479761844220487131)
        ·
          refine ⟨7481199719642766330730697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4987466479761844220487131 7481199719642766330730697)
          ·
            refine ⟨5610899789732074748048023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7481199719642766330730697 5610899789732074748048023)
            ·
              refine ⟨8416349684598112122072035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610899789732074748048023 8416349684598112122072035)
              ·
                refine ⟨12624524526897168183108053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416349684598112122072035 12624524526897168183108053)
                ·
                  refine ⟨295887293599152379291595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12624524526897168183108053 295887293599152379291595)
                  ·
                    rfl

theorem cell23_5186146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_5186146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186146 prefixEnd_5186146 := by exact prefixLift 5186146
  have htrace : WordTrace (prefixWord ++ tailWord_5186146) baseStart_5186146 baseEnd_5186146 := by
    simpa [prefixWord, tailWord_5186146, baseEnd_5186146] using wordTrace_append hprefix tailTrace_5186146
  have hstable : (prefixWord ++ tailWord_5186146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186146).length < 2 ^ (prefixWord ++ tailWord_5186146).sum := by decide
  have hdescent : baseEnd_5186146 < baseStart_5186146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186172 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_5186172 : Nat := 118140960795 + 5186172 * 2 ^ 59
def prefixEnd_5186172 : Nat := 4983230072969 + 3 ^ 40 * 5186172 * 2
def baseEnd_5186172 : Nat := 887666330963129437299745

theorem tailTrace_5186172 : CollatzResearch.WordTrace tailWord_5186172 prefixEnd_5186172 887666330963129437299745 := by
  unfold tailWord_5186172
  simp only [CollatzResearch.WordTrace]
  refine ⟨94577616283696023253164385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126103488378261364337552513 94577616283696023253164385)
  ·
    refine ⟨70933212212772017439873289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94577616283696023253164385 70933212212772017439873289)
    ·
      refine ⟨53199909159579013079904967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70933212212772017439873289 53199909159579013079904967)
      ·
        refine ⟨79799863739368519619857451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53199909159579013079904967 79799863739368519619857451)
        ·
          refine ⟨119699795609052779429786177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79799863739368519619857451 119699795609052779429786177)
          ·
            refine ⟨89774846706789584572339633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119699795609052779429786177 89774846706789584572339633)
            ·
              refine ⟨67331135030092188429254725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89774846706789584572339633 67331135030092188429254725)
              ·
                refine ⟨12624587818142285330485261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67331135030092188429254725 12624587818142285330485261)
                ·
                  refine ⟨4734220431803356998931973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12624587818142285330485261 4734220431803356998931973)
                  ·
                    refine ⟨887666330963129437299745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734220431803356998931973 887666330963129437299745)
                    ·
                      rfl

theorem cell23_5186172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_5186172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186172 prefixEnd_5186172 := by exact prefixLift 5186172
  have htrace : WordTrace (prefixWord ++ tailWord_5186172) baseStart_5186172 baseEnd_5186172 := by
    simpa [prefixWord, tailWord_5186172, baseEnd_5186172] using wordTrace_append hprefix tailTrace_5186172
  have hstable : (prefixWord ++ tailWord_5186172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186172).length < 2 ^ (prefixWord ++ tailWord_5186172).sum := by decide
  have hdescent : baseEnd_5186172 < baseStart_5186172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186230 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_5186230 : Nat := 118140960795 + 5186230 * 2 ^ 59
def prefixEnd_5186230 : Nat := 4983230072969 + 3 ^ 40 * 5186230 * 2
def baseEnd_5186230 : Nat := 2663028774767349084973969

theorem tailTrace_5186230 : CollatzResearch.WordTrace tailWord_5186230 prefixEnd_5186230 2663028774767349084973969 := by
  unfold tailWord_5186230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11822334250073870150746259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126104898667454614941293429 11822334250073870150746259)
  ·
    refine ⟨17733501375110805226119389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11822334250073870150746259 17733501375110805226119389)
    ·
      refine ⟨6650063015666551959794771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17733501375110805226119389 6650063015666551959794771)
      ·
        refine ⟨9975094523499827939692157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650063015666551959794771 9975094523499827939692157)
        ·
          refine ⟨3740660446312435477384559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9975094523499827939692157 3740660446312435477384559)
          ·
            refine ⟨5610990669468653216076839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740660446312435477384559 5610990669468653216076839)
            ·
              refine ⟨8416486004202979824115259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5610990669468653216076839 8416486004202979824115259)
              ·
                refine ⟨12624729006304469736172889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416486004202979824115259 12624729006304469736172889)
                ·
                  refine ⟨9468546754728352302129667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12624729006304469736172889 9468546754728352302129667)
                  ·
                    refine ⟨14202820132092528453194501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9468546754728352302129667 14202820132092528453194501)
                    ·
                      refine ⟨2663028774767349084973969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14202820132092528453194501 2663028774767349084973969)
                      ·
                        rfl

theorem cell23_5186230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_5186230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186230 prefixEnd_5186230 := by exact prefixLift 5186230
  have htrace : WordTrace (prefixWord ++ tailWord_5186230) baseStart_5186230 baseEnd_5186230 := by
    simpa [prefixWord, tailWord_5186230, baseEnd_5186230] using wordTrace_append hprefix tailTrace_5186230
  have hstable : (prefixWord ++ tailWord_5186230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186230).length < 2 ^ (prefixWord ++ tailWord_5186230).sum := by decide
  have hdescent : baseEnd_5186230 < baseStart_5186230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186239 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 1, 5, 2]
def baseStart_5186239 : Nat := 118140960795 + 5186239 * 2 ^ 59
def prefixEnd_5186239 : Nat := 4983230072969 + 3 ^ 40 * 5186239 * 2
def baseEnd_5186239 : Nat := 2663033396093239549761427

theorem tailTrace_5186239 : CollatzResearch.WordTrace tailWord_5186239 prefixEnd_5186239 2663033396093239549761427 := by
  unfold tailWord_5186239
  simp only [CollatzResearch.WordTrace]
  refine ⟨189157676258149316949017771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126105117505432877966011847 189157676258149316949017771)
  ·
    refine ⟨283736514387223975423526657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189157676258149316949017771 283736514387223975423526657)
    ·
      refine ⟨212802385790417981567644993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283736514387223975423526657 212802385790417981567644993)
      ·
        refine ⟨159601789342813486175733745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212802385790417981567644993 159601789342813486175733745)
        ·
          refine ⟨119701342007110114631800309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159601789342813486175733745 119701342007110114631800309)
          ·
            refine ⟨11222000813166573246731279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119701342007110114631800309 11222000813166573246731279)
            ·
              refine ⟨16833001219749859870096919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11222000813166573246731279 16833001219749859870096919)
              ·
                refine ⟨25249501829624789805145379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16833001219749859870096919 25249501829624789805145379)
                ·
                  refine ⟨37874252744437184707718069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25249501829624789805145379 37874252744437184707718069)
                  ·
                    refine ⟨3550711194790986066348569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37874252744437184707718069 3550711194790986066348569)
                    ·
                      refine ⟨2663033396093239549761427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550711194790986066348569 2663033396093239549761427)
                      ·
                        rfl

theorem cell23_5186239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_5186239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186239 prefixEnd_5186239 := by exact prefixLift 5186239
  have htrace : WordTrace (prefixWord ++ tailWord_5186239) baseStart_5186239 baseEnd_5186239 := by
    simpa [prefixWord, tailWord_5186239, baseEnd_5186239] using wordTrace_append hprefix tailTrace_5186239
  have hstable : (prefixWord ++ tailWord_5186239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186239).length < 2 ^ (prefixWord ++ tailWord_5186239).sum := by decide
  have hdescent : baseEnd_5186239 < baseStart_5186239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186253 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 6]
def baseStart_5186253 : Nat := 118140960795 + 5186253 * 2 ^ 59
def prefixEnd_5186253 : Nat := 4983230072969 + 3 ^ 40 * 5186253 * 2
def baseEnd_5186253 : Nat := 295893398313600277220707

theorem tailTrace_5186253 : CollatzResearch.WordTrace tailWord_5186253 prefixEnd_5186253 295893398313600277220707 := by
  unfold tailWord_5186253
  simp only [CollatzResearch.WordTrace]
  refine ⟨189158186880098597340027413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126105457920065731560018275 189158186880098597340027413)
  ·
    refine ⟨8866790010004621750313785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 189158186880098597340027413 8866790010004621750313785)
    ·
      refine ⟨6650092507503466312735339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8866790010004621750313785 6650092507503466312735339)
      ·
        refine ⟨9975138761255199469103009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650092507503466312735339 9975138761255199469103009)
        ·
          refine ⟨7481354070941399601827257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9975138761255199469103009 7481354070941399601827257)
          ·
            refine ⟨5611015553206049701370443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7481354070941399601827257 5611015553206049701370443)
            ·
              refine ⟨8416523329809074552055665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5611015553206049701370443 8416523329809074552055665)
              ·
                refine ⟨6312392497356805914041749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8416523329809074552055665 6312392497356805914041749)
                ·
                  refine ⟨295893398313600277220707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6312392497356805914041749 295893398313600277220707)
                  ·
                    rfl

theorem cell23_5186253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_5186253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186253 prefixEnd_5186253 := by exact prefixLift 5186253
  have htrace : WordTrace (prefixWord ++ tailWord_5186253) baseStart_5186253 baseEnd_5186253 := by
    simpa [prefixWord, tailWord_5186253, baseEnd_5186253] using wordTrace_append hprefix tailTrace_5186253
  have hstable : (prefixWord ++ tailWord_5186253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186253).length < 2 ^ (prefixWord ++ tailWord_5186253).sum := by decide
  have hdescent : baseEnd_5186253 < baseStart_5186253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186286 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_5186286 : Nat := 118140960795 + 5186286 * 2 ^ 59
def prefixEnd_5186286 : Nat := 4983230072969 + 3 ^ 40 * 5186286 * 2
def baseEnd_5186286 : Nat := 2663057529684000865873711

theorem tailTrace_5186286 : CollatzResearch.WordTrace tailWord_5186286 prefixEnd_5186286 2663057529684000865873711 := by
  unfold tailWord_5186286
  simp only [CollatzResearch.WordTrace]
  refine ⟨23644923811122380496997339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126106260325986029317319141 23644923811122380496997339)
  ·
    refine ⟨35467385716683570745496009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23644923811122380496997339 35467385716683570745496009)
    ·
      refine ⟨26600539287512678059122007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35467385716683570745496009 26600539287512678059122007)
      ·
        refine ⟨39900808931269017088683011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26600539287512678059122007 39900808931269017088683011)
        ·
          refine ⟨59851213396903525633024517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39900808931269017088683011 59851213396903525633024517)
          ·
            refine ⟨11222102511919411056192097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59851213396903525633024517 11222102511919411056192097)
            ·
              refine ⟨8416576883939558292144073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11222102511919411056192097 8416576883939558292144073)
              ·
                refine ⟨6312432662954668719108055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8416576883939558292144073 6312432662954668719108055)
                ·
                  refine ⟨9468648994432003078662083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6312432662954668719108055 9468648994432003078662083)
                  ·
                    refine ⟨14202973491648004617993125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9468648994432003078662083 14202973491648004617993125)
                    ·
                      refine ⟨2663057529684000865873711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14202973491648004617993125 2663057529684000865873711)
                      ·
                        rfl

theorem cell23_5186286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_5186286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186286 prefixEnd_5186286 := by exact prefixLift 5186286
  have htrace : WordTrace (prefixWord ++ tailWord_5186286) baseStart_5186286 baseEnd_5186286 := by
    simpa [prefixWord, tailWord_5186286, baseEnd_5186286] using wordTrace_append hprefix tailTrace_5186286
  have hstable : (prefixWord ++ tailWord_5186286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186286).length < 2 ^ (prefixWord ++ tailWord_5186286).sum := by decide
  have hdescent : baseEnd_5186286 < baseStart_5186286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186306 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_5186306 : Nat := 118140960795 + 5186306 * 2 ^ 59
def prefixEnd_5186306 : Nat := 4983230072969 + 3 ^ 40 * 5186306 * 2
def baseEnd_5186306 : Nat := 2663067799297090787623619

theorem tailTrace_5186306 : CollatzResearch.WordTrace tailWord_5186306 prefixEnd_5186306 2663067799297090787623619 := by
  unfold tailWord_5186306
  simp only [CollatzResearch.WordTrace]
  refine ⟨47290029987226646847926693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126106746632604391594471181 47290029987226646847926693)
  ·
    refine ⟨8866880622604996283986255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47290029987226646847926693 8866880622604996283986255)
    ·
      refine ⟨13300320933907494425979383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8866880622604996283986255 13300320933907494425979383)
      ·
        refine ⟨19950481400861241638969075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13300320933907494425979383 19950481400861241638969075)
        ·
          refine ⟨29925722101291862458453613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19950481400861241638969075 29925722101291862458453613)
          ·
            refine ⟨11222145787984448421920105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29925722101291862458453613 11222145787984448421920105)
            ·
              refine ⟨8416609340988336316440079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11222145787984448421920105 8416609340988336316440079)
              ·
                refine ⟨12624914011482504474660119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8416609340988336316440079 12624914011482504474660119)
                ·
                  refine ⟨18937371017223756711990179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12624914011482504474660119 18937371017223756711990179)
                  ·
                    refine ⟨28406056525835635067985269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18937371017223756711990179 28406056525835635067985269)
                    ·
                      refine ⟨2663067799297090787623619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28406056525835635067985269 2663067799297090787623619)
                      ·
                        rfl

theorem cell23_5186306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_5186306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186306 prefixEnd_5186306 := by exact prefixLift 5186306
  have htrace : WordTrace (prefixWord ++ tailWord_5186306) baseStart_5186306 baseEnd_5186306 := by
    simpa [prefixWord, tailWord_5186306, baseEnd_5186306] using wordTrace_append hprefix tailTrace_5186306
  have hstable : (prefixWord ++ tailWord_5186306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186306).length < 2 ^ (prefixWord ++ tailWord_5186306).sum := by decide
  have hdescent : baseEnd_5186306 < baseStart_5186306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186319 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 3]
def baseStart_5186319 : Nat := 118140960795 + 5186319 * 2 ^ 59
def prefixEnd_5186319 : Nat := 4983230072969 + 3 ^ 40 * 5186319 * 2
def baseEnd_5186319 : Nat := 2663074474545599236761059

theorem tailTrace_5186319 : CollatzResearch.WordTrace tailWord_5186319 prefixEnd_5186319 2663074474545599236761059 := by
  unfold tailWord_5186319
  simp only [CollatzResearch.WordTrace]
  refine ⟨189160594097859490611930011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126107062731906327074620007 189160594097859490611930011)
  ·
    refine ⟨283740891146789235917895017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189160594097859490611930011 283740891146789235917895017)
    ·
      refine ⟨212805668360091926938421263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283740891146789235917895017 212805668360091926938421263)
      ·
        refine ⟨319208502540137890407631895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212805668360091926938421263 319208502540137890407631895)
        ·
          refine ⟨478812753810206835611447843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319208502540137890407631895 478812753810206835611447843)
          ·
            refine ⟨718219130715310253417171765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478812753810206835611447843 718219130715310253417171765)
            ·
              refine ⟨67333043504560336257859853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 718219130715310253417171765 67333043504560336257859853)
              ·
                refine ⟨25249891314210126096697445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67333043504560336257859853 25249891314210126096697445)
                ·
                  refine ⟨4734354621414398643130771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25249891314210126096697445 4734354621414398643130771)
                  ·
                    refine ⟨7101531932121597964696157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4734354621414398643130771 7101531932121597964696157)
                    ·
                      refine ⟨2663074474545599236761059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7101531932121597964696157 2663074474545599236761059)
                      ·
                        rfl

theorem cell23_5186319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 3].length) (baseStart_5186319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186319 prefixEnd_5186319 := by exact prefixLift 5186319
  have htrace : WordTrace (prefixWord ++ tailWord_5186319) baseStart_5186319 baseEnd_5186319 := by
    simpa [prefixWord, tailWord_5186319, baseEnd_5186319] using wordTrace_append hprefix tailTrace_5186319
  have hstable : (prefixWord ++ tailWord_5186319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186319).length < 2 ^ (prefixWord ++ tailWord_5186319).sum := by decide
  have hdescent : baseEnd_5186319 < baseStart_5186319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186340 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_5186340 : Nat := 118140960795 + 5186340 * 2 ^ 59
def prefixEnd_5186340 : Nat := 4983230072969 + 3 ^ 40 * 5186340 * 2
def baseEnd_5186340 : Nat := 2663085257639343654598463

theorem tailTrace_5186340 : CollatzResearch.WordTrace tailWord_5186340 prefixEnd_5186340 2663085257639343654598463 := by
  unfold tailWord_5186340
  simp only [CollatzResearch.WordTrace]
  refine ⟨94580680015391705599222237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126107573353855607465629649 94580680015391705599222237)
  ·
    refine ⟨35467755005771889599708339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94580680015391705599222237 35467755005771889599708339)
    ·
      refine ⟨53201632508657834399562509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35467755005771889599708339 53201632508657834399562509)
      ·
        refine ⟨19950612190746687899835941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53201632508657834399562509 19950612190746687899835941)
        ·
          refine ⟨3740739785765003981219239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19950612190746687899835941 3740739785765003981219239)
          ·
            refine ⟨5611109678647505971828859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740739785765003981219239 5611109678647505971828859)
            ·
              refine ⟨8416664517971258957743289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5611109678647505971828859 8416664517971258957743289)
              ·
                refine ⟨6312498388478444218307467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8416664517971258957743289 6312498388478444218307467)
                ·
                  refine ⟨9468747582717666327461201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6312498388478444218307467 9468747582717666327461201)
                  ·
                    refine ⟨7101560687038249745595901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9468747582717666327461201 7101560687038249745595901)
                    ·
                      refine ⟨2663085257639343654598463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7101560687038249745595901 2663085257639343654598463)
                      ·
                        rfl

theorem cell23_5186340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_5186340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186340 prefixEnd_5186340 := by exact prefixLift 5186340
  have htrace : WordTrace (prefixWord ++ tailWord_5186340) baseStart_5186340 baseEnd_5186340 := by
    simpa [prefixWord, tailWord_5186340, baseEnd_5186340] using wordTrace_append hprefix tailTrace_5186340
  have hstable : (prefixWord ++ tailWord_5186340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186340).length < 2 ^ (prefixWord ++ tailWord_5186340).sum := by decide
  have hdescent : baseEnd_5186340 < baseStart_5186340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186382 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_5186382 : Nat := 118140960795 + 5186382 * 2 ^ 59
def prefixEnd_5186382 : Nat := 4983230072969 + 3 ^ 40 * 5186382 * 2
def baseEnd_5186382 : Nat := 295900758202981387808141

theorem tailTrace_5186382 : CollatzResearch.WordTrace tailWord_5186382 prefixEnd_5186382 295900758202981387808141 := by
  unfold tailWord_5186382
  simp only [CollatzResearch.WordTrace]
  refine ⟨23645361487078906546434175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126108594597754168247648933 23645361487078906546434175)
  ·
    refine ⟨35468042230618359819651263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23645361487078906546434175 35468042230618359819651263)
    ·
      refine ⟨53202063345927539729476895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35468042230618359819651263 53202063345927539729476895)
      ·
        refine ⟨79803095018891309594215343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53202063345927539729476895 79803095018891309594215343)
        ·
          refine ⟨119704642528336964391323015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79803095018891309594215343 119704642528336964391323015)
          ·
            refine ⟨179556963792505446586984523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119704642528336964391323015 179556963792505446586984523)
            ·
              refine ⟨269335445688758169880476785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179556963792505446586984523 269335445688758169880476785)
              ·
                refine ⟨202001584266568627410357589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269335445688758169880476785 202001584266568627410357589)
                ·
                  refine ⟨295900758202981387808141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 202001584266568627410357589 295900758202981387808141)
                  ·
                    rfl

theorem cell23_5186382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_5186382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186382 prefixEnd_5186382 := by exact prefixLift 5186382
  have htrace : WordTrace (prefixWord ++ tailWord_5186382) baseStart_5186382 baseEnd_5186382 := by
    simpa [prefixWord, tailWord_5186382, baseEnd_5186382] using wordTrace_append hprefix tailTrace_5186382
  have hstable : (prefixWord ++ tailWord_5186382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186382).length < 2 ^ (prefixWord ++ tailWord_5186382).sum := by decide
  have hdescent : baseEnd_5186382 < baseStart_5186382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186389 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_5186389 : Nat := 118140960795 + 5186389 * 2 ^ 59
def prefixEnd_5186389 : Nat := 4983230072969 + 3 ^ 40 * 5186389 * 2
def baseEnd_5186389 : Nat := 2663110418191413962885737

theorem tailTrace_5186389 : CollatzResearch.WordTrace tailWord_5186389 prefixEnd_5186389 2663110418191413962885737 := by
  unfold tailWord_5186389
  simp only [CollatzResearch.WordTrace]
  refine ⟨189163147207605892566978221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126108764805070595044652147 189163147207605892566978221)
  ·
    refine ⟨70936180202852209712616833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189163147207605892566978221 70936180202852209712616833)
    ·
      refine ⟨53202135152139157284462625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70936180202852209712616833 53202135152139157284462625)
      ·
        refine ⟨39901601364104367963346969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53202135152139157284462625 39901601364104367963346969)
        ·
          refine ⟨29926201023078275972510227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39901601364104367963346969 29926201023078275972510227)
          ·
            refine ⟨44889301534617413958765341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29926201023078275972510227 44889301534617413958765341)
            ·
              refine ⟨16833488075481530234537003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44889301534617413958765341 16833488075481530234537003)
              ·
                refine ⟨25250232113222295351805505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16833488075481530234537003 25250232113222295351805505)
                ·
                  refine ⟨18937674084916721513854129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25250232113222295351805505 18937674084916721513854129)
                  ·
                    refine ⟨14203255563687541135390597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18937674084916721513854129 14203255563687541135390597)
                    ·
                      refine ⟨2663110418191413962885737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14203255563687541135390597 2663110418191413962885737)
                      ·
                        rfl

theorem cell23_5186389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_5186389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186389 prefixEnd_5186389 := by exact prefixLift 5186389
  have htrace : WordTrace (prefixWord ++ tailWord_5186389) baseStart_5186389 baseEnd_5186389 := by
    simpa [prefixWord, tailWord_5186389, baseEnd_5186389] using wordTrace_append hprefix tailTrace_5186389
  have hstable : (prefixWord ++ tailWord_5186389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186389).length < 2 ^ (prefixWord ++ tailWord_5186389).sum := by decide
  have hdescent : baseEnd_5186389 < baseStart_5186389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186393 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 2, 2, 2]
def baseStart_5186393 : Nat := 118140960795 + 5186393 * 2 ^ 59
def prefixEnd_5186393 : Nat := 4983230072969 + 3 ^ 40 * 5186393 * 2
def baseEnd_5186393 : Nat := 2663112472114031947235719

theorem tailTrace_5186393 : CollatzResearch.WordTrace tailWord_5186393 prefixEnd_5186393 2663112472114031947235719 := by
  unfold tailWord_5186393
  simp only [CollatzResearch.WordTrace]
  refine ⟨189163293099591401250123833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126108862066394267500082555 189163293099591401250123833)
  ·
    refine ⟨141872469824693550937592875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189163293099591401250123833 141872469824693550937592875)
    ·
      refine ⟨212808704737040326406389313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141872469824693550937592875 212808704737040326406389313)
      ·
        refine ⟨159606528552780244804791985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212808704737040326406389313 159606528552780244804791985)
        ·
          refine ⟨119704896414585183603593989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159606528552780244804791985 119704896414585183603593989)
          ·
            refine ⟨22444668077734721925673873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119704896414585183603593989 22444668077734721925673873)
            ·
              refine ⟨16833501058301041444255405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22444668077734721925673873 16833501058301041444255405)
              ·
                refine ⟨6312562896862890541595777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16833501058301041444255405 6312562896862890541595777)
                ·
                  refine ⟨4734422172647167906196833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312562896862890541595777 4734422172647167906196833)
                  ·
                    refine ⟨3550816629485375929647625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4734422172647167906196833 3550816629485375929647625)
                    ·
                      refine ⟨2663112472114031947235719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550816629485375929647625 2663112472114031947235719)
                      ·
                        rfl

theorem cell23_5186393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_5186393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186393 prefixEnd_5186393 := by exact prefixLift 5186393
  have htrace : WordTrace (prefixWord ++ tailWord_5186393) baseStart_5186393 baseEnd_5186393 := by
    simpa [prefixWord, tailWord_5186393, baseEnd_5186393] using wordTrace_append hprefix tailTrace_5186393
  have hstable : (prefixWord ++ tailWord_5186393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186393).length < 2 ^ (prefixWord ++ tailWord_5186393).sum := by decide
  have hdescent : baseEnd_5186393 < baseStart_5186393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186414 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_5186414 : Nat := 118140960795 + 5186414 * 2 ^ 59
def prefixEnd_5186414 : Nat := 4983230072969 + 3 ^ 40 * 5186414 * 2
def baseEnd_5186414 : Nat := 2663123255207776365073123

theorem tailTrace_5186414 : CollatzResearch.WordTrace tailWord_5186414 prefixEnd_5186414 2663123255207776365073123 := by
  unfold tailWord_5186414
  simp only [CollatzResearch.WordTrace]
  refine ⟨23645507379064415229579787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126109372688343547891092197 23645507379064415229579787)
  ·
    refine ⟨35468261068596622844369681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23645507379064415229579787 35468261068596622844369681)
    ·
      refine ⟨26601195801447467133277261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35468261068596622844369681 26601195801447467133277261)
      ·
        refine ⟨9975448425542800174978973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26601195801447467133277261 9975448425542800174978973)
        ·
          refine ⟨3740793159578550065617115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9975448425542800174978973 3740793159578550065617115)
          ·
            refine ⟨5611189739367825098425673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740793159578550065617115 5611189739367825098425673)
            ·
              refine ⟨4208392304525868823819255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5611189739367825098425673 4208392304525868823819255)
              ·
                refine ⟨6312588456788803235728883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208392304525868823819255 6312588456788803235728883)
                ·
                  refine ⟨9468882685183204853593325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6312588456788803235728883 9468882685183204853593325)
                  ·
                    refine ⟨3550831006943701820097497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9468882685183204853593325 3550831006943701820097497)
                    ·
                      refine ⟨2663123255207776365073123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550831006943701820097497 2663123255207776365073123)
                      ·
                        rfl

theorem cell23_5186414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_5186414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186414 prefixEnd_5186414 := by exact prefixLift 5186414
  have htrace : WordTrace (prefixWord ++ tailWord_5186414) baseStart_5186414 baseEnd_5186414 := by
    simpa [prefixWord, tailWord_5186414, baseEnd_5186414] using wordTrace_append hprefix tailTrace_5186414
  have hstable : (prefixWord ++ tailWord_5186414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186414).length < 2 ^ (prefixWord ++ tailWord_5186414).sum := by decide
  have hdescent : baseEnd_5186414 < baseStart_5186414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186429 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_5186429 : Nat := 118140960795 + 5186429 * 2 ^ 59
def prefixEnd_5186429 : Nat := 4983230072969 + 3 ^ 40 * 5186429 * 2
def baseEnd_5186429 : Nat := 887710319139197935461851

theorem tailTrace_5186429 : CollatzResearch.WordTrace tailWord_5186429 prefixEnd_5186429 887710319139197935461851 := by
  unfold tailWord_5186429
  simp only [CollatzResearch.WordTrace]
  refine ⟨189164606127460979398434341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126109737418307319598956227 189164606127460979398434341)
  ·
    refine ⟨35468363648898933637206439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189164606127460979398434341 35468363648898933637206439)
    ·
      refine ⟨53202545473348400455809659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35468363648898933637206439 53202545473348400455809659)
      ·
        refine ⟨79803818210022600683714489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53202545473348400455809659 79803818210022600683714489)
        ·
          refine ⟨59852863657516950512785867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79803818210022600683714489 59852863657516950512785867)
          ·
            refine ⟨89779295486275425769178801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59852863657516950512785867 89779295486275425769178801)
            ·
              refine ⟨67334471614706569326884101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89779295486275425769178801 67334471614706569326884101)
              ·
                refine ⟨12625213427757481748790769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67334471614706569326884101 12625213427757481748790769)
                ·
                  refine ⟨9468910070818111311593077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12625213427757481748790769 9468910070818111311593077)
                  ·
                    refine ⟨887710319139197935461851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9468910070818111311593077 887710319139197935461851)
                    ·
                      rfl

theorem cell23_5186429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_5186429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186429 prefixEnd_5186429 := by exact prefixLift 5186429
  have htrace : WordTrace (prefixWord ++ tailWord_5186429) baseStart_5186429 baseEnd_5186429 := by
    simpa [prefixWord, tailWord_5186429, baseEnd_5186429] using wordTrace_append hprefix tailTrace_5186429
  have hstable : (prefixWord ++ tailWord_5186429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186429).length < 2 ^ (prefixWord ++ tailWord_5186429).sum := by decide
  have hdescent : baseEnd_5186429 < baseStart_5186429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186466 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_5186466 : Nat := 118140960795 + 5186466 * 2 ^ 59
def prefixEnd_5186466 : Nat := 4983230072969 + 3 ^ 40 * 5186466 * 2
def baseEnd_5186466 : Nat := 2663149956201810161622883

theorem tailTrace_5186466 : CollatzResearch.WordTrace tailWord_5186466 prefixEnd_5186466 2663149956201810161622883 := by
  unfold tailWord_5186466
  simp only [CollatzResearch.WordTrace]
  refine ⟨47291488907081733679382813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126110637085551289811687501 47291488907081733679382813)
  ·
    refine ⟨17734308340155650129768555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47291488907081733679382813 17734308340155650129768555)
    ·
      refine ⟨26601462510233475194652833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17734308340155650129768555 26601462510233475194652833)
      ·
        refine ⟨19951096882675106395989625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26601462510233475194652833 19951096882675106395989625)
        ·
          refine ⟨14963322662006329796992219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19951096882675106395989625 14963322662006329796992219)
          ·
            refine ⟨22444983993009494695488329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14963322662006329796992219 22444983993009494695488329)
            ·
              refine ⟨16833737994757121021616247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22444983993009494695488329 16833737994757121021616247)
              ·
                refine ⟨25250606992135681532424371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16833737994757121021616247 25250606992135681532424371)
                ·
                  refine ⟨37875910488203522298636557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25250606992135681532424371 37875910488203522298636557)
                  ·
                    refine ⟨14203466433076320861988709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37875910488203522298636557 14203466433076320861988709)
                    ·
                      refine ⟨2663149956201810161622883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14203466433076320861988709 2663149956201810161622883)
                      ·
                        rfl

theorem cell23_5186466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_5186466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186466 prefixEnd_5186466 := by exact prefixLift 5186466
  have htrace : WordTrace (prefixWord ++ tailWord_5186466) baseStart_5186466 baseEnd_5186466 := by
    simpa [prefixWord, tailWord_5186466, baseEnd_5186466] using wordTrace_append hprefix tailTrace_5186466
  have hstable : (prefixWord ++ tailWord_5186466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186466).length < 2 ^ (prefixWord ++ tailWord_5186466).sum := by decide
  have hdescent : baseEnd_5186466 < baseStart_5186466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186489 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 8]
def baseStart_5186489 : Nat := 118140960795 + 5186489 * 2 ^ 59
def prefixEnd_5186489 : Nat := 4983230072969 + 3 ^ 40 * 5186489 * 2
def baseEnd_5186489 : Nat := 295906862917429285737253

theorem tailTrace_5186489 : CollatzResearch.WordTrace tailWord_5186489 prefixEnd_5186489 295906862917429285737253 := by
  unfold tailWord_5186489
  simp only [CollatzResearch.WordTrace]
  refine ⟨189166794507243609645618521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126111196338162406430412347 189166794507243609645618521)
  ·
    refine ⟨141875095880432707234213891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189166794507243609645618521 141875095880432707234213891)
    ·
      refine ⟨212812643820649060851320837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141875095880432707234213891 212812643820649060851320837)
      ·
        refine ⟨39902370716371698909622657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212812643820649060851320837 39902370716371698909622657)
        ·
          refine ⟨29926778037278774182216993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39902370716371698909622657 29926778037278774182216993)
          ·
            refine ⟨22445083527959080636662745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29926778037278774182216993 22445083527959080636662745)
            ·
              refine ⟨16833812645969310477497059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22445083527959080636662745 16833812645969310477497059)
              ·
                refine ⟨25250718968953965716245589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16833812645969310477497059 25250718968953965716245589)
                ·
                  refine ⟨295906862917429285737253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25250718968953965716245589 295906862917429285737253)
                  ·
                    rfl

theorem cell23_5186489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 8].length) (baseStart_5186489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186489 prefixEnd_5186489 := by exact prefixLift 5186489
  have htrace : WordTrace (prefixWord ++ tailWord_5186489) baseStart_5186489 baseEnd_5186489 := by
    simpa [prefixWord, tailWord_5186489, baseEnd_5186489] using wordTrace_append hprefix tailTrace_5186489
  have hstable : (prefixWord ++ tailWord_5186489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186489).length < 2 ^ (prefixWord ++ tailWord_5186489).sum := by decide
  have hdescent : baseEnd_5186489 < baseStart_5186489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186536 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 1, 5]
def baseStart_5186536 : Nat := 118140960795 + 5186536 * 2 ^ 59
def prefixEnd_5186536 : Nat := 4983230072969 + 3 ^ 40 * 5186536 * 2
def baseEnd_5186536 : Nat := 887728633282541629249187

theorem tailTrace_5186536 : CollatzResearch.WordTrace tailWord_5186536 prefixEnd_5186536 887728633282541629249187 := by
  unfold tailWord_5186536
  simp only [CollatzResearch.WordTrace]
  refine ⟨94584254369036668336289731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126112339158715557781719641 94584254369036668336289731)
  ·
    refine ⟨141876381553555002504434597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94584254369036668336289731 141876381553555002504434597)
    ·
      refine ⟨26601821541291562969581487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141876381553555002504434597 26601821541291562969581487)
      ·
        refine ⟨39902732311937344454372231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26601821541291562969581487 39902732311937344454372231)
        ·
          refine ⟨59854098467906016681558347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39902732311937344454372231 59854098467906016681558347)
          ·
            refine ⟨89781147701859025022337521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59854098467906016681558347 89781147701859025022337521)
            ·
              refine ⟨67335860776394268766753141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89781147701859025022337521 67335860776394268766753141)
              ·
                refine ⟨6312736947786962696883107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67335860776394268766753141 6312736947786962696883107)
                ·
                  refine ⟨9469105421680444045324661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6312736947786962696883107 9469105421680444045324661)
                  ·
                    refine ⟨887728633282541629249187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9469105421680444045324661 887728633282541629249187)
                    ·
                      rfl

theorem cell23_5186536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_5186536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186536 prefixEnd_5186536 := by exact prefixLift 5186536
  have htrace : WordTrace (prefixWord ++ tailWord_5186536) baseStart_5186536 baseEnd_5186536 := by
    simpa [prefixWord, tailWord_5186536, baseEnd_5186536] using wordTrace_append hprefix tailTrace_5186536
  have hstable : (prefixWord ++ tailWord_5186536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186536).length < 2 ^ (prefixWord ++ tailWord_5186536).sum := by decide
  have hdescent : baseEnd_5186536 < baseStart_5186536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186543 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 2, 3, 2]
def baseStart_5186543 : Nat := 118140960795 + 5186543 * 2 ^ 59
def prefixEnd_5186543 : Nat := 4983230072969 + 3 ^ 40 * 5186543 * 2
def baseEnd_5186543 : Nat := 2663189494212206360360029

theorem tailTrace_5186543 : CollatzResearch.WordTrace tailWord_5186543 prefixEnd_5186543 2663189494212206360360029 := by
  unfold tailWord_5186543
  simp only [CollatzResearch.WordTrace]
  refine ⟨189168764049047976868084283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126112509366031984578722855 189168764049047976868084283)
  ·
    refine ⟨283753146073571965302126425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189168764049047976868084283 283753146073571965302126425)
    ·
      refine ⟨212814859555178973976594819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283753146073571965302126425 212814859555178973976594819)
      ·
        refine ⟨319222289332768460964892229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212814859555178973976594819 319222289332768460964892229)
        ·
          refine ⟨59854179249894086430917293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319222289332768460964892229 59854179249894086430917293)
          ·
            refine ⟨22445317218710282411593985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59854179249894086430917293 22445317218710282411593985)
            ·
              refine ⟨16833987914032711808695489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22445317218710282411593985 16833987914032711808695489)
              ·
                refine ⟨12625490935524533856521617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16833987914032711808695489 12625490935524533856521617)
                ·
                  refine ⟨9469118201643400392391213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12625490935524533856521617 9469118201643400392391213)
                  ·
                    refine ⟨3550919325616275147146705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9469118201643400392391213 3550919325616275147146705)
                    ·
                      refine ⟨2663189494212206360360029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3550919325616275147146705 2663189494212206360360029)
                      ·
                        rfl

theorem cell23_5186543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 3, 2].length) (baseStart_5186543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186543 prefixEnd_5186543 := by exact prefixLift 5186543
  have htrace : WordTrace (prefixWord ++ tailWord_5186543) baseStart_5186543 baseEnd_5186543 := by
    simpa [prefixWord, tailWord_5186543, baseEnd_5186543] using wordTrace_append hprefix tailTrace_5186543
  have hstable : (prefixWord ++ tailWord_5186543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186543).length < 2 ^ (prefixWord ++ tailWord_5186543).sum := by decide
  have hdescent : baseEnd_5186543 < baseStart_5186543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186556 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_5186556 : Nat := 118140960795 + 5186556 * 2 ^ 59
def prefixEnd_5186556 : Nat := 4983230072969 + 3 ^ 40 * 5186556 * 2
def baseEnd_5186556 : Nat := 2663196169460714809497469

theorem tailTrace_5186556 : CollatzResearch.WordTrace tailWord_5186556 prefixEnd_5186556 2663196169460714809497469 := by
  unfold tailWord_5186556
  simp only [CollatzResearch.WordTrace]
  refine ⟨94584619099000440044153761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126112825465333920058871681 94584619099000440044153761)
  ·
    refine ⟨70938464324250330033115321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94584619099000440044153761 70938464324250330033115321)
    ·
      refine ⟨53203848243187747524836491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70938464324250330033115321 53203848243187747524836491)
      ·
        refine ⟨79805772364781621287254737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53203848243187747524836491 79805772364781621287254737)
        ·
          refine ⟨59854329273586215965441053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79805772364781621287254737 59854329273586215965441053)
          ·
            refine ⟨22445373477594830987040395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59854329273586215965441053 22445373477594830987040395)
            ·
              refine ⟨33668060216392246480560593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22445373477594830987040395 33668060216392246480560593)
              ·
                refine ⟨25251045162294184860420445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33668060216392246480560593 25251045162294184860420445)
                ·
                  refine ⟨9469141935860319322657667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25251045162294184860420445 9469141935860319322657667)
                  ·
                    refine ⟨14203712903790478983986501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9469141935860319322657667 14203712903790478983986501)
                    ·
                      refine ⟨2663196169460714809497469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14203712903790478983986501 2663196169460714809497469)
                      ·
                        rfl

theorem cell23_5186556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_5186556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186556 prefixEnd_5186556 := by exact prefixLift 5186556
  have htrace : WordTrace (prefixWord ++ tailWord_5186556) baseStart_5186556 baseEnd_5186556 := by
    simpa [prefixWord, tailWord_5186556, baseEnd_5186556] using wordTrace_append hprefix tailTrace_5186556
  have hstable : (prefixWord ++ tailWord_5186556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186556).length < 2 ^ (prefixWord ++ tailWord_5186556).sum := by decide
  have hdescent : baseEnd_5186556 < baseStart_5186556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186569 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_5186569 : Nat := 118140960795 + 5186569 * 2 ^ 59
def prefixEnd_5186569 : Nat := 4983230072969 + 3 ^ 40 * 5186569 * 2
def baseEnd_5186569 : Nat := 2663202844709223258634909

theorem tailTrace_5186569 : CollatzResearch.WordTrace tailWord_5186569 prefixEnd_5186569 2663202844709223258634909 := by
  unfold tailWord_5186569
  simp only [CollatzResearch.WordTrace]
  refine ⟨189169712346953783308530761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126113141564635855539020507 189169712346953783308530761)
  ·
    refine ⟨141877284260215337481398071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189169712346953783308530761 141877284260215337481398071)
    ·
      refine ⟨212815926390323006222097107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141877284260215337481398071 212815926390323006222097107)
      ·
        refine ⟨319223889585484509333145661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212815926390323006222097107 319223889585484509333145661)
        ·
          refine ⟨119708958594556690999929623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319223889585484509333145661 119708958594556690999929623)
          ·
            refine ⟨179563437891835036499894435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119708958594556690999929623 179563437891835036499894435)
            ·
              refine ⟨269345156837752554749841653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179563437891835036499894435 269345156837752554749841653)
              ·
                refine ⟨25251108453539302007797655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 269345156837752554749841653 25251108453539302007797655)
                ·
                  refine ⟨37876662680308953011696483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25251108453539302007797655 37876662680308953011696483)
                  ·
                    refine ⟨56814994020463429517544725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37876662680308953011696483 56814994020463429517544725)
                    ·
                      refine ⟨2663202844709223258634909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56814994020463429517544725 2663202844709223258634909)
                      ·
                        rfl

theorem cell23_5186569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_5186569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186569 prefixEnd_5186569 := by exact prefixLift 5186569
  have htrace : WordTrace (prefixWord ++ tailWord_5186569) baseStart_5186569 baseEnd_5186569 := by
    simpa [prefixWord, tailWord_5186569, baseEnd_5186569] using wordTrace_append hprefix tailTrace_5186569
  have hstable : (prefixWord ++ tailWord_5186569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186569).length < 2 ^ (prefixWord ++ tailWord_5186569).sum := by decide
  have hdescent : baseEnd_5186569 < baseStart_5186569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186586 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_5186586 : Nat := 118140960795 + 5186586 * 2 ^ 59
def prefixEnd_5186586 : Nat := 4983230072969 + 3 ^ 40 * 5186586 * 2
def baseEnd_5186586 : Nat := 2663211573880349692122331

theorem tailTrace_5186586 : CollatzResearch.WordTrace tailWord_5186586 prefixEnd_5186586 2663211573880349692122331 := by
  unfold tailWord_5186586
  simp only [CollatzResearch.WordTrace]
  refine ⟨47292583096973048802974903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126113554925261463474599741 47292583096973048802974903)
  ·
    refine ⟨70938874645459573204462355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47292583096973048802974903 70938874645459573204462355)
    ·
      refine ⟨106408311968189359806693533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70938874645459573204462355 106408311968189359806693533)
      ·
        refine ⟨39903116988071009927510075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106408311968189359806693533 39903116988071009927510075)
        ·
          refine ⟨59854675482106514891265113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39903116988071009927510075 59854675482106514891265113)
          ·
            refine ⟨44891006611579886168448835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59854675482106514891265113 44891006611579886168448835)
            ·
              refine ⟨67336509917369829252673253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44891006611579886168448835 67336509917369829252673253)
              ·
                refine ⟨12625595609506842984876235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67336509917369829252673253 12625595609506842984876235)
                ·
                  refine ⟨18938393414260264477314353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12625595609506842984876235 18938393414260264477314353)
                  ·
                    refine ⟨14203795060695198357985765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18938393414260264477314353 14203795060695198357985765)
                    ·
                      refine ⟨2663211573880349692122331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14203795060695198357985765 2663211573880349692122331)
                      ·
                        rfl

theorem cell23_5186586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_5186586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186586 prefixEnd_5186586 := by exact prefixLift 5186586
  have htrace : WordTrace (prefixWord ++ tailWord_5186586) baseStart_5186586 baseEnd_5186586 := by
    simpa [prefixWord, tailWord_5186586, baseEnd_5186586] using wordTrace_append hprefix tailTrace_5186586
  have hstable : (prefixWord ++ tailWord_5186586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186586).length < 2 ^ (prefixWord ++ tailWord_5186586).sum := by decide
  have hdescent : baseEnd_5186586 < baseStart_5186586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186596 : List Nat := [2, 3, 1, 4, 1, 2, 10]
def baseStart_5186596 : Nat := 118140960795 + 5186596 * 2 ^ 59
def prefixEnd_5186596 : Nat := 4983230072969 + 3 ^ 40 * 5186596 * 2
def baseEnd_5186596 : Nat := 32879218625764131518485

theorem tailTrace_5186596 : CollatzResearch.WordTrace tailWord_5186596 prefixEnd_5186596 32879218625764131518485 := by
  unfold tailWord_5186596
  simp only [CollatzResearch.WordTrace]
  refine ⟨94585348558927983459881821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126113798078570644613175761 94585348558927983459881821)
  ·
    refine ⟨35469505709597993797455683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94585348558927983459881821 35469505709597993797455683)
    ·
      refine ⟨53204258564396990696183525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35469505709597993797455683 53204258564396990696183525)
      ·
        refine ⟨9975798480824435755534411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53204258564396990696183525 9975798480824435755534411)
        ·
          refine ⟨14963697721236653633301617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9975798480824435755534411 14963697721236653633301617)
          ·
            refine ⟨11222773290927490224976213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14963697721236653633301617 11222773290927490224976213)
            ·
              refine ⟨32879218625764131518485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11222773290927490224976213 32879218625764131518485)
              ·
                rfl

theorem cell23_5186596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 10].length) (baseStart_5186596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186596 prefixEnd_5186596 := by exact prefixLift 5186596
  have htrace : WordTrace (prefixWord ++ tailWord_5186596) baseStart_5186596 baseEnd_5186596 := by
    simpa [prefixWord, tailWord_5186596, baseEnd_5186596] using wordTrace_append hprefix tailTrace_5186596
  have hstable : (prefixWord ++ tailWord_5186596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186596).length < 2 ^ (prefixWord ++ tailWord_5186596).sum := by decide
  have hdescent : baseEnd_5186596 < baseStart_5186596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186619 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 5]
def baseStart_5186619 : Nat := 118140960795 + 5186619 * 2 ^ 59
def prefixEnd_5186619 : Nat := 4983230072969 + 3 ^ 40 * 5186619 * 2
def baseEnd_5186619 : Nat := 2663228518741948063009679

theorem tailTrace_5186619 : CollatzResearch.WordTrace tailWord_5186619 prefixEnd_5186619 2663228518741948063009679 := by
  unfold tailWord_5186619
  simp only [CollatzResearch.WordTrace]
  refine ⟨189171535996772641847850911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126114357331181761231900607 189171535996772641847850911)
  ·
    refine ⟨283757303995158962771776367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189171535996772641847850911 283757303995158962771776367)
    ·
      refine ⟨425635955992738444157664551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283757303995158962771776367 425635955992738444157664551)
      ·
        refine ⟨638453933989107666236496827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425635955992738444157664551 638453933989107666236496827)
        ·
          refine ⟨957680900983661499354745241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638453933989107666236496827 957680900983661499354745241)
          ·
            refine ⟨718260675737746124516058931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957680900983661499354745241 718260675737746124516058931)
            ·
              refine ⟨1077391013606619186774088397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718260675737746124516058931 1077391013606619186774088397)
              ·
                refine ⟨404021630102482195040283149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1077391013606619186774088397 404021630102482195040283149)
                ·
                  refine ⟨151508111288430823140106181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404021630102482195040283149 151508111288430823140106181)
                  ·
                    refine ⟨28407770866580779338769909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151508111288430823140106181 28407770866580779338769909)
                    ·
                      refine ⟨2663228518741948063009679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28407770866580779338769909 2663228518741948063009679)
                      ·
                        rfl

theorem cell23_5186619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_5186619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186619 prefixEnd_5186619 := by exact prefixLift 5186619
  have htrace : WordTrace (prefixWord ++ tailWord_5186619) baseStart_5186619 baseEnd_5186619 := by
    simpa [prefixWord, tailWord_5186619, baseEnd_5186619] using wordTrace_append hprefix tailTrace_5186619
  have hstable : (prefixWord ++ tailWord_5186619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186619).length < 2 ^ (prefixWord ++ tailWord_5186619).sum := by decide
  have hdescent : baseEnd_5186619 < baseStart_5186619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186630 : List Nat := [6, 1, 1, 1, 1, 2, 4, 7]
def baseStart_5186630 : Nat := 118140960795 + 5186630 * 2 ^ 59
def prefixEnd_5186630 : Nat := 4983230072969 + 3 ^ 40 * 5186630 * 2
def baseEnd_5186630 : Nat := 98638302482561019258227

theorem tailTrace_5186630 : CollatzResearch.WordTrace tailWord_5186630 prefixEnd_5186630 98638302482561019258227 := by
  unfold tailWord_5186630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911623037491649710203167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126114624799821860484334229 5911623037491649710203167)
  ·
    refine ⟨8867434556237474565304751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5911623037491649710203167 8867434556237474565304751)
    ·
      refine ⟨13301151834356211847957127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8867434556237474565304751 13301151834356211847957127)
      ·
        refine ⟨19951727751534317771935691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13301151834356211847957127 19951727751534317771935691)
        ·
          refine ⟨29927591627301476657903537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19951727751534317771935691 29927591627301476657903537)
          ·
            refine ⟨22445693720476107493427653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29927591627301476657903537 22445693720476107493427653)
            ·
              refine ⟨4208567572589270155017685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22445693720476107493427653 4208567572589270155017685)
              ·
                refine ⟨98638302482561019258227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4208567572589270155017685 98638302482561019258227)
                ·
                  rfl

theorem cell23_5186630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_5186630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186630 prefixEnd_5186630 := by exact prefixLift 5186630
  have htrace : WordTrace (prefixWord ++ tailWord_5186630) baseStart_5186630 baseEnd_5186630 := by
    simpa [prefixWord, tailWord_5186630, baseEnd_5186630] using wordTrace_append hprefix tailTrace_5186630
  have hstable : (prefixWord ++ tailWord_5186630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186630).length < 2 ^ (prefixWord ++ tailWord_5186630).sum := by decide
  have hdescent : baseEnd_5186630 < baseStart_5186630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186714 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2]
def baseStart_5186714 : Nat := 118140960795 + 5186714 * 2 ^ 59
def prefixEnd_5186714 : Nat := 4983230072969 + 3 ^ 40 * 5186714 * 2
def baseEnd_5186714 : Nat := 2663277299404125191321743

theorem tailTrace_5186714 : CollatzResearch.WordTrace tailWord_5186714 prefixEnd_5186714 2663277299404125191321743 := by
  unfold tailWord_5186714
  simp only [CollatzResearch.WordTrace]
  refine ⟨47293750232857118268139799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126116667287618982048372797 47293750232857118268139799)
  ·
    refine ⟨70940625349285677402209699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47293750232857118268139799 70940625349285677402209699)
    ·
      refine ⟨106410938023928516103314549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70940625349285677402209699 106410938023928516103314549)
      ·
        refine ⟨9976025439743298384685739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106410938023928516103314549 9976025439743298384685739)
        ·
          refine ⟨14964038159614947577028609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9976025439743298384685739 14964038159614947577028609)
          ·
            refine ⟨11223028619711210682771457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14964038159614947577028609 11223028619711210682771457)
            ·
              refine ⟨8417271464783408012078593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11223028619711210682771457 8417271464783408012078593)
              ·
                refine ⟨6312953598587556009058945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8417271464783408012078593 6312953598587556009058945)
                ·
                  refine ⟨4734715198940667006794209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6312953598587556009058945 4734715198940667006794209)
                  ·
                    refine ⟨3551036399205500255095657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4734715198940667006794209 3551036399205500255095657)
                    ·
                      refine ⟨2663277299404125191321743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551036399205500255095657 2663277299404125191321743)
                      ·
                        rfl

theorem cell23_5186714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_5186714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186714 prefixEnd_5186714 := by exact prefixLift 5186714
  have htrace : WordTrace (prefixWord ++ tailWord_5186714) baseStart_5186714 baseEnd_5186714 := by
    simpa [prefixWord, tailWord_5186714, baseEnd_5186714] using wordTrace_append hprefix tailTrace_5186714
  have hstable : (prefixWord ++ tailWord_5186714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186714).length < 2 ^ (prefixWord ++ tailWord_5186714).sum := by decide
  have hdescent : baseEnd_5186714 < baseStart_5186714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186730 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5186730 : Nat := 118140960795 + 5186730 * 2 ^ 59
def prefixEnd_5186730 : Nat := 4983230072969 + 3 ^ 40 * 5186730 * 2
def baseEnd_5186730 : Nat := 2663285515094597128721669

theorem tailTrace_5186730 : CollatzResearch.WordTrace tailWord_5186730 prefixEnd_5186730 2663285515094597128721669 := by
  unfold tailWord_5186730
  simp only [CollatzResearch.WordTrace]
  refine ⟨47293896124842626951285411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126117056332913671870094429 47293896124842626951285411)
  ·
    refine ⟨70940844187263940426928117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47293896124842626951285411 70940844187263940426928117)
    ·
      refine ⟨6650704142555994415024511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70940844187263940426928117 6650704142555994415024511)
      ·
        refine ⟨9976056213833991622536767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6650704142555994415024511 9976056213833991622536767)
        ·
          refine ⟨14964084320750987433805151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9976056213833991622536767 14964084320750987433805151)
          ·
            refine ⟨22446126481126481150707727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14964084320750987433805151 22446126481126481150707727)
            ·
              refine ⟨33669189721689721726061591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22446126481126481150707727 33669189721689721726061591)
              ·
                refine ⟨50503784582534582589092387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33669189721689721726061591 50503784582534582589092387)
                ·
                  refine ⟨75755676873801873883638581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50503784582534582589092387 75755676873801873883638581)
                  ·
                    refine ⟨7102094706918925676591117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75755676873801873883638581 7102094706918925676591117)
                    ·
                      refine ⟨2663285515094597128721669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7102094706918925676591117 2663285515094597128721669)
                      ·
                        rfl

theorem cell23_5186730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5186730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186730 prefixEnd_5186730 := by exact prefixLift 5186730
  have htrace : WordTrace (prefixWord ++ tailWord_5186730) baseStart_5186730 baseEnd_5186730 := by
    simpa [prefixWord, tailWord_5186730, baseEnd_5186730] using wordTrace_append hprefix tailTrace_5186730
  have hstable : (prefixWord ++ tailWord_5186730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186730).length < 2 ^ (prefixWord ++ tailWord_5186730).sum := by decide
  have hdescent : baseEnd_5186730 < baseStart_5186730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186736 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_5186736 : Nat := 118140960795 + 5186736 * 2 ^ 59
def prefixEnd_5186736 : Nat := 4983230072969 + 3 ^ 40 * 5186736 * 2
def baseEnd_5186736 : Nat := 2663288595978524105246641

theorem tailTrace_5186736 : CollatzResearch.WordTrace tailWord_5186736 prefixEnd_5186736 2663288595978524105246641 := by
  unfold tailWord_5186736
  simp only [CollatzResearch.WordTrace]
  refine ⟨94587901668674385414930031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126117202224899180553240041 94587901668674385414930031)
  ·
    refine ⟨141881852503011578122395047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94587901668674385414930031 141881852503011578122395047)
    ·
      refine ⟨212822778754517367183592571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141881852503011578122395047 212822778754517367183592571)
      ·
        refine ⟨319234168131776050775388857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212822778754517367183592571 319234168131776050775388857)
        ·
          refine ⟨239425626098832038081541643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319234168131776050775388857 239425626098832038081541643)
          ·
            refine ⟨359138439148248057122312465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239425626098832038081541643 359138439148248057122312465)
            ·
              refine ⟨269353829361186042841734349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359138439148248057122312465 269353829361186042841734349)
              ·
                refine ⟨101007686010444766065650381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269353829361186042841734349 101007686010444766065650381)
                ·
                  refine ⟨37877882253916787274618893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101007686010444766065650381 37877882253916787274618893)
                  ·
                    refine ⟨14204205845218795227982085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37877882253916787274618893 14204205845218795227982085)
                    ·
                      refine ⟨2663288595978524105246641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14204205845218795227982085 2663288595978524105246641)
                      ·
                        rfl

theorem cell23_5186736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_5186736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186736 prefixEnd_5186736 := by exact prefixLift 5186736
  have htrace : WordTrace (prefixWord ++ tailWord_5186736) baseStart_5186736 baseEnd_5186736 := by
    simpa [prefixWord, tailWord_5186736, baseEnd_5186736] using wordTrace_append hprefix tailTrace_5186736
  have hstable : (prefixWord ++ tailWord_5186736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186736).length < 2 ^ (prefixWord ++ tailWord_5186736).sum := by decide
  have hdescent : baseEnd_5186736 < baseStart_5186736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186750 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_5186750 : Nat := 118140960795 + 5186750 * 2 ^ 59
def prefixEnd_5186750 : Nat := 4983230072969 + 3 ^ 40 * 5186750 * 2
def baseEnd_5186750 : Nat := 887765261569229016823859

theorem tailTrace_5186750 : CollatzResearch.WordTrace tailWord_5186750 prefixEnd_5186750 887765261569229016823859 := by
  unfold tailWord_5186750
  simp only [CollatzResearch.WordTrace]
  refine ⟨23647039244912256402608713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126117542639532034147246469 23647039244912256402608713)
  ·
    refine ⟨17735279433684192301956535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23647039244912256402608713 17735279433684192301956535)
    ·
      refine ⟨26602919150526288452934803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17735279433684192301956535 26602919150526288452934803)
      ·
        refine ⟨39904378725789432679402205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26602919150526288452934803 39904378725789432679402205)
        ·
          refine ⟨14964142022171037254775827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39904378725789432679402205 14964142022171037254775827)
          ·
            refine ⟨22446213033256555882163741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14964142022171037254775827 22446213033256555882163741)
            ·
              refine ⟨8417329887471208455811403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22446213033256555882163741 8417329887471208455811403)
              ·
                refine ⟨12625994831206812683717105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8417329887471208455811403 12625994831206812683717105)
                ·
                  refine ⟨9469496123405109512787829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12625994831206812683717105 9469496123405109512787829)
                  ·
                    refine ⟨887765261569229016823859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9469496123405109512787829 887765261569229016823859)
                    ·
                      rfl

theorem cell23_5186750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_5186750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186750 prefixEnd_5186750 := by exact prefixLift 5186750
  have htrace : WordTrace (prefixWord ++ tailWord_5186750) baseStart_5186750 baseEnd_5186750 := by
    simpa [prefixWord, tailWord_5186750, baseEnd_5186750] using wordTrace_append hprefix tailTrace_5186750
  have hstable : (prefixWord ++ tailWord_5186750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186750).length < 2 ^ (prefixWord ++ tailWord_5186750).sum := by decide
  have hdescent : baseEnd_5186750 < baseStart_5186750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186765 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_5186765 : Nat := 118140960795 + 5186765 * 2 ^ 59
def prefixEnd_5186765 : Nat := 4983230072969 + 3 ^ 40 * 5186765 * 2
def baseEnd_5186765 : Nat := 2663303486917504491784009

theorem tailTrace_5186765 : CollatzResearch.WordTrace tailWord_5186765 prefixEnd_5186765 2663303486917504491784009 := by
  unfold tailWord_5186765
  simp only [CollatzResearch.WordTrace]
  refine ⟨189176861054243708782665749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126117907369495805855110499 189176861054243708782665749)
  ·
    refine ⟨8867665361917673849187457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 189176861054243708782665749 8867665361917673849187457)
    ·
      refine ⟨6650749021438255386890593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8867665361917673849187457 6650749021438255386890593)
      ·
        refine ⟨4988061766078691540167945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6650749021438255386890593 4988061766078691540167945)
        ·
          refine ⟨3741046324559018655125959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4988061766078691540167945 3741046324559018655125959)
          ·
            refine ⟨5611569486838527982688939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3741046324559018655125959 5611569486838527982688939)
            ·
              refine ⟨8417354230257791974033409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5611569486838527982688939 8417354230257791974033409)
              ·
                refine ⟨6313015672693343980525057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8417354230257791974033409 6313015672693343980525057)
                ·
                  refine ⟨4734761754520007985393793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6313015672693343980525057 4734761754520007985393793)
                  ·
                    refine ⟨3551071315890005989045345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4734761754520007985393793 3551071315890005989045345)
                    ·
                      refine ⟨2663303486917504491784009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551071315890005989045345 2663303486917504491784009)
                      ·
                        rfl

theorem cell23_5186765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_5186765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186765 prefixEnd_5186765 := by exact prefixLift 5186765
  have htrace : WordTrace (prefixWord ++ tailWord_5186765) baseStart_5186765 baseEnd_5186765 := by
    simpa [prefixWord, tailWord_5186765, baseEnd_5186765] using wordTrace_append hprefix tailTrace_5186765
  have hstable : (prefixWord ++ tailWord_5186765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186765).length < 2 ^ (prefixWord ++ tailWord_5186765).sum := by decide
  have hdescent : baseEnd_5186765 < baseStart_5186765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186770 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_5186770 : Nat := 118140960795 + 5186770 * 2 ^ 59
def prefixEnd_5186770 : Nat := 4983230072969 + 3 ^ 40 * 5186770 * 2
def baseEnd_5186770 : Nat := 2663306054320776972221485

theorem tailTrace_5186770 : CollatzResearch.WordTrace tailWord_5186770 prefixEnd_5186770 2663306054320776972221485 := by
  unfold tailWord_5186770
  simp only [CollatzResearch.WordTrace]
  refine ⟨47294260854806398659149441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126118028946150396424398509 47294260854806398659149441)
  ·
    refine ⟨35470695641104798994362081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47294260854806398659149441 35470695641104798994362081)
    ·
      refine ⟨26603021730828599245771561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35470695641104798994362081 26603021730828599245771561)
      ·
        refine ⟨19952266298121449434328671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26603021730828599245771561 19952266298121449434328671)
        ·
          refine ⟨29928399447182174151493007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19952266298121449434328671 29928399447182174151493007)
          ·
            refine ⟨44892599170773261227239511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29928399447182174151493007 44892599170773261227239511)
            ·
              refine ⟨67338898756159891840859267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44892599170773261227239511 67338898756159891840859267)
              ·
                refine ⟨101008348134239837761288901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67338898756159891840859267 101008348134239837761288901)
                ·
                  refine ⟨18939065275169969580241669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101008348134239837761288901 18939065275169969580241669)
                  ·
                    refine ⟨3551074739094369296295313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18939065275169969580241669 3551074739094369296295313)
                    ·
                      refine ⟨2663306054320776972221485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551074739094369296295313 2663306054320776972221485)
                      ·
                        rfl

theorem cell23_5186770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_5186770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186770 prefixEnd_5186770 := by exact prefixLift 5186770
  have htrace : WordTrace (prefixWord ++ tailWord_5186770) baseStart_5186770 baseEnd_5186770 := by
    simpa [prefixWord, tailWord_5186770, baseEnd_5186770] using wordTrace_append hprefix tailTrace_5186770
  have hstable : (prefixWord ++ tailWord_5186770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186770).length < 2 ^ (prefixWord ++ tailWord_5186770).sum := by decide
  have hdescent : baseEnd_5186770 < baseStart_5186770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186814 : List Nat := [4, 2, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_5186814 : Nat := 118140960795 + 5186814 * 2 ^ 59
def prefixEnd_5186814 : Nat := 4983230072969 + 3 ^ 40 * 5186814 * 2
def baseEnd_5186814 : Nat := 887776215823191600023761

theorem tailTrace_5186814 : CollatzResearch.WordTrace tailWord_5186814 prefixEnd_5186814 887776215823191600023761 := by
  unfold tailWord_5186814
  simp only [CollatzResearch.WordTrace]
  refine ⟨23647331028883273768899937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126119098820710793434132997 23647331028883273768899937)
  ·
    refine ⟨17735498271662455326674953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23647331028883273768899937 17735498271662455326674953)
    ·
      refine ⟨13301623703746841495006215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17735498271662455326674953 13301623703746841495006215)
      ·
        refine ⟨19952435555620262242509323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13301623703746841495006215 19952435555620262242509323)
        ·
          refine ⟨29928653333430393363763985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19952435555620262242509323 29928653333430393363763985)
          ·
            refine ⟨22446490000072795022822989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29928653333430393363763985 22446490000072795022822989)
            ·
              refine ⟨8417433750027298133558621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22446490000072795022822989 8417433750027298133558621)
              ·
                refine ⟨3156537656260236800084483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8417433750027298133558621 3156537656260236800084483)
                ·
                  refine ⟨4734806484390355200126725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156537656260236800084483 4734806484390355200126725)
                  ·
                    refine ⟨887776215823191600023761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734806484390355200126725 887776215823191600023761)
                    ·
                      rfl

theorem cell23_5186814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_5186814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186814 prefixEnd_5186814 := by exact prefixLift 5186814
  have htrace : WordTrace (prefixWord ++ tailWord_5186814) baseStart_5186814 baseEnd_5186814 := by
    simpa [prefixWord, tailWord_5186814, baseEnd_5186814] using wordTrace_append hprefix tailTrace_5186814
  have hstable : (prefixWord ++ tailWord_5186814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186814).length < 2 ^ (prefixWord ++ tailWord_5186814).sum := by decide
  have hdescent : baseEnd_5186814 < baseStart_5186814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186843 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 4]
def baseStart_5186843 : Nat := 118140960795 + 5186843 * 2 ^ 59
def prefixEnd_5186843 : Nat := 4983230072969 + 3 ^ 40 * 5186843 * 2
def baseEnd_5186843 : Nat := 2663343538408555186608649

theorem tailTrace_5186843 : CollatzResearch.WordTrace tailWord_5186843 prefixEnd_5186843 2663343538408555186608649 := by
  unfold tailWord_5186843
  simp only [CollatzResearch.WordTrace]
  refine ⟨189179705947961128104005183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126119803965307418736003455 189179705947961128104005183)
  ·
    refine ⟨283769558921941692156007775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189179705947961128104005183 283769558921941692156007775)
    ·
      refine ⟨425654338382912538234011663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283769558921941692156007775 425654338382912538234011663)
      ·
        refine ⟨638481507574368807351017495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425654338382912538234011663 638481507574368807351017495)
        ·
          refine ⟨957722261361553211026526243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638481507574368807351017495 957722261361553211026526243)
          ·
            refine ⟨1436583392042329816539789365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957722261361553211026526243 1436583392042329816539789365)
            ·
              refine ⟨134679693003968420300605253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1436583392042329816539789365 134679693003968420300605253)
              ·
                refine ⟨25252442438244078806363485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134679693003968420300605253 25252442438244078806363485)
                ·
                  refine ⟨9469665914341529552386307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25252442438244078806363485 9469665914341529552386307)
                  ·
                    refine ⟨14204498871512294328579461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9469665914341529552386307 14204498871512294328579461)
                    ·
                      refine ⟨2663343538408555186608649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14204498871512294328579461 2663343538408555186608649)
                      ·
                        rfl

theorem cell23_5186843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 4].length) (baseStart_5186843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186843 prefixEnd_5186843 := by exact prefixLift 5186843
  have htrace : WordTrace (prefixWord ++ tailWord_5186843) baseStart_5186843 baseEnd_5186843 := by
    simpa [prefixWord, tailWord_5186843, baseEnd_5186843] using wordTrace_append hprefix tailTrace_5186843
  have hstable : (prefixWord ++ tailWord_5186843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186843).length < 2 ^ (prefixWord ++ tailWord_5186843).sum := by decide
  have hdescent : baseEnd_5186843 < baseStart_5186843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186887 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 2, 4]
def baseStart_5186887 : Nat := 118140960795 + 5186887 * 2 ^ 59
def prefixEnd_5186887 : Nat := 4983230072969 + 3 ^ 40 * 5186887 * 2
def baseEnd_5186887 : Nat := 887788710519117671486149

theorem tailTrace_5186887 : CollatzResearch.WordTrace tailWord_5186887 prefixEnd_5186887 887788710519117671486149 := by
  unfold tailWord_5186887
  simp only [CollatzResearch.WordTrace]
  refine ⟨189181310759801723618606915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126120873839867815745737943 189181310759801723618606915)
  ·
    refine ⟨283771966139702585427910373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189181310759801723618606915 283771966139702585427910373)
    ·
      refine ⟨53207243651194234767733195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283771966139702585427910373 53207243651194234767733195)
      ·
        refine ⟨79810865476791352151599793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53207243651194234767733195 79810865476791352151599793)
        ·
          refine ⟨59858149107593514113699845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79810865476791352151599793 59858149107593514113699845)
          ·
            refine ⟨11223402957673783896318721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59858149107593514113699845 11223402957673783896318721)
            ·
              refine ⟨8417552218255337922239041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11223402957673783896318721 8417552218255337922239041)
              ·
                refine ⟨6313164163691503441679281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8417552218255337922239041 6313164163691503441679281)
                ·
                  refine ⟨4734873122768627581259461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6313164163691503441679281 4734873122768627581259461)
                  ·
                    refine ⟨887788710519117671486149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4734873122768627581259461 887788710519117671486149)
                    ·
                      rfl

theorem cell23_5186887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_5186887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186887 prefixEnd_5186887 := by exact prefixLift 5186887
  have htrace : WordTrace (prefixWord ++ tailWord_5186887) baseStart_5186887 baseEnd_5186887 := by
    simpa [prefixWord, tailWord_5186887, baseEnd_5186887] using wordTrace_append hprefix tailTrace_5186887
  have hstable : (prefixWord ++ tailWord_5186887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186887).length < 2 ^ (prefixWord ++ tailWord_5186887).sum := by decide
  have hdescent : baseEnd_5186887 < baseStart_5186887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5186970 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_5186970 : Nat := 118140960795 + 5186970 * 2 ^ 59
def prefixEnd_5186970 : Nat := 4983230072969 + 3 ^ 40 * 5186970 * 2
def baseEnd_5186970 : Nat := 2663408750451676189720565

theorem tailTrace_5186970 : CollatzResearch.WordTrace tailWord_5186970 prefixEnd_5186970 2663408750451676189720565 := by
  unfold tailWord_5186970
  simp only [CollatzResearch.WordTrace]
  refine ⟨47296084504625257198469591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126122892012334019195918909 47296084504625257198469591)
  ·
    refine ⟨70944126756937885797704387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47296084504625257198469591 70944126756937885797704387)
    ·
      refine ⟨106416190135406828696556581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70944126756937885797704387 106416190135406828696556581)
      ·
        refine ⟨19953035650388780380604359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106416190135406828696556581 19953035650388780380604359)
        ·
          refine ⟨29929553475583170570906539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19953035650388780380604359 29929553475583170570906539)
          ·
            refine ⟨44894330213374755856359809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29929553475583170570906539 44894330213374755856359809)
            ·
              refine ⟨33670747660031066892269857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44894330213374755856359809 33670747660031066892269857)
              ·
                refine ⟨25253060745023300169202393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33670747660031066892269857 25253060745023300169202393)
                ·
                  refine ⟨18939795558767475126901795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25253060745023300169202393 18939795558767475126901795)
                  ·
                    refine ⟨28409693338151212690352693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18939795558767475126901795 28409693338151212690352693)
                    ·
                      refine ⟨2663408750451676189720565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28409693338151212690352693 2663408750451676189720565)
                      ·
                        rfl

theorem cell23_5186970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_5186970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5186970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5186970 prefixEnd_5186970 := by exact prefixLift 5186970
  have htrace : WordTrace (prefixWord ++ tailWord_5186970) baseStart_5186970 baseEnd_5186970 := by
    simpa [prefixWord, tailWord_5186970, baseEnd_5186970] using wordTrace_append hprefix tailTrace_5186970
  have hstable : (prefixWord ++ tailWord_5186970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5186970).length < 2 ^ (prefixWord ++ tailWord_5186970).sum := by decide
  have hdescent : baseEnd_5186970 < baseStart_5186970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5186970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187000 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_5187000 : Nat := 118140960795 + 5187000 * 2 ^ 59
def prefixEnd_5187000 : Nat := 4983230072969 + 3 ^ 40 * 5187000 * 2
def baseEnd_5187000 : Nat := 2663424154871311072345427

theorem tailTrace_5187000 : CollatzResearch.WordTrace tailWord_5187000 prefixEnd_5187000 2663424154871311072345427 := by
  unfold tailWord_5187000
  simp only [CollatzResearch.WordTrace]
  refine ⟨94592716104196171958735227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126123621472261562611646969 94592716104196171958735227)
  ·
    refine ⟨141889074156294257938102841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94592716104196171958735227 141889074156294257938102841)
    ·
      refine ⟨106416805617220693453577131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141889074156294257938102841 106416805617220693453577131)
      ·
        refine ⟨159625208425831040180365697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106416805617220693453577131 159625208425831040180365697)
        ·
          refine ⟨119718906319373280135274273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159625208425831040180365697 119718906319373280135274273)
          ·
            refine ⟨89789179739529960101455705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119718906319373280135274273 89789179739529960101455705)
            ·
              refine ⟨67341884804647470076091779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89789179739529960101455705 67341884804647470076091779)
              ·
                refine ⟨101012827206971205114137669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67341884804647470076091779 101012827206971205114137669)
                ·
                  refine ⟨18939905101307100958900813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101012827206971205114137669 18939905101307100958900813)
                  ·
                    refine ⟨7102464412990162859587805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18939905101307100958900813 7102464412990162859587805)
                    ·
                      refine ⟨2663424154871311072345427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7102464412990162859587805 2663424154871311072345427)
                      ·
                        rfl

theorem cell23_5187000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_5187000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187000 prefixEnd_5187000 := by exact prefixLift 5187000
  have htrace : WordTrace (prefixWord ++ tailWord_5187000) baseStart_5187000 baseEnd_5187000 := by
    simpa [prefixWord, tailWord_5187000, baseEnd_5187000] using wordTrace_append hprefix tailTrace_5187000
  have hstable : (prefixWord ++ tailWord_5187000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187000).length < 2 ^ (prefixWord ++ tailWord_5187000).sum := by decide
  have hdescent : baseEnd_5187000 < baseStart_5187000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187018 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_5187018 : Nat := 118140960795 + 5187018 * 2 ^ 59
def prefixEnd_5187018 : Nat := 4983230072969 + 3 ^ 40 * 5187018 * 2
def baseEnd_5187018 : Nat := 2663433397523092001920345

theorem tailTrace_5187018 : CollatzResearch.WordTrace tailWord_5187018 prefixEnd_5187018 2663433397523092001920345 := by
  unfold tailWord_5187018
  simp only [CollatzResearch.WordTrace]
  refine ⟨47296522180581783247906427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126124059148218088661083805 47296522180581783247906427)
  ·
    refine ⟨70944783270872674871859641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47296522180581783247906427 70944783270872674871859641)
    ·
      refine ⟨53208587453154506153894731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70944783270872674871859641 53208587453154506153894731)
      ·
        refine ⟨79812881179731759230842097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53208587453154506153894731 79812881179731759230842097)
        ·
          refine ⟨59859660884798819423131573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79812881179731759230842097 59859660884798819423131573)
          ·
            refine ⟨5611843207949889320918585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59859660884798819423131573 5611843207949889320918585)
            ·
              refine ⟨4208882405962416990688939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5611843207949889320918585 4208882405962416990688939)
              ·
                refine ⟨6313323608943625486033409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4208882405962416990688939 6313323608943625486033409)
                ·
                  refine ⟨4734992706707719114525057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6313323608943625486033409 4734992706707719114525057)
                  ·
                    refine ⟨3551244530030789335893793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4734992706707719114525057 3551244530030789335893793)
                    ·
                      refine ⟨2663433397523092001920345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551244530030789335893793 2663433397523092001920345)
                      ·
                        rfl

theorem cell23_5187018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_5187018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187018 prefixEnd_5187018 := by exact prefixLift 5187018
  have htrace : WordTrace (prefixWord ++ tailWord_5187018) baseStart_5187018 baseEnd_5187018 := by
    simpa [prefixWord, tailWord_5187018, baseEnd_5187018] using wordTrace_append hprefix tailTrace_5187018
  have hstable : (prefixWord ++ tailWord_5187018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187018).length < 2 ^ (prefixWord ++ tailWord_5187018).sum := by decide
  have hdescent : baseEnd_5187018 < baseStart_5187018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187037 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_5187037 : Nat := 118140960795 + 5187037 * 2 ^ 59
def prefixEnd_5187037 : Nat := 4983230072969 + 3 ^ 40 * 5187037 * 2
def baseEnd_5187037 : Nat := 887814384551842475860919

theorem tailTrace_5187037 : CollatzResearch.WordTrace tailWord_5187037 prefixEnd_5187037 887814384551842475860919 := by
  unfold tailWord_5187037
  simp only [CollatzResearch.WordTrace]
  refine ⟨189186781709258299236567365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126124521139505532824378243 189186781709258299236567365)
  ·
    refine ⟨35472521570485931106856381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189186781709258299236567365 35472521570485931106856381)
    ·
      refine ⟨13302195588932224165071143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35472521570485931106856381 13302195588932224165071143)
      ·
        refine ⟨19953293383398336247606715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13302195588932224165071143 19953293383398336247606715)
        ·
          refine ⟨29929940075097504371410073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19953293383398336247606715 29929940075097504371410073)
          ·
            refine ⟨22447455056323128278557555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29929940075097504371410073 22447455056323128278557555)
            ·
              refine ⟨33671182584484692417836333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22447455056323128278557555 33671182584484692417836333)
              ·
                refine ⟨12626693469181759656688625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33671182584484692417836333 12626693469181759656688625)
                ·
                  refine ⟨9470020101886319742516469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12626693469181759656688625 9470020101886319742516469)
                  ·
                    refine ⟨887814384551842475860919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9470020101886319742516469 887814384551842475860919)
                    ·
                      rfl

theorem cell23_5187037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_5187037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187037 prefixEnd_5187037 := by exact prefixLift 5187037
  have htrace : WordTrace (prefixWord ++ tailWord_5187037) baseStart_5187037 baseEnd_5187037 := by
    simpa [prefixWord, tailWord_5187037, baseEnd_5187037] using wordTrace_append hprefix tailTrace_5187037
  have hstable : (prefixWord ++ tailWord_5187037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187037).length < 2 ^ (prefixWord ++ tailWord_5187037).sum := by decide
  have hdescent : baseEnd_5187037 < baseStart_5187037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187057 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_5187057 : Nat := 118140960795 + 5187057 * 2 ^ 59
def prefixEnd_5187057 : Nat := 4983230072969 + 3 ^ 40 * 5187057 * 2
def baseEnd_5187057 : Nat := 2663453423268617349332665

theorem tailTrace_5187057 : CollatzResearch.WordTrace tailWord_5187057 prefixEnd_5187057 2663453423268617349332665 := by
  unfold tailWord_5187057
  simp only [CollatzResearch.WordTrace]
  refine ⟨189187511169185842652295425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126125007446123895101530283 189187511169185842652295425)
  ·
    refine ⟨141890633376889381989221569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189187511169185842652295425 141890633376889381989221569)
    ·
      refine ⟨106417975032667036491916177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141890633376889381989221569 106417975032667036491916177)
      ·
        refine ⟨79813481274500277368937133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106417975032667036491916177 79813481274500277368937133)
        ·
          refine ⟨29930055477937604013351425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79813481274500277368937133 29930055477937604013351425)
          ·
            refine ⟨22447541608453203010013569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29930055477937604013351425 22447541608453203010013569)
            ·
              refine ⟨16835656206339902257510177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22447541608453203010013569 16835656206339902257510177)
              ·
                refine ⟨12626742154754926693132633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16835656206339902257510177 12626742154754926693132633)
                ·
                  refine ⟨9470056616066195019849475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12626742154754926693132633 9470056616066195019849475)
                  ·
                    refine ⟨14205084924099292529774213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9470056616066195019849475 14205084924099292529774213)
                    ·
                      refine ⟨2663453423268617349332665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14205084924099292529774213 2663453423268617349332665)
                      ·
                        rfl

theorem cell23_5187057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_5187057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187057 prefixEnd_5187057 := by exact prefixLift 5187057
  have htrace : WordTrace (prefixWord ++ tailWord_5187057) baseStart_5187057 baseEnd_5187057 := by
    simpa [prefixWord, tailWord_5187057, baseEnd_5187057] using wordTrace_append hprefix tailTrace_5187057
  have hstable : (prefixWord ++ tailWord_5187057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187057).length < 2 ^ (prefixWord ++ tailWord_5187057).sum := by decide
  have hdescent : baseEnd_5187057 < baseStart_5187057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187084 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_5187084 : Nat := 118140960795 + 5187084 * 2 ^ 59
def prefixEnd_5187084 : Nat := 4983230072969 + 3 ^ 40 * 5187084 * 2
def baseEnd_5187084 : Nat := 887822429082096247898347

theorem tailTrace_5187084 : CollatzResearch.WordTrace tailWord_5187084 prefixEnd_5187084 887822429082096247898347 := by
  unfold tailWord_5187084
  simp only [CollatzResearch.WordTrace]
  refine ⟨94594247970044013131764153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126125663960058684175685537 94594247970044013131764153)
  ·
    refine ⟨70945685977533009848823115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94594247970044013131764153 70945685977533009848823115)
    ·
      refine ⟨106418528966299514773234673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70945685977533009848823115 106418528966299514773234673)
      ·
        refine ⟨79813896724724636079926005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106418528966299514773234673 79813896724724636079926005)
        ·
          refine ⟨7482552817942934632493063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79813896724724636079926005 7482552817942934632493063)
          ·
            refine ⟨11223829226914401948739595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7482552817942934632493063 11223829226914401948739595)
            ·
              refine ⟨16835743840371602923109393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11223829226914401948739595 16835743840371602923109393)
              ·
                refine ⟨12626807880278702192332045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16835743840371602923109393 12626807880278702192332045)
                ·
                  refine ⟨4735052955104513322124517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12626807880278702192332045 4735052955104513322124517)
                  ·
                    refine ⟨887822429082096247898347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4735052955104513322124517 887822429082096247898347)
                    ·
                      rfl

theorem cell23_5187084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_5187084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187084 prefixEnd_5187084 := by exact prefixLift 5187084
  have htrace : WordTrace (prefixWord ++ tailWord_5187084) baseStart_5187084 baseEnd_5187084 := by
    simpa [prefixWord, tailWord_5187084, baseEnd_5187084] using wordTrace_append hprefix tailTrace_5187084
  have hstable : (prefixWord ++ tailWord_5187084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187084).length < 2 ^ (prefixWord ++ tailWord_5187084).sum := by decide
  have hdescent : baseEnd_5187084 < baseStart_5187084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187101 : List Nat := [1, 4, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_5187101 : Nat := 118140960795 + 5187101 * 2 ^ 59
def prefixEnd_5187101 : Nat := 4983230072969 + 3 ^ 40 * 5187101 * 2
def baseEnd_5187101 : Nat := 887825338805805059060821

theorem tailTrace_5187101 : CollatzResearch.WordTrace tailWord_5187101 prefixEnd_5187101 887825338805805059060821 := by
  unfold tailWord_5187101
  simp only [CollatzResearch.WordTrace]
  refine ⟨189189115981026438166897157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126126077320684292111264771 189189115981026438166897157)
  ·
    refine ⟨35472959246442457156293217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189189115981026438166897157 35472959246442457156293217)
    ·
      refine ⟨26604719434831842867219913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35472959246442457156293217 26604719434831842867219913)
      ·
        refine ⟨19953539576123882150414935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26604719434831842867219913 19953539576123882150414935)
        ·
          refine ⟨29930309364185823225622403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19953539576123882150414935 29930309364185823225622403)
          ·
            refine ⟨44895464046278734838433605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29930309364185823225622403 44895464046278734838433605)
            ·
              refine ⟨8417899508677262782206301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44895464046278734838433605 8417899508677262782206301)
              ·
                refine ⟨3156712315753973543327363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8417899508677262782206301 3156712315753973543327363)
                ·
                  refine ⟨4735068473630960314991045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156712315753973543327363 4735068473630960314991045)
                  ·
                    refine ⟨887825338805805059060821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4735068473630960314991045 887825338805805059060821)
                    ·
                      rfl

theorem cell23_5187101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_5187101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187101 prefixEnd_5187101 := by exact prefixLift 5187101
  have htrace : WordTrace (prefixWord ++ tailWord_5187101) baseStart_5187101 baseEnd_5187101 := by
    simpa [prefixWord, tailWord_5187101, baseEnd_5187101] using wordTrace_append hprefix tailTrace_5187101
  have hstable : (prefixWord ++ tailWord_5187101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187101).length < 2 ^ (prefixWord ++ tailWord_5187101).sum := by decide
  have hdescent : baseEnd_5187101 < baseStart_5187101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187147 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 8, 2]
def baseStart_5187147 : Nat := 118140960795 + 5187147 * 2 ^ 59
def prefixEnd_5187147 : Nat := 4983230072969 + 3 ^ 40 * 5187147 * 2
def baseEnd_5187147 : Nat := 2663499636527521997207251

theorem tailTrace_5187147 : CollatzResearch.WordTrace tailWord_5187147 prefixEnd_5187147 2663499636527521997207251 := by
  unfold tailWord_5187147
  simp only [CollatzResearch.WordTrace]
  refine ⟨189190793738859788023071695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126127195825906525348714463 189190793738859788023071695)
  ·
    refine ⟨283786190608289682034607543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189190793738859788023071695 283786190608289682034607543)
    ·
      refine ⟨425679285912434523051911315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283786190608289682034607543 425679285912434523051911315)
      ·
        refine ⟨638518928868651784577866973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425679285912434523051911315 638518928868651784577866973)
        ·
          refine ⟨239444598325744419216700115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638518928868651784577866973 239444598325744419216700115)
          ·
            refine ⟨359166897488616628825050173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239444598325744419216700115 359166897488616628825050173)
            ·
              refine ⟨134687586558231235809393815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359166897488616628825050173 134687586558231235809393815)
              ·
                refine ⟨202031379837346853714090723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134687586558231235809393815 202031379837346853714090723)
                ·
                  refine ⟨303047069756020280571136085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202031379837346853714090723 303047069756020280571136085)
                  ·
                    refine ⟨3551332848703362662943001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 303047069756020280571136085 3551332848703362662943001)
                    ·
                      refine ⟨2663499636527521997207251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551332848703362662943001 2663499636527521997207251)
                      ·
                        rfl

theorem cell23_5187147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8, 2].length) (baseStart_5187147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187147 prefixEnd_5187147 := by exact prefixLift 5187147
  have htrace : WordTrace (prefixWord ++ tailWord_5187147) baseStart_5187147 baseEnd_5187147 := by
    simpa [prefixWord, tailWord_5187147, baseEnd_5187147] using wordTrace_append hprefix tailTrace_5187147
  have hstable : (prefixWord ++ tailWord_5187147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187147).length < 2 ^ (prefixWord ++ tailWord_5187147).sum := by decide
  have hdescent : baseEnd_5187147 < baseStart_5187147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187167 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 3]
def baseStart_5187167 : Nat := 118140960795 + 5187167 * 2 ^ 59
def prefixEnd_5187167 : Nat := 4983230072969 + 3 ^ 40 * 5187167 * 2
def baseEnd_5187167 : Nat := 2663509906140611918957159

theorem tailTrace_5187167 : CollatzResearch.WordTrace tailWord_5187167 prefixEnd_5187167 2663509906140611918957159 := by
  unfold tailWord_5187167
  simp only [CollatzResearch.WordTrace]
  refine ⟨189191523198787331438799755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126127682132524887625866503 189191523198787331438799755)
  ·
    refine ⟨283787284798180997158199633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189191523198787331438799755 283787284798180997158199633)
    ·
      refine ⟨212840463598635747868649725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283787284798180997158199633 212840463598635747868649725)
      ·
        refine ⟨79815173849488405450743647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212840463598635747868649725 79815173849488405450743647)
        ·
          refine ⟨119722760774232608176115471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79815173849488405450743647 119722760774232608176115471)
          ·
            refine ⟨179584141161348912264173207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119722760774232608176115471 179584141161348912264173207)
            ·
              refine ⟨269376211742023368396259811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179584141161348912264173207 269376211742023368396259811)
              ·
                refine ⟨404064317613035052594389717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269376211742023368396259811 404064317613035052594389717)
                ·
                  refine ⟨9470257444055509045181009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 404064317613035052594389717 9470257444055509045181009)
                  ·
                    refine ⟨7102693083041631783885757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9470257444055509045181009 7102693083041631783885757)
                    ·
                      refine ⟨2663509906140611918957159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7102693083041631783885757 2663509906140611918957159)
                      ·
                        rfl

theorem cell23_5187167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_5187167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187167 prefixEnd_5187167 := by exact prefixLift 5187167
  have htrace : WordTrace (prefixWord ++ tailWord_5187167) baseStart_5187167 baseEnd_5187167 := by
    simpa [prefixWord, tailWord_5187167, baseEnd_5187167] using wordTrace_append hprefix tailTrace_5187167
  have hstable : (prefixWord ++ tailWord_5187167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187167).length < 2 ^ (prefixWord ++ tailWord_5187167).sum := by decide
  have hdescent : baseEnd_5187167 < baseStart_5187167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187201 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_5187201 : Nat := 118140960795 + 5187201 * 2 ^ 59
def prefixEnd_5187201 : Nat := 4983230072969 + 3 ^ 40 * 5187201 * 2
def baseEnd_5187201 : Nat := 2663527364482864785932003

theorem tailTrace_5187201 : CollatzResearch.WordTrace tailWord_5187201 prefixEnd_5187201 2663527364482864785932003 := by
  unfold tailWord_5187201
  simp only [CollatzResearch.WordTrace]
  refine ⟨189192763280664155245537457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126128508853776103497024971 189192763280664155245537457)
  ·
    refine ⟨141894572460498116434153093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189192763280664155245537457 141894572460498116434153093)
    ·
      refine ⟨26605232336343396831403705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141894572460498116434153093 26605232336343396831403705)
      ·
        refine ⟨19953924252257547623552779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26605232336343396831403705 19953924252257547623552779)
        ·
          refine ⟨29930886378386321435329169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19953924252257547623552779 29930886378386321435329169)
          ·
            refine ⟨22448164783789741076496877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29930886378386321435329169 22448164783789741076496877)
            ·
              refine ⟨8418061793921152903686329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22448164783789741076496877 8418061793921152903686329)
              ·
                refine ⟨6313546345440864677764747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8418061793921152903686329 6313546345440864677764747)
                ·
                  refine ⟨9470319518161297016647121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6313546345440864677764747 9470319518161297016647121)
                  ·
                    refine ⟨7102739638620972762485341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9470319518161297016647121 7102739638620972762485341)
                    ·
                      refine ⟨2663527364482864785932003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7102739638620972762485341 2663527364482864785932003)
                      ·
                        rfl

theorem cell23_5187201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_5187201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187201 prefixEnd_5187201 := by exact prefixLift 5187201
  have htrace : WordTrace (prefixWord ++ tailWord_5187201) baseStart_5187201 baseEnd_5187201 := by
    simpa [prefixWord, tailWord_5187201, baseEnd_5187201] using wordTrace_append hprefix tailTrace_5187201
  have hstable : (prefixWord ++ tailWord_5187201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187201).length < 2 ^ (prefixWord ++ tailWord_5187201).sum := by decide
  have hdescent : baseEnd_5187201 < baseStart_5187201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187214 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_5187214 : Nat := 118140960795 + 5187214 * 2 ^ 59
def prefixEnd_5187214 : Nat := 4983230072969 + 3 ^ 40 * 5187214 * 2
def baseEnd_5187214 : Nat := 2663534039731373235069443

theorem tailTrace_5187214 : CollatzResearch.WordTrace tailWord_5187214 prefixEnd_5187214 2663534039731373235069443 := by
  unfold tailWord_5187214
  simp only [CollatzResearch.WordTrace]
  refine ⟨23649154678702132308220087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126128824953078038977173797 23649154678702132308220087)
  ·
    refine ⟨35473732018053198462330131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23649154678702132308220087 35473732018053198462330131)
    ·
      refine ⟨53210598027079797693495197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35473732018053198462330131 53210598027079797693495197)
      ·
        refine ⟨19953974260154924135060699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53210598027079797693495197 19953974260154924135060699)
        ·
          refine ⟨29930961390232386202591049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19953974260154924135060699 29930961390232386202591049)
          ·
            refine ⟨22448221042674289651943287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29930961390232386202591049 22448221042674289651943287)
            ·
              refine ⟨33672331564011434477914931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22448221042674289651943287 33672331564011434477914931)
              ·
                refine ⟨50508497346017151716872397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33672331564011434477914931 50508497346017151716872397)
                ·
                  refine ⟨18940686504756431893827149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50508497346017151716872397 18940686504756431893827149)
                  ·
                    refine ⟨7102757439283661960185181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18940686504756431893827149 7102757439283661960185181)
                    ·
                      refine ⟨2663534039731373235069443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7102757439283661960185181 2663534039731373235069443)
                      ·
                        rfl

theorem cell23_5187214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_5187214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187214 prefixEnd_5187214 := by exact prefixLift 5187214
  have htrace : WordTrace (prefixWord ++ tailWord_5187214) baseStart_5187214 baseEnd_5187214 := by
    simpa [prefixWord, tailWord_5187214, baseEnd_5187214] using wordTrace_append hprefix tailTrace_5187214
  have hstable : (prefixWord ++ tailWord_5187214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187214).length < 2 ^ (prefixWord ++ tailWord_5187214).sum := by decide
  have hdescent : baseEnd_5187214 < baseStart_5187214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187218 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_5187218 : Nat := 118140960795 + 5187218 * 2 ^ 59
def prefixEnd_5187218 : Nat := 4983230072969 + 3 ^ 40 * 5187218 * 2
def baseEnd_5187218 : Nat := 2663536093653991219419425

theorem tailTrace_5187218 : CollatzResearch.WordTrace tailWord_5187218 prefixEnd_5187218 2663536093653991219419425 := by
  unfold tailWord_5187218
  simp only [CollatzResearch.WordTrace]
  refine ⟨47298345830400641787226577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126128922214401711432604205 47298345830400641787226577)
  ·
    refine ⟨35473759372800481340419933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47298345830400641787226577 35473759372800481340419933)
    ·
      refine ⟨13302659764800180502657475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35473759372800481340419933 13302659764800180502657475)
      ·
        refine ⟨19953989647200270753986213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13302659764800180502657475 19953989647200270753986213)
        ·
          refine ⟨3741373058850050766372415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19953989647200270753986213 3741373058850050766372415)
          ·
            refine ⟨5612059588275076149558623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3741373058850050766372415 5612059588275076149558623)
            ·
              refine ⟨8418089382412614224337935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5612059588275076149558623 8418089382412614224337935)
              ·
                refine ⟨12627134073618921336506903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8418089382412614224337935 12627134073618921336506903)
                ·
                  refine ⟨18940701110428382004760355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12627134073618921336506903 18940701110428382004760355)
                  ·
                    refine ⟨28411051665642573007140533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18940701110428382004760355 28411051665642573007140533)
                    ·
                      refine ⟨2663536093653991219419425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28411051665642573007140533 2663536093653991219419425)
                      ·
                        rfl

theorem cell23_5187218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_5187218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187218 prefixEnd_5187218 := by exact prefixLift 5187218
  have htrace : WordTrace (prefixWord ++ tailWord_5187218) baseStart_5187218 baseEnd_5187218 := by
    simpa [prefixWord, tailWord_5187218, baseEnd_5187218] using wordTrace_append hprefix tailTrace_5187218
  have hstable : (prefixWord ++ tailWord_5187218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187218).length < 2 ^ (prefixWord ++ tailWord_5187218).sum := by decide
  have hdescent : baseEnd_5187218 < baseStart_5187218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187232 : List Nat := [2, 1, 1, 4, 3, 3, 2, 2, 1, 2, 2]
def baseStart_5187232 : Nat := 118140960795 + 5187232 * 2 ^ 59
def prefixEnd_5187232 : Nat := 4983230072969 + 3 ^ 40 * 5187232 * 2
def baseEnd_5187232 : Nat := 2663543282383154164644361

theorem tailTrace_5187232 : CollatzResearch.WordTrace tailWord_5187232 prefixEnd_5187232 2663543282383154164644361 := by
  unfold tailWord_5187232
  simp only [CollatzResearch.WordTrace]
  refine ⟨94596946971775923769957975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126129262629034565026610633 94596946971775923769957975)
  ·
    refine ⟨141895420457663885654936963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94596946971775923769957975 141895420457663885654936963)
    ·
      refine ⟨212843130686495828482405445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141895420457663885654936963 212843130686495828482405445)
      ·
        refine ⟨39908087003717967840451021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212843130686495828482405445 39908087003717967840451021)
        ·
          refine ⟨14965532626394237940169133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39908087003717967840451021 14965532626394237940169133)
          ·
            refine ⟨5612074734897839227563425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14965532626394237940169133 5612074734897839227563425)
            ·
              refine ⟨4209056051173379420672569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5612074734897839227563425 4209056051173379420672569)
              ·
                refine ⟨3156792038380034565504427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4209056051173379420672569 3156792038380034565504427)
                ·
                  refine ⟨4735188057570051848256641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156792038380034565504427 4735188057570051848256641)
                  ·
                    refine ⟨3551391043177538886192481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4735188057570051848256641 3551391043177538886192481)
                    ·
                      refine ⟨2663543282383154164644361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551391043177538886192481 2663543282383154164644361)
                      ·
                        rfl

theorem cell23_5187232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_5187232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187232 prefixEnd_5187232 := by exact prefixLift 5187232
  have htrace : WordTrace (prefixWord ++ tailWord_5187232) baseStart_5187232 baseEnd_5187232 := by
    simpa [prefixWord, tailWord_5187232, baseEnd_5187232] using wordTrace_append hprefix tailTrace_5187232
  have hstable : (prefixWord ++ tailWord_5187232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187232).length < 2 ^ (prefixWord ++ tailWord_5187232).sum := by decide
  have hdescent : baseEnd_5187232 < baseStart_5187232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187237 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_5187237 : Nat := 118140960795 + 5187237 * 2 ^ 59
def prefixEnd_5187237 : Nat := 4983230072969 + 3 ^ 40 * 5187237 * 2
def baseEnd_5187237 : Nat := 2663545849786426645081837

theorem tailTrace_5187237 : CollatzResearch.WordTrace tailWord_5187237 prefixEnd_5187237 2663545849786426645081837 := by
  unfold tailWord_5187237
  simp only [CollatzResearch.WordTrace]
  refine ⟨189194076308533733393847965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126129384205689155595898643 189194076308533733393847965)
  ·
    refine ⟨70947778615700150022692987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189194076308533733393847965 70947778615700150022692987)
    ·
      refine ⟨106421667923550225034039481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70947778615700150022692987 106421667923550225034039481)
      ·
        refine ⟨79816250942662668775529611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106421667923550225034039481 79816250942662668775529611)
        ·
          refine ⟨119724376413994003163294417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79816250942662668775529611 119724376413994003163294417)
          ·
            refine ⟨89793282310495502372470813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119724376413994003163294417 89793282310495502372470813)
            ·
              refine ⟨33672480866435813389676555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89793282310495502372470813 33672480866435813389676555)
              ·
                refine ⟨50508721299653720084514833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33672480866435813389676555 50508721299653720084514833)
                ·
                  refine ⟨37881540974740290063386125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50508721299653720084514833 37881540974740290063386125)
                  ·
                    refine ⟨14205577865527608773769797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37881540974740290063386125 14205577865527608773769797)
                    ·
                      refine ⟨2663545849786426645081837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14205577865527608773769797 2663545849786426645081837)
                      ·
                        rfl

theorem cell23_5187237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_5187237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187237 prefixEnd_5187237 := by exact prefixLift 5187237
  have htrace : WordTrace (prefixWord ++ tailWord_5187237) baseStart_5187237 baseEnd_5187237 := by
    simpa [prefixWord, tailWord_5187237, baseEnd_5187237] using wordTrace_append hprefix tailTrace_5187237
  have hstable : (prefixWord ++ tailWord_5187237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187237).length < 2 ^ (prefixWord ++ tailWord_5187237).sum := by decide
  have hdescent : baseEnd_5187237 < baseStart_5187237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187247 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 2, 6]
def baseStart_5187247 : Nat := 118140960795 + 5187247 * 2 ^ 59
def prefixEnd_5187247 : Nat := 4983230072969 + 3 ^ 40 * 5187247 * 2
def baseEnd_5187247 : Nat := 887850328197657201985597

theorem tailTrace_5187247 : CollatzResearch.WordTrace tailWord_5187247 prefixEnd_5187247 887850328197657201985597 := by
  unfold tailWord_5187247
  simp only [CollatzResearch.WordTrace]
  refine ⟨189194441038497505101711995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126129627358998336734474663 189194441038497505101711995)
  ·
    refine ⟨283791661557746257652567993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189194441038497505101711995 283791661557746257652567993)
    ·
      refine ⟨212843746168309693239425995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283791661557746257652567993 212843746168309693239425995)
      ·
        refine ⟨319265619252464539859138993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212843746168309693239425995 319265619252464539859138993)
        ·
          refine ⟨239449214439348404894354245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319265619252464539859138993 239449214439348404894354245)
          ·
            refine ⟨44896727707377825917691421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239449214439348404894354245 44896727707377825917691421)
            ·
              refine ⟨16836272890266684719134283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44896727707377825917691421 16836272890266684719134283)
              ·
                refine ⟨25254409335400027078701425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16836272890266684719134283 25254409335400027078701425)
                ·
                  refine ⟨18940807001550020309026069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25254409335400027078701425 18940807001550020309026069)
                  ·
                    refine ⟨887850328197657201985597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18940807001550020309026069 887850328197657201985597)
                    ·
                      rfl

theorem cell23_5187247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_5187247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187247 prefixEnd_5187247 := by exact prefixLift 5187247
  have htrace : WordTrace (prefixWord ++ tailWord_5187247) baseStart_5187247 baseEnd_5187247 := by
    simpa [prefixWord, tailWord_5187247, baseEnd_5187247] using wordTrace_append hprefix tailTrace_5187247
  have hstable : (prefixWord ++ tailWord_5187247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187247).length < 2 ^ (prefixWord ++ tailWord_5187247).sum := by decide
  have hdescent : baseEnd_5187247 < baseStart_5187247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187257 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_5187257 : Nat := 118140960795 + 5187257 * 2 ^ 59
def prefixEnd_5187257 : Nat := 4983230072969 + 3 ^ 40 * 5187257 * 2
def baseEnd_5187257 : Nat := 2663556119399516566831745

theorem tailTrace_5187257 : CollatzResearch.WordTrace tailWord_5187257 prefixEnd_5187257 2663556119399516566831745 := by
  unfold tailWord_5187257
  simp only [CollatzResearch.WordTrace]
  refine ⟨189194805768461276809576025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126129870512307517873050683 189194805768461276809576025)
  ·
    refine ⟨141896104326345957607182019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189194805768461276809576025 141896104326345957607182019)
    ·
      refine ⟨212844156489518936410773029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141896104326345957607182019 212844156489518936410773029)
      ·
        refine ⟨39908279341784800577019943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212844156489518936410773029 39908279341784800577019943)
        ·
          refine ⟨59862419012677200865529915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39908279341784800577019943 59862419012677200865529915)
          ·
            refine ⟨89793628519015801298294873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59862419012677200865529915 89793628519015801298294873)
            ·
              refine ⟨67345221389261850973721155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89793628519015801298294873 67345221389261850973721155)
              ·
                refine ⟨101017832083892776460581733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67345221389261850973721155 101017832083892776460581733)
                ·
                  refine ⟨18940843515729895586359075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101017832083892776460581733 18940843515729895586359075)
                  ·
                    refine ⟨28411265273594843379538613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18940843515729895586359075 28411265273594843379538613)
                    ·
                      refine ⟨2663556119399516566831745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28411265273594843379538613 2663556119399516566831745)
                      ·
                        rfl

theorem cell23_5187257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_5187257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187257 prefixEnd_5187257 := by exact prefixLift 5187257
  have htrace : WordTrace (prefixWord ++ tailWord_5187257) baseStart_5187257 baseEnd_5187257 := by
    simpa [prefixWord, tailWord_5187257, baseEnd_5187257] using wordTrace_append hprefix tailTrace_5187257
  have hstable : (prefixWord ++ tailWord_5187257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187257).length < 2 ^ (prefixWord ++ tailWord_5187257).sum := by decide
  have hdescent : baseEnd_5187257 < baseStart_5187257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187266 : List Nat := [3, 5, 1, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_5187266 : Nat := 118140960795 + 5187266 * 2 ^ 59
def prefixEnd_5187266 : Nat := 4983230072969 + 3 ^ 40 * 5187266 * 2
def baseEnd_5187266 : Nat := 2663560740725407031619205

theorem tailTrace_5187266 : CollatzResearch.WordTrace tailWord_5187266 prefixEnd_5187266 2663560740725407031619205 := by
  unfold tailWord_5187266
  simp only [CollatzResearch.WordTrace]
  refine ⟨47298783506357167836663413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126130089350285780897769101 47298783506357167836663413)
  ·
    refine ⟨4434260953720984484687195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47298783506357167836663413 4434260953720984484687195)
    ·
      refine ⟨6651391430581476727030793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4434260953720984484687195 6651391430581476727030793)
      ·
        refine ⟨4988543572936107545273095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6651391430581476727030793 4988543572936107545273095)
        ·
          refine ⟨7482815359404161317909643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988543572936107545273095 7482815359404161317909643)
          ·
            refine ⟨11224223039106241976864465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7482815359404161317909643 11224223039106241976864465)
            ·
              refine ⟨8418167279329681482648349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11224223039106241976864465 8418167279329681482648349)
              ·
                refine ⟨3156812729748630555993131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8418167279329681482648349 3156812729748630555993131)
                ·
                  refine ⟨4735219094622945833989697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156812729748630555993131 4735219094622945833989697)
                  ·
                    refine ⟨3551414320967209375492273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4735219094622945833989697 3551414320967209375492273)
                    ·
                      refine ⟨2663560740725407031619205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551414320967209375492273 2663560740725407031619205)
                      ·
                        rfl

theorem cell23_5187266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_5187266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187266 prefixEnd_5187266 := by exact prefixLift 5187266
  have htrace : WordTrace (prefixWord ++ tailWord_5187266) baseStart_5187266 baseEnd_5187266 := by
    simpa [prefixWord, tailWord_5187266, baseEnd_5187266] using wordTrace_append hprefix tailTrace_5187266
  have hstable : (prefixWord ++ tailWord_5187266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187266).length < 2 ^ (prefixWord ++ tailWord_5187266).sum := by decide
  have hdescent : baseEnd_5187266 < baseStart_5187266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187271 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_5187271 : Nat := 118140960795 + 5187271 * 2 ^ 59
def prefixEnd_5187271 : Nat := 4983230072969 + 3 ^ 40 * 5187271 * 2
def baseEnd_5187271 : Nat := 2663563308128679512056681

theorem tailTrace_5187271 : CollatzResearch.WordTrace tailWord_5187271 prefixEnd_5187271 2663563308128679512056681 := by
  unfold tailWord_5187271
  simp only [CollatzResearch.WordTrace]
  refine ⟨189195316390410557200585667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126130210926940371467057111 189195316390410557200585667)
  ·
    refine ⟨283792974585615835800878501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189195316390410557200585667 283792974585615835800878501)
    ·
      refine ⟨53211182734802969212664719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283792974585615835800878501 53211182734802969212664719)
      ·
        refine ⟨79816774102204453818997079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53211182734802969212664719 79816774102204453818997079)
        ·
          refine ⟨119725161153306680728495619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79816774102204453818997079 119725161153306680728495619)
          ·
            refine ⟨179587741729960021092743429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119725161153306680728495619 179587741729960021092743429)
            ·
              refine ⟨33672701574367503954889393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179587741729960021092743429 33672701574367503954889393)
              ·
                refine ⟨25254526180775627966167045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33672701574367503954889393 25254526180775627966167045)
                ·
                  refine ⟨4735223658895430243656321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25254526180775627966167045 4735223658895430243656321)
                  ·
                    refine ⟨3551417744171572682742241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4735223658895430243656321 3551417744171572682742241)
                    ·
                      refine ⟨2663563308128679512056681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551417744171572682742241 2663563308128679512056681)
                      ·
                        rfl

theorem cell23_5187271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_5187271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187271 prefixEnd_5187271 := by exact prefixLift 5187271
  have htrace : WordTrace (prefixWord ++ tailWord_5187271) baseStart_5187271 baseEnd_5187271 := by
    simpa [prefixWord, tailWord_5187271, baseEnd_5187271] using wordTrace_append hprefix tailTrace_5187271
  have hstable : (prefixWord ++ tailWord_5187271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187271).length < 2 ^ (prefixWord ++ tailWord_5187271).sum := by decide
  have hdescent : baseEnd_5187271 < baseStart_5187271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187307 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 1, 7]
def baseStart_5187307 : Nat := 118140960795 + 5187307 * 2 ^ 59
def prefixEnd_5187307 : Nat := 4983230072969 + 3 ^ 40 * 5187307 * 2
def baseEnd_5187307 : Nat := 887860597810747123735505

theorem tailTrace_5187307 : CollatzResearch.WordTrace tailWord_5187307 prefixEnd_5187307 887860597810747123735505 := by
  unfold tailWord_5187307
  simp only [CollatzResearch.WordTrace]
  refine ⟨189196629418280135348896175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126131086278853423565930783 189196629418280135348896175)
  ·
    refine ⟨283794944127420203023344263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189196629418280135348896175 283794944127420203023344263)
    ·
      refine ⟨425692416191130304535016395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283794944127420203023344263 425692416191130304535016395)
      ·
        refine ⟨638538624286695456802524593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425692416191130304535016395 638538624286695456802524593)
        ·
          refine ⟨478903968215021592601893445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638538624286695456802524593 478903968215021592601893445)
          ·
            refine ⟨89794494040316548612855021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 478903968215021592601893445 89794494040316548612855021)
            ·
              refine ⟨33672935265118705729820633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89794494040316548612855021 33672935265118705729820633)
              ·
                refine ⟨25254701448839029297365475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33672935265118705729820633 25254701448839029297365475)
                ·
                  refine ⟨37882052173258543946048213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25254701448839029297365475 37882052173258543946048213)
                  ·
                    refine ⟨887860597810747123735505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37882052173258543946048213 887860597810747123735505)
                    ·
                      rfl

theorem cell23_5187307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 7].length) (baseStart_5187307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187307 prefixEnd_5187307 := by exact prefixLift 5187307
  have htrace : WordTrace (prefixWord ++ tailWord_5187307) baseStart_5187307 baseEnd_5187307 := by
    simpa [prefixWord, tailWord_5187307, baseEnd_5187307] using wordTrace_append hprefix tailTrace_5187307
  have hstable : (prefixWord ++ tailWord_5187307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187307).length < 2 ^ (prefixWord ++ tailWord_5187307).sum := by decide
  have hdescent : baseEnd_5187307 < baseStart_5187307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187324 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_5187324 : Nat := 118140960795 + 5187324 * 2 ^ 59
def prefixEnd_5187324 : Nat := 4983230072969 + 3 ^ 40 * 5187324 * 2
def baseEnd_5187324 : Nat := 887863507534455934897979

theorem tailTrace_5187324 : CollatzResearch.WordTrace tailWord_5187324 prefixEnd_5187324 887863507534455934897979 := by
  unfold tailWord_5187324
  simp only [CollatzResearch.WordTrace]
  refine ⟨94598624729609273626132513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126131499639479031501510017 94598624729609273626132513)
  ·
    refine ⟨70948968547206955219599385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94598624729609273626132513 70948968547206955219599385)
    ·
      refine ⟨53211726410405216414699539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70948968547206955219599385 53211726410405216414699539)
      ·
        refine ⟨79817589615607824622049309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53211726410405216414699539 79817589615607824622049309)
        ·
          refine ⟨29931596105852934233268491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79817589615607824622049309 29931596105852934233268491)
          ·
            refine ⟨44897394158779401349902737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29931596105852934233268491 44897394158779401349902737)
            ·
              refine ⟨33673045619084551012427053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44897394158779401349902737 33673045619084551012427053)
              ·
                refine ⟨12627392107156706629660145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33673045619084551012427053 12627392107156706629660145)
                ·
                  refine ⟨9470544080367529972245109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12627392107156706629660145 9470544080367529972245109)
                  ·
                    refine ⟨887863507534455934897979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9470544080367529972245109 887863507534455934897979)
                    ·
                      rfl

theorem cell23_5187324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_5187324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187324 prefixEnd_5187324 := by exact prefixLift 5187324
  have htrace : WordTrace (prefixWord ++ tailWord_5187324) baseStart_5187324 baseEnd_5187324 := by
    simpa [prefixWord, tailWord_5187324, baseEnd_5187324] using wordTrace_append hprefix tailTrace_5187324
  have hstable : (prefixWord ++ tailWord_5187324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187324).length < 2 ^ (prefixWord ++ tailWord_5187324).sum := by decide
  have hdescent : baseEnd_5187324 < baseStart_5187324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187347 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 5]
def baseStart_5187347 : Nat := 118140960795 + 5187347 * 2 ^ 59
def prefixEnd_5187347 : Nat := 4983230072969 + 3 ^ 40 * 5187347 * 2
def baseEnd_5187347 : Nat := 2663602332658421214706331

theorem tailTrace_5187347 : CollatzResearch.WordTrace tailWord_5187347 prefixEnd_5187347 2663602332658421214706331 := by
  unfold tailWord_5187347
  simp only [CollatzResearch.WordTrace]
  refine ⟨189198088338135222180352295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126132058892090148120234863 189198088338135222180352295)
  ·
    refine ⟨283797132507202833270528443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189198088338135222180352295 283797132507202833270528443)
    ·
      refine ⟨425695698760804249905792665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283797132507202833270528443 425695698760804249905792665)
      ·
        refine ⟨319271774070603187429344499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425695698760804249905792665 319271774070603187429344499)
        ·
          refine ⟨478907661105904781144016749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319271774070603187429344499 478907661105904781144016749)
          ·
            refine ⟨179590372914714292929006281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478907661105904781144016749 179590372914714292929006281)
            ·
              refine ⟨134692779686035719696754711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179590372914714292929006281 134692779686035719696754711)
              ·
                refine ⟨202039169529053579545132067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134692779686035719696754711 202039169529053579545132067)
                ·
                  refine ⟨303058754293580369317698101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202039169529053579545132067 303058754293580369317698101)
                  ·
                    refine ⟨28411758215023159623534197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 303058754293580369317698101 28411758215023159623534197)
                    ·
                      refine ⟨2663602332658421214706331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28411758215023159623534197 2663602332658421214706331)
                      ·
                        rfl

theorem cell23_5187347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_5187347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187347 prefixEnd_5187347 := by exact prefixLift 5187347
  have htrace : WordTrace (prefixWord ++ tailWord_5187347) baseStart_5187347 baseEnd_5187347 := by
    simpa [prefixWord, tailWord_5187347, baseEnd_5187347] using wordTrace_append hprefix tailTrace_5187347
  have hstable : (prefixWord ++ tailWord_5187347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187347).length < 2 ^ (prefixWord ++ tailWord_5187347).sum := by decide
  have hdescent : baseEnd_5187347 < baseStart_5187347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187431 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 1, 5]
def baseStart_5187431 : Nat := 118140960795 + 5187431 * 2 ^ 59
def prefixEnd_5187431 : Nat := 4983230072969 + 3 ^ 40 * 5187431 * 2
def baseEnd_5187431 : Nat := 887881821677799628685315

theorem tailTrace_5187431 : CollatzResearch.WordTrace tailWord_5187431 prefixEnd_5187431 887881821677799628685315 := by
  unfold tailWord_5187431
  simp only [CollatzResearch.WordTrace]
  refine ⟨189201152069830904526410147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126134101379887269684273431 189201152069830904526410147)
  ·
    refine ⟨283801728104746356789615221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189201152069830904526410147 283801728104746356789615221)
    ·
      refine ⟨26606412009819970949026427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 283801728104746356789615221 26606412009819970949026427)
      ·
        refine ⟨39909618014729956423539641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26606412009819970949026427 39909618014729956423539641)
        ·
          refine ⟨29932213511047467317654731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39909618014729956423539641 29932213511047467317654731)
          ·
            refine ⟨44898320266571200976482097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29932213511047467317654731 44898320266571200976482097)
            ·
              refine ⟨33673740199928400732361573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44898320266571200976482097 33673740199928400732361573)
              ·
                refine ⟨6313826287486575137317795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33673740199928400732361573 6313826287486575137317795)
                ·
                  refine ⟨9470739431229862705976693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6313826287486575137317795 9470739431229862705976693)
                  ·
                    refine ⟨887881821677799628685315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9470739431229862705976693 887881821677799628685315)
                    ·
                      rfl

theorem cell23_5187431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_5187431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187431 prefixEnd_5187431 := by exact prefixLift 5187431
  have htrace : WordTrace (prefixWord ++ tailWord_5187431) baseStart_5187431 baseEnd_5187431 := by
    simpa [prefixWord, tailWord_5187431, baseEnd_5187431] using wordTrace_append hprefix tailTrace_5187431
  have hstable : (prefixWord ++ tailWord_5187431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187431).length < 2 ^ (prefixWord ++ tailWord_5187431).sum := by decide
  have hdescent : baseEnd_5187431 < baseStart_5187431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187461 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_5187461 : Nat := 118140960795 + 5187461 * 2 ^ 59
def prefixEnd_5187461 : Nat := 4983230072969 + 3 ^ 40 * 5187461 * 2
def baseEnd_5187461 : Nat := 887886956484344589560269

theorem tailTrace_5187461 : CollatzResearch.WordTrace tailWord_5187461 prefixEnd_5187461 887886956484344589560269 := by
  unfold tailWord_5187461
  simp only [CollatzResearch.WordTrace]
  refine ⟨189202246259722219650002237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126134830839814813100001491 189202246259722219650002237)
  ·
    refine ⟨70950842347395832368750839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189202246259722219650002237 70950842347395832368750839)
    ·
      refine ⟨106426263521093748553126259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70950842347395832368750839 106426263521093748553126259)
      ·
        refine ⟨159639395281640622829689389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106426263521093748553126259 159639395281640622829689389)
        ·
          refine ⟨59864773230615233561133521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159639395281640622829689389 59864773230615233561133521)
          ·
            refine ⟨44898579922961425170850141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59864773230615233561133521 44898579922961425170850141)
            ·
              refine ⟨16836967471110534439068803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44898579922961425170850141 16836967471110534439068803)
              ·
                refine ⟨25255451206665801658603205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16836967471110534439068803 25255451206665801658603205)
                ·
                  refine ⟨4735397101249837810988101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25255451206665801658603205 4735397101249837810988101)
                  ·
                    refine ⟨887886956484344589560269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4735397101249837810988101 887886956484344589560269)
                    ·
                      rfl

theorem cell23_5187461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_5187461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187461 prefixEnd_5187461 := by exact prefixLift 5187461
  have htrace : WordTrace (prefixWord ++ tailWord_5187461) baseStart_5187461 baseEnd_5187461 := by
    simpa [prefixWord, tailWord_5187461, baseEnd_5187461] using wordTrace_append hprefix tailTrace_5187461
  have hstable : (prefixWord ++ tailWord_5187461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187461).length < 2 ^ (prefixWord ++ tailWord_5187461).sum := by decide
  have hdescent : baseEnd_5187461 < baseStart_5187461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187481 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 4]
def baseStart_5187481 : Nat := 118140960795 + 5187481 * 2 ^ 59
def prefixEnd_5187481 : Nat := 4983230072969 + 3 ^ 40 * 5187481 * 2
def baseEnd_5187481 : Nat := 2663671139066123690430715

theorem tailTrace_5187481 : CollatzResearch.WordTrace tailWord_5187481 prefixEnd_5187481 2663671139066123690430715 := by
  unfold tailWord_5187481
  simp only [CollatzResearch.WordTrace]
  refine ⟨189202975719649763065730297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126135317146433175377153531 189202975719649763065730297)
  ·
    refine ⟨141902231789737322299297723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189202975719649763065730297 141902231789737322299297723)
    ·
      refine ⟨212853347684605983448946585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141902231789737322299297723 212853347684605983448946585)
      ·
        refine ⟨159640010763454487586709939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212853347684605983448946585 159640010763454487586709939)
        ·
          refine ⟨239460016145181731380064909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159640010763454487586709939 239460016145181731380064909)
          ·
            refine ⟨89797506054443149267524341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239460016145181731380064909 89797506054443149267524341)
            ·
              refine ⟨8418516192604045243830407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89797506054443149267524341 8418516192604045243830407)
              ·
                refine ⟨12627774288906067865745611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8418516192604045243830407 12627774288906067865745611)
                ·
                  refine ⟨18941661433359101798618417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12627774288906067865745611 18941661433359101798618417)
                  ·
                    refine ⟨14206246075019326348963813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18941661433359101798618417 14206246075019326348963813)
                    ·
                      refine ⟨2663671139066123690430715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14206246075019326348963813 2663671139066123690430715)
                      ·
                        rfl

theorem cell23_5187481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_5187481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187481 prefixEnd_5187481 := by exact prefixLift 5187481
  have htrace : WordTrace (prefixWord ++ tailWord_5187481) baseStart_5187481 baseEnd_5187481 := by
    simpa [prefixWord, tailWord_5187481, baseEnd_5187481] using wordTrace_append hprefix tailTrace_5187481
  have hstable : (prefixWord ++ tailWord_5187481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187481).length < 2 ^ (prefixWord ++ tailWord_5187481).sum := by decide
  have hdescent : baseEnd_5187481 < baseStart_5187481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187485 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_5187485 : Nat := 118140960795 + 5187485 * 2 ^ 59
def prefixEnd_5187485 : Nat := 4983230072969 + 3 ^ 40 * 5187485 * 2
def baseEnd_5187485 : Nat := 2663673192988741674780697

theorem tailTrace_5187485 : CollatzResearch.WordTrace tailWord_5187485 prefixEnd_5187485 2663673192988741674780697 := by
  unfold tailWord_5187485
  simp only [CollatzResearch.WordTrace]
  refine ⟨189203121611635271748875909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126135414407756847832583939 189203121611635271748875909)
  ·
    refine ⟨35475585302181613452914233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189203121611635271748875909 35475585302181613452914233)
    ·
      refine ⟨26606688976636210089685675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35475585302181613452914233 26606688976636210089685675)
      ·
        refine ⟨39910033464954315134528513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26606688976636210089685675 39910033464954315134528513)
        ·
          refine ⟨29932525098715736350896385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39910033464954315134528513 29932525098715736350896385)
          ·
            refine ⟨22449393824036802263172289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29932525098715736350896385 22449393824036802263172289)
            ·
              refine ⟨16837045368027601697379217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22449393824036802263172289 16837045368027601697379217)
              ·
                refine ⟨12627784026020701273034413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16837045368027601697379217 12627784026020701273034413)
                ·
                  refine ⟨4735419009757762977387905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12627784026020701273034413 4735419009757762977387905)
                  ·
                    refine ⟨3551564257318322233040929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4735419009757762977387905 3551564257318322233040929)
                    ·
                      refine ⟨2663673192988741674780697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551564257318322233040929 2663673192988741674780697)
                      ·
                        rfl

theorem cell23_5187485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_5187485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187485 prefixEnd_5187485 := by exact prefixLift 5187485
  have htrace : WordTrace (prefixWord ++ tailWord_5187485) baseStart_5187485 baseEnd_5187485 := by
    simpa [prefixWord, tailWord_5187485, baseEnd_5187485] using wordTrace_append hprefix tailTrace_5187485
  have hstable : (prefixWord ++ tailWord_5187485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187485).length < 2 ^ (prefixWord ++ tailWord_5187485).sum := by decide
  have hdescent : baseEnd_5187485 < baseStart_5187485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187496 : List Nat := [2, 1, 6, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5187496 : Nat := 118140960795 + 5187496 * 2 ^ 59
def prefixEnd_5187496 : Nat := 4983230072969 + 3 ^ 40 * 5187496 * 2
def baseEnd_5187496 : Nat := 2663678841275941131743147

theorem tailTrace_5187496 : CollatzResearch.WordTrace tailWord_5187496 prefixEnd_5187496 2663678841275941131743147 := by
  unfold tailWord_5187496
  simp only [CollatzResearch.WordTrace]
  refine ⟨94601761407297710313763171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126135681876396947085017561 94601761407297710313763171)
  ·
    refine ⟨141902642110946565470644757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94601761407297710313763171 141902642110946565470644757)
    ·
      refine ⟨6651686348950620256436473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 141902642110946565470644757 6651686348950620256436473)
      ·
        refine ⟨4988764761712965192327355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6651686348950620256436473 4988764761712965192327355)
        ·
          refine ⟨7483147142569447788491033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988764761712965192327355 7483147142569447788491033)
          ·
            refine ⟨5612360356927085841368275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7483147142569447788491033 5612360356927085841368275)
            ·
              refine ⟨8418540535390628762052413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5612360356927085841368275 8418540535390628762052413)
              ·
                refine ⟨3156952700771485785769655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8418540535390628762052413 3156952700771485785769655)
                ·
                  refine ⟨4735429051157228678654483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156952700771485785769655 4735429051157228678654483)
                  ·
                    refine ⟨7103143576735843017981725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4735429051157228678654483 7103143576735843017981725)
                    ·
                      refine ⟨2663678841275941131743147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7103143576735843017981725 2663678841275941131743147)
                      ·
                        rfl

theorem cell23_5187496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5187496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187496 prefixEnd_5187496 := by exact prefixLift 5187496
  have htrace : WordTrace (prefixWord ++ tailWord_5187496) baseStart_5187496 baseEnd_5187496 := by
    simpa [prefixWord, tailWord_5187496, baseEnd_5187496] using wordTrace_append hprefix tailTrace_5187496
  have hstable : (prefixWord ++ tailWord_5187496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187496).length < 2 ^ (prefixWord ++ tailWord_5187496).sum := by decide
  have hdescent : baseEnd_5187496 < baseStart_5187496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187545 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 3, 3, 2]
def baseStart_5187545 : Nat := 118140960795 + 5187545 * 2 ^ 59
def prefixEnd_5187545 : Nat := 4983230072969 + 3 ^ 40 * 5187545 * 2
def baseEnd_5187545 : Nat := 2663704001828011440030421

theorem tailTrace_5187545 : CollatzResearch.WordTrace tailWord_5187545 prefixEnd_5187545 2663704001828011440030421 := by
  unfold tailWord_5187545
  simp only [CollatzResearch.WordTrace]
  refine ⟨189205309991417901996060089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126136873327611934664040059 189205309991417901996060089)
  ·
    refine ⟨141903982493563426497045067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189205309991417901996060089 141903982493563426497045067)
    ·
      refine ⟨212855973740345139745567601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141903982493563426497045067 212855973740345139745567601)
      ·
        refine ⟨159641980305258854809175701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212855973740345139745567601 159641980305258854809175701)
        ·
          refine ⟨7483217826809008819180111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159641980305258854809175701 7483217826809008819180111)
          ·
            refine ⟨11224826740213513228770167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483217826809008819180111 11224826740213513228770167)
            ·
              refine ⟨16837240110320269843155251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11224826740213513228770167 16837240110320269843155251)
              ·
                refine ⟨25255860165480404764732877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16837240110320269843155251 25255860165480404764732877)
                ·
                  refine ⟨9470947562055151786774829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25255860165480404764732877 9470947562055151786774829)
                  ·
                    refine ⟨3551605335770681920040561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9470947562055151786774829 3551605335770681920040561)
                    ·
                      refine ⟨2663704001828011440030421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551605335770681920040561 2663704001828011440030421)
                      ·
                        rfl

theorem cell23_5187545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_5187545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187545 prefixEnd_5187545 := by exact prefixLift 5187545
  have htrace : WordTrace (prefixWord ++ tailWord_5187545) baseStart_5187545 baseEnd_5187545 := by
    simpa [prefixWord, tailWord_5187545, baseEnd_5187545] using wordTrace_append hprefix tailTrace_5187545
  have hstable : (prefixWord ++ tailWord_5187545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187545).length < 2 ^ (prefixWord ++ tailWord_5187545).sum := by decide
  have hdescent : baseEnd_5187545 < baseStart_5187545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187562 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_5187562 : Nat := 118140960795 + 5187562 * 2 ^ 59
def prefixEnd_5187562 : Nat := 4983230072969 + 3 ^ 40 * 5187562 * 2
def baseEnd_5187562 : Nat := 2663712730999137873517843

theorem tailTrace_5187562 : CollatzResearch.WordTrace tailWord_5187562 prefixEnd_5187562 2663712730999137873517843 := by
  unfold tailWord_5187562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47301482508089078474857235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126137286688237542599619293 47301482508089078474857235)
  ·
    refine ⟨70952223762133617712285853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47301482508089078474857235 70952223762133617712285853)
    ·
      refine ⟨26607083910800106642107195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70952223762133617712285853 26607083910800106642107195)
      ·
        refine ⟨39910625866200159963160793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26607083910800106642107195 39910625866200159963160793)
        ·
          refine ⟨29932969399650119972370595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39910625866200159963160793 29932969399650119972370595)
          ·
            refine ⟨44899454099475179958555893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29932969399650119972370595 44899454099475179958555893)
            ·
              refine ⟨4209323821825798121114615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44899454099475179958555893 4209323821825798121114615)
              ·
                refine ⟨6313985732738697181671923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209323821825798121114615 6313985732738697181671923)
                ·
                  refine ⟨9470978599108045772507885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6313985732738697181671923 9470978599108045772507885)
                  ·
                    refine ⟨3551616974665517164690457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9470978599108045772507885 3551616974665517164690457)
                    ·
                      refine ⟨2663712730999137873517843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551616974665517164690457 2663712730999137873517843)
                      ·
                        rfl

theorem cell23_5187562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_5187562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187562 prefixEnd_5187562 := by exact prefixLift 5187562
  have htrace : WordTrace (prefixWord ++ tailWord_5187562) baseStart_5187562 baseEnd_5187562 := by
    simpa [prefixWord, tailWord_5187562, baseEnd_5187562] using wordTrace_append hprefix tailTrace_5187562
  have hstable : (prefixWord ++ tailWord_5187562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187562).length < 2 ^ (prefixWord ++ tailWord_5187562).sum := by decide
  have hdescent : baseEnd_5187562 < baseStart_5187562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187611 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 2, 5]
def baseStart_5187611 : Nat := 118140960795 + 5187611 * 2 ^ 59
def prefixEnd_5187611 : Nat := 4983230072969 + 3 ^ 40 * 5187611 * 2
def baseEnd_5187611 : Nat := 887912630517069393935039

theorem tailTrace_5187611 : CollatzResearch.WordTrace tailWord_5187611 prefixEnd_5187611 887912630517069393935039 := by
  unfold tailWord_5187611
  simp only [CollatzResearch.WordTrace]
  refine ⟨189207717209178795267962687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126138478139452530178641791 189207717209178795267962687)
  ·
    refine ⟨283811575813768192901944031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189207717209178795267962687 283811575813768192901944031)
    ·
      refine ⟨425717363720652289352916047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283811575813768192901944031 425717363720652289352916047)
      ·
        refine ⟨638576045580978434029374071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425717363720652289352916047 638576045580978434029374071)
        ·
          refine ⟨957864068371467651044061107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638576045580978434029374071 957864068371467651044061107)
          ·
            refine ⟨1436796102557201476566091661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957864068371467651044061107 1436796102557201476566091661)
            ·
              refine ⟨538798538458950553712284373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1436796102557201476566091661 538798538458950553712284373)
              ·
                refine ⟨12628090745131653602631665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 538798538458950553712284373 12628090745131653602631665)
                ·
                  refine ⟨9471068058848740201973749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12628090745131653602631665 9471068058848740201973749)
                  ·
                    refine ⟨887912630517069393935039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9471068058848740201973749 887912630517069393935039)
                    ·
                      rfl

theorem cell23_5187611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 5].length) (baseStart_5187611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187611 prefixEnd_5187611 := by exact prefixLift 5187611
  have htrace : WordTrace (prefixWord ++ tailWord_5187611) baseStart_5187611 baseEnd_5187611 := by
    simpa [prefixWord, tailWord_5187611, baseEnd_5187611] using wordTrace_append hprefix tailTrace_5187611
  have hstable : (prefixWord ++ tailWord_5187611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187611).length < 2 ^ (prefixWord ++ tailWord_5187611).sum := by decide
  have hdescent : baseEnd_5187611 < baseStart_5187611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187638 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5187638 : Nat := 118140960795 + 5187638 * 2 ^ 59
def prefixEnd_5187638 : Nat := 4983230072969 + 3 ^ 40 * 5187638 * 2
def baseEnd_5187638 : Nat := 2663751755528879576167493

theorem tailTrace_5187638 : CollatzResearch.WordTrace tailWord_5187638 prefixEnd_5187638 2663751755528879576167493 := by
  unfold tailWord_5187638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11825543873755061179949723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126139134653387319252797045 11825543873755061179949723)
  ·
    refine ⟨17738315810632591769924585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11825543873755061179949723 17738315810632591769924585)
    ·
      refine ⟨13303736857974443827443439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17738315810632591769924585 13303736857974443827443439)
      ·
        refine ⟨19955605286961665741165159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13303736857974443827443439 19955605286961665741165159)
        ·
          refine ⟨29933407930442498611747739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19955605286961665741165159 29933407930442498611747739)
          ·
            refine ⟨44900111895663747917621609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29933407930442498611747739 44900111895663747917621609)
            ·
              refine ⟨33675083921747810938216207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44900111895663747917621609 33675083921747810938216207)
              ·
                refine ⟨50512625882621716407324311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33675083921747810938216207 50512625882621716407324311)
                ·
                  refine ⟨75768938823932574610986467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50512625882621716407324311 75768938823932574610986467)
                  ·
                    refine ⟨113653408235898861916479701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75768938823932574610986467 113653408235898861916479701)
                    ·
                      refine ⟨2663751755528879576167493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113653408235898861916479701 2663751755528879576167493)
                      ·
                        rfl

theorem cell23_5187638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5187638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187638 prefixEnd_5187638 := by exact prefixLift 5187638
  have htrace : WordTrace (prefixWord ++ tailWord_5187638) baseStart_5187638 baseEnd_5187638 := by
    simpa [prefixWord, tailWord_5187638, baseEnd_5187638] using wordTrace_append hprefix tailTrace_5187638
  have hstable : (prefixWord ++ tailWord_5187638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187638).length < 2 ^ (prefixWord ++ tailWord_5187638).sum := by decide
  have hdescent : baseEnd_5187638 < baseStart_5187638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187671 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 8]
def baseStart_5187671 : Nat := 118140960795 + 5187671 * 2 ^ 59
def prefixEnd_5187671 : Nat := 4983230072969 + 3 ^ 40 * 5187671 * 2
def baseEnd_5187671 : Nat := 295974300043386438561649

theorem tailTrace_5187671 : CollatzResearch.WordTrace tailWord_5187671 prefixEnd_5187671 295974300043386438561649 := by
  unfold tailWord_5187671
  simp only [CollatzResearch.WordTrace]
  refine ⟨189209905588961425515146867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126139937059307617010097911 189209905588961425515146867)
  ·
    refine ⟨283814858383442138272720301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189209905588961425515146867 283814858383442138272720301)
    ·
      refine ⟨106430571893790801852270113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283814858383442138272720301 106430571893790801852270113)
      ·
        refine ⟨79822928920343101389202585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106430571893790801852270113 79822928920343101389202585)
        ·
          refine ⟨59867196690257326041901939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79822928920343101389202585 59867196690257326041901939)
          ·
            refine ⟨89800795035385989062852909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59867196690257326041901939 89800795035385989062852909)
            ·
              refine ⟨33675298138269745898569841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89800795035385989062852909 33675298138269745898569841)
              ·
                refine ⟨25256473603702309423927381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33675298138269745898569841 25256473603702309423927381)
                ·
                  refine ⟨295974300043386438561649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25256473603702309423927381 295974300043386438561649)
                  ·
                    rfl

theorem cell23_5187671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 8].length) (baseStart_5187671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187671 prefixEnd_5187671 := by exact prefixLift 5187671
  have htrace : WordTrace (prefixWord ++ tailWord_5187671) baseStart_5187671 baseEnd_5187671 := by
    simpa [prefixWord, tailWord_5187671, baseEnd_5187671] using wordTrace_append hprefix tailTrace_5187671
  have hstable : (prefixWord ++ tailWord_5187671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187671).length < 2 ^ (prefixWord ++ tailWord_5187671).sum := by decide
  have hdescent : baseEnd_5187671 < baseStart_5187671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187682 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5187682 : Nat := 118140960795 + 5187682 * 2 ^ 59
def prefixEnd_5187682 : Nat := 4983230072969 + 3 ^ 40 * 5187682 * 2
def baseEnd_5187682 : Nat := 2663774348677677404017291

theorem tailTrace_5187682 : CollatzResearch.WordTrace tailWord_5187682 prefixEnd_5187682 2663774348677677404017291 := by
  unfold tailWord_5187682
  simp only [CollatzResearch.WordTrace]
  refine ⟨47302576697980393598449325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126140204527947716262531533 47302576697980393598449325)
  ·
    refine ⟨17738466261742647599418497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47302576697980393598449325 17738466261742647599418497)
    ·
      refine ⟨13303849696306985699563873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17738466261742647599418497 13303849696306985699563873)
      ·
        refine ⟨9977887272230239274672905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13303849696306985699563873 9977887272230239274672905)
        ·
          refine ⟨7483415454172679456004679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9977887272230239274672905 7483415454172679456004679)
          ·
            refine ⟨11225123181259019184007019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483415454172679456004679 11225123181259019184007019)
            ·
              refine ⟨16837684771888528776010529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11225123181259019184007019 16837684771888528776010529)
              ·
                refine ⟨12628263578916396582007897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16837684771888528776010529 12628263578916396582007897)
                ·
                  refine ⟨9471197684187297436505923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12628263578916396582007897 9471197684187297436505923)
                  ·
                    refine ⟨14206796526280946154758885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9471197684187297436505923 14206796526280946154758885)
                    ·
                      refine ⟨2663774348677677404017291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14206796526280946154758885 2663774348677677404017291)
                      ·
                        rfl

theorem cell23_5187682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5187682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187682 prefixEnd_5187682 := by exact prefixLift 5187682
  have htrace : WordTrace (prefixWord ++ tailWord_5187682) baseStart_5187682 baseEnd_5187682 := by
    simpa [prefixWord, tailWord_5187682, baseEnd_5187682] using wordTrace_append hprefix tailTrace_5187682
  have hstable : (prefixWord ++ tailWord_5187682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187682).length < 2 ^ (prefixWord ++ tailWord_5187682).sum := by decide
  have hdescent : baseEnd_5187682 < baseStart_5187682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187685 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_5187685 : Nat := 118140960795 + 5187685 * 2 ^ 59
def prefixEnd_5187685 : Nat := 4983230072969 + 3 ^ 40 * 5187685 * 2
def baseEnd_5187685 : Nat := 2663775889119640892279777

theorem tailTrace_5187685 : CollatzResearch.WordTrace tailWord_5187685 prefixEnd_5187685 2663775889119640892279777 := by
  unfold tailWord_5187685
  simp only [CollatzResearch.WordTrace]
  refine ⟨189210416210910705906156509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126140277473940470604104339 189210416210910705906156509)
  ·
    refine ⟨70953906079091514714808691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189210416210910705906156509 70953906079091514714808691)
    ·
      refine ⟨106430859118637272072213037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70953906079091514714808691 106430859118637272072213037)
      ·
        refine ⟨39911572169488977027079889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106430859118637272072213037 39911572169488977027079889)
        ·
          refine ⟨29933679127116732770309917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39911572169488977027079889 29933679127116732770309917)
          ·
            refine ⟨11225129672668774788866219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29933679127116732770309917 11225129672668774788866219)
            ·
              refine ⟨16837694509003162183299329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11225129672668774788866219 16837694509003162183299329)
              ·
                refine ⟨12628270881752371637474497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16837694509003162183299329 12628270881752371637474497)
                ·
                  refine ⟨9471203161314278728105873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12628270881752371637474497 9471203161314278728105873)
                  ·
                    refine ⟨7103402370985709046079405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9471203161314278728105873 7103402370985709046079405)
                    ·
                      refine ⟨2663775889119640892279777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7103402370985709046079405 2663775889119640892279777)
                      ·
                        rfl

theorem cell23_5187685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_5187685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187685 prefixEnd_5187685 := by exact prefixLift 5187685
  have htrace : WordTrace (prefixWord ++ tailWord_5187685) baseStart_5187685 baseEnd_5187685 := by
    simpa [prefixWord, tailWord_5187685, baseEnd_5187685] using wordTrace_append hprefix tailTrace_5187685
  have hstable : (prefixWord ++ tailWord_5187685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187685).length < 2 ^ (prefixWord ++ tailWord_5187685).sum := by decide
  have hdescent : baseEnd_5187685 < baseStart_5187685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187705 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 6]
def baseStart_5187705 : Nat := 118140960795 + 5187705 * 2 ^ 59
def prefixEnd_5187705 : Nat := 4983230072969 + 3 ^ 40 * 5187705 * 2
def baseEnd_5187705 : Nat := 295976239859192312669965

theorem tailTrace_5187705 : CollatzResearch.WordTrace tailWord_5187705 prefixEnd_5187705 295976239859192312669965 := by
  unfold tailWord_5187705
  simp only [CollatzResearch.WordTrace]
  refine ⟨189211145670838249321884569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126140763780558832881256379 189211145670838249321884569)
  ·
    refine ⟨141908359253128686991413427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189211145670838249321884569 141908359253128686991413427)
    ·
      refine ⟨212862538879693030487120141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141908359253128686991413427 212862538879693030487120141)
      ·
        refine ⟨79823452079884886432670053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212862538879693030487120141 79823452079884886432670053)
        ·
          refine ⟨14966897264978416206125635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79823452079884886432670053 14966897264978416206125635)
          ·
            refine ⟨22450345897467624309188453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14966897264978416206125635 22450345897467624309188453)
            ·
              refine ⟨4209439855775179557972835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22450345897467624309188453 4209439855775179557972835)
              ·
                refine ⟨6314159783662769336959253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209439855775179557972835 6314159783662769336959253)
                ·
                  refine ⟨295976239859192312669965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6314159783662769336959253 295976239859192312669965)
                  ·
                    rfl

theorem cell23_5187705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 6].length) (baseStart_5187705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187705 prefixEnd_5187705 := by exact prefixLift 5187705
  have htrace : WordTrace (prefixWord ++ tailWord_5187705) baseStart_5187705 baseEnd_5187705 := by
    simpa [prefixWord, tailWord_5187705, baseEnd_5187705] using wordTrace_append hprefix tailTrace_5187705
  have hstable : (prefixWord ++ tailWord_5187705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187705).length < 2 ^ (prefixWord ++ tailWord_5187705).sum := by decide
  have hdescent : baseEnd_5187705 < baseStart_5187705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187775 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 3]
def baseStart_5187775 : Nat := 118140960795 + 5187775 * 2 ^ 59
def prefixEnd_5187775 : Nat := 4983230072969 + 3 ^ 40 * 5187775 * 2
def baseEnd_5187775 : Nat := 2663822102378545540154363

theorem tailTrace_5187775 : CollatzResearch.WordTrace tailWord_5187775 prefixEnd_5187775 2663822102378545540154363 := by
  unfold tailWord_5187775
  simp only [CollatzResearch.WordTrace]
  refine ⟨189213698780584651276932779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126142465853723100851288519 189213698780584651276932779)
  ·
    refine ⟨283820548170876976915399169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189213698780584651276932779 283820548170876976915399169)
    ·
      refine ⟨212865411128157732686549377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283820548170876976915399169 212865411128157732686549377)
      ·
        refine ⟨159649058346118299514912033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212865411128157732686549377 159649058346118299514912033)
        ·
          refine ⟨119736793759588724636184025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159649058346118299514912033 119736793759588724636184025)
          ·
            refine ⟨89802595319691543477138019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119736793759588724636184025 89802595319691543477138019)
            ·
              refine ⟨134703892979537315215707029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89802595319691543477138019 134703892979537315215707029)
              ·
                refine ⟨6314244983415811650736267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134703892979537315215707029 6314244983415811650736267)
                ·
                  refine ⟨9471367475123717476104401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6314244983415811650736267 9471367475123717476104401)
                  ·
                    refine ⟨7103525606342788107078301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9471367475123717476104401 7103525606342788107078301)
                    ·
                      refine ⟨2663822102378545540154363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7103525606342788107078301 2663822102378545540154363)
                      ·
                        rfl

theorem cell23_5187775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_5187775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187775 prefixEnd_5187775 := by exact prefixLift 5187775
  have htrace : WordTrace (prefixWord ++ tailWord_5187775) baseStart_5187775 baseEnd_5187775 := by
    simpa [prefixWord, tailWord_5187775, baseEnd_5187775] using wordTrace_append hprefix tailTrace_5187775
  have hstable : (prefixWord ++ tailWord_5187775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187775).length < 2 ^ (prefixWord ++ tailWord_5187775).sum := by decide
  have hdescent : baseEnd_5187775 < baseStart_5187775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187922 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_5187922 : Nat := 118140960795 + 5187922 * 2 ^ 59
def prefixEnd_5187922 : Nat := 4983230072969 + 3 ^ 40 * 5187922 * 2
def baseEnd_5187922 : Nat := 2663897584034756465016187

theorem tailTrace_5187922 : CollatzResearch.WordTrace tailWord_5187922 prefixEnd_5187922 2663897584034756465016187 := by
  unfold tailWord_5187922
  simp only [CollatzResearch.WordTrace]
  refine ⟨47304765077763023845633505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126146040207368063588356013 47304765077763023845633505)
  ·
    refine ⟨35478573808322267884225129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47304765077763023845633505 35478573808322267884225129)
    ·
      refine ⟨26608930356241700913168847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35478573808322267884225129 26608930356241700913168847)
      ·
        refine ⟨39913395534362551369753271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26608930356241700913168847 39913395534362551369753271)
        ·
          refine ⟨59870093301543827054629907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39913395534362551369753271 59870093301543827054629907)
          ·
            refine ⟨89805139952315740581944861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59870093301543827054629907 89805139952315740581944861)
            ·
              refine ⟨33676927482118402718229323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89805139952315740581944861 33676927482118402718229323)
              ·
                refine ⟨50515391223177604077343985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33676927482118402718229323 50515391223177604077343985)
                ·
                  refine ⟨37886543417383203058007989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50515391223177604077343985 37886543417383203058007989)
                  ·
                    refine ⟨3551863445379675286688249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37886543417383203058007989 3551863445379675286688249)
                    ·
                      refine ⟨2663897584034756465016187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551863445379675286688249 2663897584034756465016187)
                      ·
                        rfl

theorem cell23_5187922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_5187922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187922 prefixEnd_5187922 := by exact prefixLift 5187922
  have htrace : WordTrace (prefixWord ++ tailWord_5187922) baseStart_5187922 baseEnd_5187922 := by
    simpa [prefixWord, tailWord_5187922, baseEnd_5187922] using wordTrace_append hprefix tailTrace_5187922
  have hstable : (prefixWord ++ tailWord_5187922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187922).length < 2 ^ (prefixWord ++ tailWord_5187922).sum := by decide
  have hdescent : baseEnd_5187922 < baseStart_5187922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187935 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_5187935 : Nat := 118140960795 + 5187935 * 2 ^ 59
def prefixEnd_5187935 : Nat := 4983230072969 + 3 ^ 40 * 5187935 * 2
def baseEnd_5187935 : Nat := 2663904259283264914153627

theorem tailTrace_5187935 : CollatzResearch.WordTrace tailWord_5187935 prefixEnd_5187935 2663904259283264914153627 := by
  unfold tailWord_5187935
  simp only [CollatzResearch.WordTrace]
  refine ⟨189219534460004998602757259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126146356306669999068504839 189219534460004998602757259)
  ·
    refine ⟨283829301690007497904135889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189219534460004998602757259 283829301690007497904135889)
    ·
      refine ⟨212871976267505623428101917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283829301690007497904135889 212871976267505623428101917)
      ·
        refine ⟨79826991100314608785538219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212871976267505623428101917 79826991100314608785538219)
        ·
          refine ⟨119740486650471913178307329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79826991100314608785538219 119740486650471913178307329)
          ·
            refine ⟨89805364987853934883730497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119740486650471913178307329 89805364987853934883730497)
            ·
              refine ⟨67354023740890451162797873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89805364987853934883730497 67354023740890451162797873)
              ·
                refine ⟨50515517805667838372098405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67354023740890451162797873 50515517805667838372098405)
                ·
                  refine ⟨9471659588562719694768451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50515517805667838372098405 9471659588562719694768451)
                  ·
                    refine ⟨14207489382844079542152677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9471659588562719694768451 14207489382844079542152677)
                    ·
                      refine ⟨2663904259283264914153627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14207489382844079542152677 2663904259283264914153627)
                      ·
                        rfl

theorem cell23_5187935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_5187935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187935 prefixEnd_5187935 := by exact prefixLift 5187935
  have htrace : WordTrace (prefixWord ++ tailWord_5187935) baseStart_5187935 baseEnd_5187935 := by
    simpa [prefixWord, tailWord_5187935, baseEnd_5187935] using wordTrace_append hprefix tailTrace_5187935
  have hstable : (prefixWord ++ tailWord_5187935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187935).length < 2 ^ (prefixWord ++ tailWord_5187935).sum := by decide
  have hdescent : baseEnd_5187935 < baseStart_5187935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187952 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 4]
def baseStart_5187952 : Nat := 118140960795 + 5187952 * 2 ^ 59
def prefixEnd_5187952 : Nat := 4983230072969 + 3 ^ 40 * 5187952 * 2
def baseEnd_5187952 : Nat := 2663912988454391347641049

theorem tailTrace_5187952 : CollatzResearch.WordTrace tailWord_5187952 prefixEnd_5187952 2663912988454391347641049 := by
  unfold tailWord_5187952
  simp only [CollatzResearch.WordTrace]
  refine ⟨94610077250471705253063055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126146769667295607004084073 94610077250471705253063055)
  ·
    refine ⟨141915115875707557879594583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94610077250471705253063055 141915115875707557879594583)
    ·
      refine ⟨212872673813561336819391875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141915115875707557879594583 212872673813561336819391875)
      ·
        refine ⟨319309010720342005229087813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212872673813561336819391875 319309010720342005229087813)
        ·
          refine ⟨59870439510064125980453965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319309010720342005229087813 59870439510064125980453965)
          ·
            refine ⟨22451414816274047242670237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59870439510064125980453965 22451414816274047242670237)
            ·
              refine ⟨8419280556102767716001339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22451414816274047242670237 8419280556102767716001339)
              ·
                refine ⟨12628920834154151574002009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8419280556102767716001339 12628920834154151574002009)
                ·
                  refine ⟨9471690625615613680501507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12628920834154151574002009 9471690625615613680501507)
                  ·
                    refine ⟨14207535938423420520752261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9471690625615613680501507 14207535938423420520752261)
                    ·
                      refine ⟨2663912988454391347641049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14207535938423420520752261 2663912988454391347641049)
                      ·
                        rfl

theorem cell23_5187952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_5187952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187952 prefixEnd_5187952 := by exact prefixLift 5187952
  have htrace : WordTrace (prefixWord ++ tailWord_5187952) baseStart_5187952 baseEnd_5187952 := by
    simpa [prefixWord, tailWord_5187952, baseEnd_5187952] using wordTrace_append hprefix tailTrace_5187952
  have hstable : (prefixWord ++ tailWord_5187952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187952).length < 2 ^ (prefixWord ++ tailWord_5187952).sum := by decide
  have hdescent : baseEnd_5187952 < baseStart_5187952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187955 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 3]
def baseStart_5187955 : Nat := 118140960795 + 5187955 * 2 ^ 59
def prefixEnd_5187955 : Nat := 4983230072969 + 3 ^ 40 * 5187955 * 2
def baseEnd_5187955 : Nat := 2663914528896354835903535

theorem tailTrace_5187955 : CollatzResearch.WordTrace tailWord_5187955 prefixEnd_5187955 2663914528896354835903535 := by
  unfold tailWord_5187955
  simp only [CollatzResearch.WordTrace]
  refine ⟨189220263919932542018485319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126146842613288361345656879 189220263919932542018485319)
  ·
    refine ⟨283830395879898813027727979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189220263919932542018485319 283830395879898813027727979)
    ·
      refine ⟨425745593819848219541591969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283830395879898813027727979 425745593819848219541591969)
      ·
        refine ⟨319309195364886164656193977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425745593819848219541591969 319309195364886164656193977)
        ·
          refine ⟨239481896523664623492145483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319309195364886164656193977 239481896523664623492145483)
          ·
            refine ⟨359222844785496935238218225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239481896523664623492145483 359222844785496935238218225)
            ·
              refine ⟨269417133589122701428663669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359222844785496935238218225 269417133589122701428663669)
              ·
                refine ⟨25257856273980253258937219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 269417133589122701428663669 25257856273980253258937219)
                ·
                  refine ⟨37886784410970379888405829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25257856273980253258937219 37886784410970379888405829)
                  ·
                    refine ⟨7103772077056946229076093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37886784410970379888405829 7103772077056946229076093)
                    ·
                      refine ⟨2663914528896354835903535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7103772077056946229076093 2663914528896354835903535)
                      ·
                        rfl

theorem cell23_5187955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_5187955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187955 prefixEnd_5187955 := by exact prefixLift 5187955
  have htrace : WordTrace (prefixWord ++ tailWord_5187955) baseStart_5187955 baseEnd_5187955 := by
    simpa [prefixWord, tailWord_5187955, baseEnd_5187955] using wordTrace_append hprefix tailTrace_5187955
  have hstable : (prefixWord ++ tailWord_5187955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187955).length < 2 ^ (prefixWord ++ tailWord_5187955).sum := by decide
  have hdescent : baseEnd_5187955 < baseStart_5187955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187965 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_5187965 : Nat := 118140960795 + 5187965 * 2 ^ 59
def prefixEnd_5187965 : Nat := 4983230072969 + 3 ^ 40 * 5187965 * 2
def baseEnd_5187965 : Nat := 2663919663702899796778489

theorem tailTrace_5187965 : CollatzResearch.WordTrace tailWord_5187965 prefixEnd_5187965 2663919663702899796778489 := by
  unfold tailWord_5187965
  simp only [CollatzResearch.WordTrace]
  refine ⟨189220628649896313726349349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126147085766597542484232899 189220628649896313726349349)
  ·
    refine ⟨35478867871855558823690503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189220628649896313726349349 35478867871855558823690503)
    ·
      refine ⟨53218301807783338235535755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35478867871855558823690503 53218301807783338235535755)
      ·
        refine ⟨79827452711675007353303633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53218301807783338235535755 79827452711675007353303633)
        ·
          refine ⟨59870589533756255514977725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79827452711675007353303633 59870589533756255514977725)
          ·
            refine ⟨22451471075158595818116647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59870589533756255514977725 22451471075158595818116647)
            ·
              refine ⟨33677206612737893727174971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22451471075158595818116647 33677206612737893727174971)
              ·
                refine ⟨50515809919106840590762457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33677206612737893727174971 50515809919106840590762457)
                ·
                  refine ⟨37886857439330130443071843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50515809919106840590762457 37886857439330130443071843)
                  ·
                    refine ⟨56830286158995195664607765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37886857439330130443071843 56830286158995195664607765)
                    ·
                      refine ⟨2663919663702899796778489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56830286158995195664607765 2663919663702899796778489)
                      ·
                        rfl

theorem cell23_5187965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_5187965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187965 prefixEnd_5187965 := by exact prefixLift 5187965
  have htrace : WordTrace (prefixWord ++ tailWord_5187965) baseStart_5187965 baseEnd_5187965 := by
    simpa [prefixWord, tailWord_5187965, baseEnd_5187965] using wordTrace_append hprefix tailTrace_5187965
  have hstable : (prefixWord ++ tailWord_5187965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187965).length < 2 ^ (prefixWord ++ tailWord_5187965).sum := by decide
  have hdescent : baseEnd_5187965 < baseStart_5187965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187969 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_5187969 : Nat := 118140960795 + 5187969 * 2 ^ 59
def prefixEnd_5187969 : Nat := 4983230072969 + 3 ^ 40 * 5187969 * 2
def baseEnd_5187969 : Nat := 2663921717625517781128471

theorem tailTrace_5187969 : CollatzResearch.WordTrace tailWord_5187969 prefixEnd_5187969 2663921717625517781128471 := by
  unfold tailWord_5187969
  simp only [CollatzResearch.WordTrace]
  refine ⟨189220774541881822409494961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126147183027921214939663307 189220774541881822409494961)
  ·
    refine ⟨141915580906411366807121221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189220774541881822409494961 141915580906411366807121221)
    ·
      refine ⟨26609171419952131276335229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141915580906411366807121221 26609171419952131276335229)
      ·
        refine ⟨9978439282482049228625711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26609171419952131276335229 9978439282482049228625711)
        ·
          refine ⟨14967658923723073842938567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9978439282482049228625711 14967658923723073842938567)
          ·
            refine ⟨22451488385584610764407851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14967658923723073842938567 22451488385584610764407851)
            ·
              refine ⟨33677232578376916146611777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22451488385584610764407851 33677232578376916146611777)
              ·
                refine ⟨25257924433782687109958833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33677232578376916146611777 25257924433782687109958833)
                ·
                  refine ⟨18943443325337015332469125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25257924433782687109958833 18943443325337015332469125)
                  ·
                    refine ⟨3551895623500690374837961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18943443325337015332469125 3551895623500690374837961)
                    ·
                      refine ⟨2663921717625517781128471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551895623500690374837961 2663921717625517781128471)
                      ·
                        rfl

theorem cell23_5187969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_5187969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187969 prefixEnd_5187969 := by exact prefixLift 5187969
  have htrace : WordTrace (prefixWord ++ tailWord_5187969) baseStart_5187969 baseEnd_5187969 := by
    simpa [prefixWord, tailWord_5187969, baseEnd_5187969] using wordTrace_append hprefix tailTrace_5187969
  have hstable : (prefixWord ++ tailWord_5187969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187969).length < 2 ^ (prefixWord ++ tailWord_5187969).sum := by decide
  have hdescent : baseEnd_5187969 < baseStart_5187969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187972 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_5187972 : Nat := 118140960795 + 5187972 * 2 ^ 59
def prefixEnd_5187972 : Nat := 4983230072969 + 3 ^ 40 * 5187972 * 2
def baseEnd_5187972 : Nat := 2663923258067481269390957

theorem tailTrace_5187972 : CollatzResearch.WordTrace tailWord_5187972 prefixEnd_5187972 2663923258067481269390957 := by
  unfold tailWord_5187972
  simp only [CollatzResearch.WordTrace]
  refine ⟨94610441980435476960927085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126147255973913969281236113 94610441980435476960927085)
  ·
    refine ⟨35478915742663303860347657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94610441980435476960927085 35478915742663303860347657)
    ·
      refine ⟨26609186806997477895260743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35478915742663303860347657 26609186806997477895260743)
      ·
        refine ⟨39913780210496216842891115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26609186806997477895260743 39913780210496216842891115)
        ·
          refine ⟨59870670315744325264336673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39913780210496216842891115 59870670315744325264336673)
          ·
            refine ⟨44903002736808243948252505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59870670315744325264336673 44903002736808243948252505)
            ·
              refine ⟨33677252052606182961189379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44903002736808243948252505 33677252052606182961189379)
              ·
                refine ⟨50515878078909274441784069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33677252052606182961189379 50515878078909274441784069)
                ·
                  refine ⟨9471727139795488957834513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50515878078909274441784069 9471727139795488957834513)
                  ·
                    refine ⟨7103795354846616718375885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9471727139795488957834513 7103795354846616718375885)
                    ·
                      refine ⟨2663923258067481269390957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7103795354846616718375885 2663923258067481269390957)
                      ·
                        rfl

theorem cell23_5187972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_5187972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187972 prefixEnd_5187972 := by exact prefixLift 5187972
  have htrace : WordTrace (prefixWord ++ tailWord_5187972) baseStart_5187972 baseEnd_5187972 := by
    simpa [prefixWord, tailWord_5187972, baseEnd_5187972] using wordTrace_append hprefix tailTrace_5187972
  have hstable : (prefixWord ++ tailWord_5187972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187972).length < 2 ^ (prefixWord ++ tailWord_5187972).sum := by decide
  have hdescent : baseEnd_5187972 < baseStart_5187972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187975 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 8]
def baseStart_5187975 : Nat := 118140960795 + 5187975 * 2 ^ 59
def prefixEnd_5187975 : Nat := 4983230072969 + 3 ^ 40 * 5187975 * 2
def baseEnd_5187975 : Nat := 295991644278827195294827

theorem tailTrace_5187975 : CollatzResearch.WordTrace tailWord_5187975 prefixEnd_5187975 295991644278827195294827 := by
  unfold tailWord_5187975
  simp only [CollatzResearch.WordTrace]
  refine ⟨189220993379860085434213379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126147328919906723622808919 189220993379860085434213379)
  ·
    refine ⟨283831490069790128151320069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189220993379860085434213379 283831490069790128151320069)
    ·
      refine ⟨53218404388085649028372513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283831490069790128151320069 53218404388085649028372513)
      ·
        refine ⟨39913803291064236771279385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53218404388085649028372513 39913803291064236771279385)
        ·
          refine ⟨29935352468298177578459539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39913803291064236771279385 29935352468298177578459539)
          ·
            refine ⟨44903028702447266367689309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29935352468298177578459539 44903028702447266367689309)
            ·
              refine ⟨16838635763417724887883491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44903028702447266367689309 16838635763417724887883491)
              ·
                refine ⟨25257953645126587331825237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16838635763417724887883491 25257953645126587331825237)
                ·
                  refine ⟨295991644278827195294827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25257953645126587331825237 295991644278827195294827)
                  ·
                    rfl

theorem cell23_5187975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 8].length) (baseStart_5187975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187975 prefixEnd_5187975 := by exact prefixLift 5187975
  have htrace : WordTrace (prefixWord ++ tailWord_5187975) baseStart_5187975 baseEnd_5187975 := by
    simpa [prefixWord, tailWord_5187975, baseEnd_5187975] using wordTrace_append hprefix tailTrace_5187975
  have hstable : (prefixWord ++ tailWord_5187975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187975).length < 2 ^ (prefixWord ++ tailWord_5187975).sum := by decide
  have hdescent : baseEnd_5187975 < baseStart_5187975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187979 : List Nat := [1, 1, 1, 1, 4, 4, 2, 4, 1, 4]
def baseStart_5187979 : Nat := 118140960795 + 5187979 * 2 ^ 59
def prefixEnd_5187979 : Nat := 4983230072969 + 3 ^ 40 * 5187979 * 2
def baseEnd_5187979 : Nat := 887975617477354247334475

theorem tailTrace_5187979 : CollatzResearch.WordTrace tailWord_5187979 prefixEnd_5187979 887975617477354247334475 := by
  unfold tailWord_5187979
  simp only [CollatzResearch.WordTrace]
  refine ⟨189221139271845594117358991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126147426181230396078239327 189221139271845594117358991)
  ·
    refine ⟨283831708907768391176038487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189221139271845594117358991 283831708907768391176038487)
    ·
      refine ⟨425747563361652586764057731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283831708907768391176038487 425747563361652586764057731)
      ·
        refine ⟨638621345042478880146086597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425747563361652586764057731 638621345042478880146086597)
        ·
          refine ⟨119741502195464790027391237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 638621345042478880146086597 119741502195464790027391237)
          ·
            refine ⟨22451531661649648130135857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119741502195464790027391237 22451531661649648130135857)
            ·
              refine ⟨16838648746237236097601893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22451531661649648130135857 16838648746237236097601893)
              ·
                refine ⟨3157246639919481768300355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16838648746237236097601893 3157246639919481768300355)
                ·
                  refine ⟨4735869959879222652450533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157246639919481768300355 4735869959879222652450533)
                  ·
                    refine ⟨887975617477354247334475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4735869959879222652450533 887975617477354247334475)
                    ·
                      rfl

theorem cell23_5187979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 4].length) (baseStart_5187979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187979 prefixEnd_5187979 := by exact prefixLift 5187979
  have htrace : WordTrace (prefixWord ++ tailWord_5187979) baseStart_5187979 baseEnd_5187979 := by
    simpa [prefixWord, tailWord_5187979, baseEnd_5187979] using wordTrace_append hprefix tailTrace_5187979
  have hstable : (prefixWord ++ tailWord_5187979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187979).length < 2 ^ (prefixWord ++ tailWord_5187979).sum := by decide
  have hdescent : baseEnd_5187979 < baseStart_5187979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5187985 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_5187985 : Nat := 118140960795 + 5187985 * 2 ^ 59
def prefixEnd_5187985 : Nat := 4983230072969 + 3 ^ 40 * 5187985 * 2
def baseEnd_5187985 : Nat := 2663929933315989718528397

theorem tailTrace_5187985 : CollatzResearch.WordTrace tailWord_5187985 prefixEnd_5187985 2663929933315989718528397 := by
  unfold tailWord_5187985
  simp only [CollatzResearch.WordTrace]
  refine ⟨189221358109823857142077409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126147572073215904761384939 189221358109823857142077409)
  ·
    refine ⟨141916018582367892856558057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189221358109823857142077409 141916018582367892856558057)
    ·
      refine ⟨106437013936775919642418543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141916018582367892856558057 106437013936775919642418543)
      ·
        refine ⟨159655520905163879463627815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106437013936775919642418543 159655520905163879463627815)
        ·
          refine ⟨239483281357745819195441723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159655520905163879463627815 239483281357745819195441723)
          ·
            refine ⟨359224922036618728793162585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239483281357745819195441723 359224922036618728793162585)
            ·
              refine ⟨269418691527464046594871939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359224922036618728793162585 269418691527464046594871939)
              ·
                refine ⟨404128037291196069892307909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269418691527464046594871939 404128037291196069892307909)
                ·
                  refine ⟨75774006992099263104807733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404128037291196069892307909 75774006992099263104807733)
                  ·
                    refine ⟨7103813155509305916075725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75774006992099263104807733 7103813155509305916075725)
                    ·
                      refine ⟨2663929933315989718528397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7103813155509305916075725 2663929933315989718528397)
                      ·
                        rfl

theorem cell23_5187985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_5187985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5187985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5187985 prefixEnd_5187985 := by exact prefixLift 5187985
  have htrace : WordTrace (prefixWord ++ tailWord_5187985) baseStart_5187985 baseEnd_5187985 := by
    simpa [prefixWord, tailWord_5187985, baseEnd_5187985] using wordTrace_append hprefix tailTrace_5187985
  have hstable : (prefixWord ++ tailWord_5187985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5187985).length < 2 ^ (prefixWord ++ tailWord_5187985).sum := by decide
  have hdescent : baseEnd_5187985 < baseStart_5187985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5187985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188002 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_5188002 : Nat := 118140960795 + 5188002 * 2 ^ 59
def prefixEnd_5188002 : Nat := 4983230072969 + 3 ^ 40 * 5188002 * 2
def baseEnd_5188002 : Nat := 2663938662487116152015819

theorem tailTrace_5188002 : CollatzResearch.WordTrace tailWord_5188002 prefixEnd_5188002 2663938662487116152015819 := by
  unfold tailWord_5188002
  simp only [CollatzResearch.WordTrace]
  refine ⟨47305494537690567261361565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126147985433841512696964173 47305494537690567261361565)
  ·
    refine ⟨17739560451633962723010587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47305494537690567261361565 17739560451633962723010587)
    ·
      refine ⟨26609340677450944084515881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17739560451633962723010587 26609340677450944084515881)
      ·
        refine ⟨19957005508088208063386911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26609340677450944084515881 19957005508088208063386911)
        ·
          refine ⟨29935508262132312095080367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19957005508088208063386911 29935508262132312095080367)
          ·
            refine ⟨44903262393198468142620551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29935508262132312095080367 44903262393198468142620551)
            ·
              refine ⟨67354893589797702213930827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44903262393198468142620551 67354893589797702213930827)
              ·
                refine ⟨101032340384696553320896241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67354893589797702213930827 101032340384696553320896241)
                ·
                  refine ⟨75774255288522414990672181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101032340384696553320896241 75774255288522414990672181)
                  ·
                    refine ⟨7103836433298976405375517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75774255288522414990672181 7103836433298976405375517)
                    ·
                      refine ⟨2663938662487116152015819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7103836433298976405375517 2663938662487116152015819)
                      ·
                        rfl

theorem cell23_5188002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_5188002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188002 prefixEnd_5188002 := by exact prefixLift 5188002
  have htrace : WordTrace (prefixWord ++ tailWord_5188002) baseStart_5188002 baseEnd_5188002 := by
    simpa [prefixWord, tailWord_5188002, baseEnd_5188002] using wordTrace_append hprefix tailTrace_5188002
  have hstable : (prefixWord ++ tailWord_5188002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188002).length < 2 ^ (prefixWord ++ tailWord_5188002).sum := by decide
  have hdescent : baseEnd_5188002 < baseStart_5188002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188029 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_5188029 : Nat := 118140960795 + 5188029 * 2 ^ 59
def prefixEnd_5188029 : Nat := 4983230072969 + 3 ^ 40 * 5188029 * 2
def baseEnd_5188029 : Nat := 2663952526464787546378195

theorem tailTrace_5188029 : CollatzResearch.WordTrace tailWord_5188029 prefixEnd_5188029 2663952526464787546378195 := by
  unfold tailWord_5188029
  simp only [CollatzResearch.WordTrace]
  refine ⟨189222962921664452656679141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126148641947776301771119427 189222962921664452656679141)
  ·
    refine ⟨35479305547812084873127339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189222962921664452656679141 35479305547812084873127339)
    ·
      refine ⟨53218958321718127309691009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35479305547812084873127339 53218958321718127309691009)
      ·
        refine ⟨39914218741288595482268257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53218958321718127309691009 39914218741288595482268257)
        ·
          refine ⟨29935664055966446611701193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39914218741288595482268257 29935664055966446611701193)
          ·
            refine ⟨22451748041974834958775895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29935664055966446611701193 22451748041974834958775895)
            ·
              refine ⟨33677622062962252438163843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22451748041974834958775895 33677622062962252438163843)
              ·
                refine ⟨50516433094443378657245765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33677622062962252438163843 50516433094443378657245765)
                ·
                  refine ⟨9471831205208133498233581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50516433094443378657245765 9471831205208133498233581)
                  ·
                    refine ⟨3551936701953050061837593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9471831205208133498233581 3551936701953050061837593)
                    ·
                      refine ⟨2663952526464787546378195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551936701953050061837593 2663952526464787546378195)
                      ·
                        rfl

theorem cell23_5188029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_5188029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188029 prefixEnd_5188029 := by exact prefixLift 5188029
  have htrace : WordTrace (prefixWord ++ tailWord_5188029) baseStart_5188029 baseEnd_5188029 := by
    simpa [prefixWord, tailWord_5188029, baseEnd_5188029] using wordTrace_append hprefix tailTrace_5188029
  have hstable : (prefixWord ++ tailWord_5188029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188029).length < 2 ^ (prefixWord ++ tailWord_5188029).sum := by decide
  have hdescent : baseEnd_5188029 < baseStart_5188029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188042 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_5188042 : Nat := 118140960795 + 5188042 * 2 ^ 59
def prefixEnd_5188042 : Nat := 4983230072969 + 3 ^ 40 * 5188042 * 2
def baseEnd_5188042 : Nat := 2663959201713295995515635

theorem tailTrace_5188042 : CollatzResearch.WordTrace tailWord_5188042 prefixEnd_5188042 2663959201713295995515635 := by
  unfold tailWord_5188042
  simp only [CollatzResearch.WordTrace]
  refine ⟨47305859267654338969225595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126148958047078237251268253 47305859267654338969225595)
  ·
    refine ⟨70958788901481508453838393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47305859267654338969225595 70958788901481508453838393)
    ·
      refine ⟨53219091676111131340378795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70958788901481508453838393 53219091676111131340378795)
      ·
        refine ⟨79828637514166697010568193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53219091676111131340378795 79828637514166697010568193)
        ·
          refine ⟨59871478135625022757926145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79828637514166697010568193 59871478135625022757926145)
          ·
            refine ⟨44903608601718767068444609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59871478135625022757926145 44903608601718767068444609)
            ·
              refine ⟨33677706451289075301333457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44903608601718767068444609 33677706451289075301333457)
              ·
                refine ⟨25258279838466806476000093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33677706451289075301333457 25258279838466806476000093)
                ·
                  refine ⟨9471854939425052428500035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25258279838466806476000093 9471854939425052428500035)
                  ·
                    refine ⟨14207782409137578642750053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9471854939425052428500035 14207782409137578642750053)
                    ·
                      refine ⟨2663959201713295995515635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14207782409137578642750053 2663959201713295995515635)
                      ·
                        rfl

theorem cell23_5188042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_5188042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188042 prefixEnd_5188042 := by exact prefixLift 5188042
  have htrace : WordTrace (prefixWord ++ tailWord_5188042) baseStart_5188042 baseEnd_5188042 := by
    simpa [prefixWord, tailWord_5188042, baseEnd_5188042] using wordTrace_append hprefix tailTrace_5188042
  have hstable : (prefixWord ++ tailWord_5188042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188042).length < 2 ^ (prefixWord ++ tailWord_5188042).sum := by decide
  have hdescent : baseEnd_5188042 < baseStart_5188042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188065 : List Nat := [1, 2, 3, 1, 2, 2, 1, 11]
def baseStart_5188065 : Nat := 118140960795 + 5188065 * 2 ^ 59
def prefixEnd_5188065 : Nat := 4983230072969 + 3 ^ 40 * 5188065 * 2
def baseEnd_5188065 : Nat := 98665593028457385389927

theorem tailTrace_5188065 : CollatzResearch.WordTrace tailWord_5188065 prefixEnd_5188065 98665593028457385389927 := by
  unfold tailWord_5188065
  simp only [CollatzResearch.WordTrace]
  refine ⟨189224275949534030804989649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126149517299689353869993099 189224275949534030804989649)
  ·
    refine ⟨141918206962150523103742237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189224275949534030804989649 141918206962150523103742237)
    ·
      refine ⟨53219327610806446163903339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141918206962150523103742237 53219327610806446163903339)
      ·
        refine ⟨79828991416209669245855009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53219327610806446163903339 79828991416209669245855009)
        ·
          refine ⟨59871743562157251934391257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79828991416209669245855009 59871743562157251934391257)
          ·
            refine ⟨44903807671617938950793443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59871743562157251934391257 44903807671617938950793443)
            ·
              refine ⟨67355711507426908426190165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44903807671617938950793443 67355711507426908426190165)
              ·
                refine ⟨98665593028457385389927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 67355711507426908426190165 98665593028457385389927)
                ·
                  rfl

theorem cell23_5188065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 11].length) (baseStart_5188065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188065 prefixEnd_5188065 := by exact prefixLift 5188065
  have htrace : WordTrace (prefixWord ++ tailWord_5188065) baseStart_5188065 baseEnd_5188065 := by
    simpa [prefixWord, tailWord_5188065, baseEnd_5188065] using wordTrace_append hprefix tailTrace_5188065
  have hstable : (prefixWord ++ tailWord_5188065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188065).length < 2 ^ (prefixWord ++ tailWord_5188065).sum := by decide
  have hdescent : baseEnd_5188065 < baseStart_5188065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188069 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_5188069 : Nat := 118140960795 + 5188069 * 2 ^ 59
def prefixEnd_5188069 : Nat := 4983230072969 + 3 ^ 40 * 5188069 * 2
def baseEnd_5188069 : Nat := 887991021896989129959337

theorem tailTrace_5188069 : CollatzResearch.WordTrace tailWord_5188069 prefixEnd_5188069 887991021896989129959337 := by
  unfold tailWord_5188069
  simp only [CollatzResearch.WordTrace]
  refine ⟨189224421841519539488135261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126149614561013026325423507 189224421841519539488135261)
  ·
    refine ⟨70959158190569827308050723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189224421841519539488135261 70959158190569827308050723)
    ·
      refine ⟨106438737285854740962076085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70959158190569827308050723 106438737285854740962076085)
      ·
        refine ⟨9978631620548881965194633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106438737285854740962076085 9978631620548881965194633)
        ·
          refine ⟨7483973715411661473895975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9978631620548881965194633 7483973715411661473895975)
          ·
            refine ⟨11225960573117492210843963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483973715411661473895975 11225960573117492210843963)
            ·
              refine ⟨16838940859676238316265945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11225960573117492210843963 16838940859676238316265945)
              ·
                refine ⟨12629205644757178737199459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16838940859676238316265945 12629205644757178737199459)
                ·
                  refine ⟨18943808467135768105799189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12629205644757178737199459 18943808467135768105799189)
                  ·
                    refine ⟨887991021896989129959337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18943808467135768105799189 887991021896989129959337)
                    ·
                      rfl

theorem cell23_5188069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_5188069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188069 prefixEnd_5188069 := by exact prefixLift 5188069
  have htrace : WordTrace (prefixWord ++ tailWord_5188069) baseStart_5188069 baseEnd_5188069 := by
    simpa [prefixWord, tailWord_5188069, baseEnd_5188069] using wordTrace_append hprefix tailTrace_5188069
  have hstable : (prefixWord ++ tailWord_5188069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188069).length < 2 ^ (prefixWord ++ tailWord_5188069).sum := by decide
  have hdescent : baseEnd_5188069 < baseStart_5188069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188072 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_5188072 : Nat := 118140960795 + 5188072 * 2 ^ 59
def prefixEnd_5188072 : Nat := 4983230072969 + 3 ^ 40 * 5188072 * 2
def baseEnd_5188072 : Nat := 2663974606132930878140497

theorem tailTrace_5188072 : CollatzResearch.WordTrace tailWord_5188072 prefixEnd_5188072 2663974606132930878140497 := by
  unfold tailWord_5188072
  simp only [CollatzResearch.WordTrace]
  refine ⟨94612265630254335500247235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126149687507005780666996313 94612265630254335500247235)
  ·
    refine ⟨141918398445381503250370853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94612265630254335500247235 141918398445381503250370853)
    ·
      refine ⟨26609699708509031859444535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141918398445381503250370853 26609699708509031859444535)
      ·
        refine ⟨39914549562763547789166803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26609699708509031859444535 39914549562763547789166803)
        ·
          refine ⟨59871824344145321683750205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39914549562763547789166803 59871824344145321683750205)
          ·
            refine ⟨22451934129054495631406327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59871824344145321683750205 22451934129054495631406327)
            ·
              refine ⟨33677901193581743447109491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22451934129054495631406327 33677901193581743447109491)
              ·
                refine ⟨50516851790372615170664237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33677901193581743447109491 50516851790372615170664237)
                ·
                  refine ⟨18943819421389730688999089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50516851790372615170664237 18943819421389730688999089)
                  ·
                    refine ⟨14207864566042298016749317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18943819421389730688999089 14207864566042298016749317)
                    ·
                      refine ⟨2663974606132930878140497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14207864566042298016749317 2663974606132930878140497)
                      ·
                        rfl

theorem cell23_5188072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_5188072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188072 prefixEnd_5188072 := by exact prefixLift 5188072
  have htrace : WordTrace (prefixWord ++ tailWord_5188072) baseStart_5188072 baseEnd_5188072 := by
    simpa [prefixWord, tailWord_5188072, baseEnd_5188072] using wordTrace_append hprefix tailTrace_5188072
  have hstable : (prefixWord ++ tailWord_5188072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188072).length < 2 ^ (prefixWord ++ tailWord_5188072).sum := by decide
  have hdescent : baseEnd_5188072 < baseStart_5188072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188082 : List Nat := [3, 2, 1, 4, 2, 11]
def baseStart_5188082 : Nat := 118140960795 + 5188082 * 2 ^ 59
def prefixEnd_5188082 : Nat := 4983230072969 + 3 ^ 40 * 5188082 * 2
def baseEnd_5188082 : Nat := 10962879592343521971257

theorem tailTrace_5188082 : CollatzResearch.WordTrace tailWord_5188082 prefixEnd_5188082 10962879592343521971257 := by
  unfold tailWord_5188082
  simp only [CollatzResearch.WordTrace]
  refine ⟨47306223997618110677089625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126149930660314961805572333 47306223997618110677089625)
  ·
    refine ⟨35479667998213583007817219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47306223997618110677089625 35479667998213583007817219)
    ·
      refine ⟨53219501997320374511725829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35479667998213583007817219 53219501997320374511725829)
      ·
        refine ⟨9978656624497570220948593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53219501997320374511725829 9978656624497570220948593)
        ·
          refine ⟨7483992468373177665711445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9978656624497570220948593 7483992468373177665711445)
          ·
            refine ⟨10962879592343521971257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7483992468373177665711445 10962879592343521971257)
            ·
              rfl

theorem cell23_5188082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 11].length) (baseStart_5188082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188082 prefixEnd_5188082 := by exact prefixLift 5188082
  have htrace : WordTrace (prefixWord ++ tailWord_5188082) baseStart_5188082 baseEnd_5188082 := by
    simpa [prefixWord, tailWord_5188082, baseEnd_5188082] using wordTrace_append hprefix tailTrace_5188082
  have hstable : (prefixWord ++ tailWord_5188082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188082).length < 2 ^ (prefixWord ++ tailWord_5188082).sum := by decide
  have hdescent : baseEnd_5188082 < baseStart_5188082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188086 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_5188086 : Nat := 118140960795 + 5188086 * 2 ^ 59
def prefixEnd_5188086 : Nat := 4983230072969 + 3 ^ 40 * 5188086 * 2
def baseEnd_5188086 : Nat := 887993931620697941121811

theorem tailTrace_5188086 : CollatzResearch.WordTrace tailWord_5188086 prefixEnd_5188086 887993931620697941121811 := by
  unfold tailWord_5188086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11826565117653621961969007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126150027921638634261002741 11826565117653621961969007)
  ·
    refine ⟨17739847676480432942953511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11826565117653621961969007 17739847676480432942953511)
    ·
      refine ⟨26609771514720649414430267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17739847676480432942953511 26609771514720649414430267)
      ·
        refine ⟨39914657272080974121645401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26609771514720649414430267 39914657272080974121645401)
        ·
          refine ⟨29935992954060730591234051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39914657272080974121645401 29935992954060730591234051)
          ·
            refine ⟨44903989431091095886851077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29935992954060730591234051 44903989431091095886851077)
            ·
              refine ⟨8419498018329580478784577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44903989431091095886851077 8419498018329580478784577)
              ·
                refine ⟨6314623513747185359088433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8419498018329580478784577 6314623513747185359088433)
                ·
                  refine ⟨4735967635310389019316325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6314623513747185359088433 4735967635310389019316325)
                  ·
                    refine ⟨887993931620697941121811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4735967635310389019316325 887993931620697941121811)
                    ·
                      rfl

theorem cell23_5188086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_5188086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188086 prefixEnd_5188086 := by exact prefixLift 5188086
  have htrace : WordTrace (prefixWord ++ tailWord_5188086) baseStart_5188086 baseEnd_5188086 := by
    simpa [prefixWord, tailWord_5188086, baseEnd_5188086] using wordTrace_append hprefix tailTrace_5188086
  have hstable : (prefixWord ++ tailWord_5188086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188086).length < 2 ^ (prefixWord ++ tailWord_5188086).sum := by decide
  have hdescent : baseEnd_5188086 < baseStart_5188086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188092 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_5188092 : Nat := 118140960795 + 5188092 * 2 ^ 59
def prefixEnd_5188092 : Nat := 4983230072969 + 3 ^ 40 * 5188092 * 2
def baseEnd_5188092 : Nat := 2663984875746020799890405

theorem tailTrace_5188092 : CollatzResearch.WordTrace tailWord_5188092 prefixEnd_5188092 2663984875746020799890405 := by
  unfold tailWord_5188092
  simp only [CollatzResearch.WordTrace]
  refine ⟨94612630360218107208111265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126150173813624142944148353 94612630360218107208111265)
  ·
    refine ⟨70959472770163580406083449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94612630360218107208111265 70959472770163580406083449)
    ·
      refine ⟨53219604577622685304562587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70959472770163580406083449 53219604577622685304562587)
      ·
        refine ⟨79829406866434027956843881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53219604577622685304562587 79829406866434027956843881)
        ·
          refine ⟨59872055149825520967632911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79829406866434027956843881 59872055149825520967632911)
          ·
            refine ⟨89808082724738281451449367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59872055149825520967632911 89808082724738281451449367)
            ·
              refine ⟨134712124087107422177174051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89808082724738281451449367 134712124087107422177174051)
              ·
                refine ⟨202068186130661133265761077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134712124087107422177174051 202068186130661133265761077)
                ·
                  refine ⟨18943892449749481243665101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202068186130661133265761077 18943892449749481243665101)
                  ·
                    refine ⟨7103959668656055466374413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18943892449749481243665101 7103959668656055466374413)
                    ·
                      refine ⟨2663984875746020799890405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7103959668656055466374413 2663984875746020799890405)
                      ·
                        rfl

theorem cell23_5188092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_5188092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188092 prefixEnd_5188092 := by exact prefixLift 5188092
  have htrace : WordTrace (prefixWord ++ tailWord_5188092) baseStart_5188092 baseEnd_5188092 := by
    simpa [prefixWord, tailWord_5188092, baseEnd_5188092] using wordTrace_append hprefix tailTrace_5188092
  have hstable : (prefixWord ++ tailWord_5188092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188092).length < 2 ^ (prefixWord ++ tailWord_5188092).sum := by decide
  have hdescent : baseEnd_5188092 < baseStart_5188092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188093 : List Nat := [1, 4, 1, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_5188093 : Nat := 118140960795 + 5188093 * 2 ^ 59
def prefixEnd_5188093 : Nat := 4983230072969 + 3 ^ 40 * 5188093 * 2
def baseEnd_5188093 : Nat := 2663985389226675295977901

theorem tailTrace_5188093 : CollatzResearch.WordTrace tailWord_5188093 prefixEnd_5188093 2663985389226675295977901 := by
  unfold tailWord_5188093
  simp only [CollatzResearch.WordTrace]
  refine ⟨189225297193432591587008933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126150198128955061058005955 189225297193432591587008933)
  ·
    refine ⟨35479743223768610922564175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189225297193432591587008933 35479743223768610922564175)
    ·
      refine ⟨53219614835652916383846263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35479743223768610922564175 53219614835652916383846263)
      ·
        refine ⟨79829422253479374575769395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53219614835652916383846263 79829422253479374575769395)
        ·
          refine ⟨119744133380219061863654093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79829422253479374575769395 119744133380219061863654093)
          ·
            refine ⟨44904050017582148198870285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119744133380219061863654093 44904050017582148198870285)
            ·
              refine ⟨16839018756593305574576357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44904050017582148198870285 16839018756593305574576357)
              ·
                refine ⟨3157316016861244795233067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16839018756593305574576357 3157316016861244795233067)
                ·
                  refine ⟨4735974025291867192849601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157316016861244795233067 4735974025291867192849601)
                  ·
                    refine ⟨3551980518968900394637201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4735974025291867192849601 3551980518968900394637201)
                    ·
                      refine ⟨2663985389226675295977901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3551980518968900394637201 2663985389226675295977901)
                      ·
                        rfl

theorem cell23_5188093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_5188093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188093 prefixEnd_5188093 := by exact prefixLift 5188093
  have htrace : WordTrace (prefixWord ++ tailWord_5188093) baseStart_5188093 baseEnd_5188093 := by
    simpa [prefixWord, tailWord_5188093, baseEnd_5188093] using wordTrace_append hprefix tailTrace_5188093
  have hstable : (prefixWord ++ tailWord_5188093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188093).length < 2 ^ (prefixWord ++ tailWord_5188093).sum := by decide
  have hdescent : baseEnd_5188093 < baseStart_5188093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188095 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 1, 9]
def baseStart_5188095 : Nat := 118140960795 + 5188095 * 2 ^ 59
def prefixEnd_5188095 : Nat := 4983230072969 + 3 ^ 40 * 5188095 * 2
def baseEnd_5188095 : Nat := 887995472062661429384297

theorem tailTrace_5188095 : CollatzResearch.WordTrace tailWord_5188095 prefixEnd_5188095 887995472062661429384297 := by
  unfold tailWord_5188095
  simp only [CollatzResearch.WordTrace]
  refine ⟨189225370139425345928581739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126150246759616897285721159 189225370139425345928581739)
  ·
    refine ⟨283838055209138018892872609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189225370139425345928581739 283838055209138018892872609)
    ·
      refine ⟨212878541406853514169654457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283838055209138018892872609 212878541406853514169654457)
      ·
        refine ⟨159658906055140135627240843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212878541406853514169654457 159658906055140135627240843)
        ·
          refine ⟨239488359082710203440861265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159658906055140135627240843 239488359082710203440861265)
          ·
            refine ⟨179616269312032652580645949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239488359082710203440861265 179616269312032652580645949)
            ·
              refine ⟨67356100992012244717742231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179616269312032652580645949 67356100992012244717742231)
              ·
                refine ⟨101034151488018367076613347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67356100992012244717742231 101034151488018367076613347)
                ·
                  refine ⟨151551227232027550614920021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101034151488018367076613347 151551227232027550614920021)
                  ·
                    refine ⟨887995472062661429384297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 151551227232027550614920021 887995472062661429384297)
                    ·
                      rfl

theorem cell23_5188095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_5188095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188095 prefixEnd_5188095 := by exact prefixLift 5188095
  have htrace : WordTrace (prefixWord ++ tailWord_5188095) baseStart_5188095 baseEnd_5188095 := by
    simpa [prefixWord, tailWord_5188095, baseEnd_5188095] using wordTrace_append hprefix tailTrace_5188095
  have hstable : (prefixWord ++ tailWord_5188095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188095).length < 2 ^ (prefixWord ++ tailWord_5188095).sum := by decide
  have hdescent : baseEnd_5188095 < baseStart_5188095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188116 : List Nat := [2, 4, 3, 1, 1, 2, 3, 7]
def baseStart_5188116 : Nat := 118140960795 + 5188116 * 2 ^ 59
def prefixEnd_5188116 : Nat := 4983230072969 + 3 ^ 40 * 5188116 * 2
def baseEnd_5188116 : Nat := 98666562936360322444085

theorem tailTrace_5188116 : CollatzResearch.WordTrace tailWord_5188116 prefixEnd_5188116 98666562936360322444085 := by
  unfold tailWord_5188116
  simp only [CollatzResearch.WordTrace]
  refine ⟨94613068036174633257548101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126150757381566177676730801 94613068036174633257548101)
  ·
    refine ⟨17739950256782743735790269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94613068036174633257548101 17739950256782743735790269)
    ·
      refine ⟨6652481346293528900921351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17739950256782743735790269 6652481346293528900921351)
      ·
        refine ⟨9978722019440293351382027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6652481346293528900921351 9978722019440293351382027)
        ·
          refine ⟨14968083029160440027073041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9978722019440293351382027 14968083029160440027073041)
          ·
            refine ⟨11226062271870330020304781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14968083029160440027073041 11226062271870330020304781)
            ·
              refine ⟨4209773351951373757614293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11226062271870330020304781 4209773351951373757614293)
              ·
                refine ⟨98666562936360322444085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4209773351951373757614293 98666562936360322444085)
                ·
                  rfl

theorem cell23_5188116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 7].length) (baseStart_5188116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188116 prefixEnd_5188116 := by exact prefixLift 5188116
  have htrace : WordTrace (prefixWord ++ tailWord_5188116) baseStart_5188116 baseEnd_5188116 := by
    simpa [prefixWord, tailWord_5188116, baseEnd_5188116] using wordTrace_append hprefix tailTrace_5188116
  have hstable : (prefixWord ++ tailWord_5188116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188116).length < 2 ^ (prefixWord ++ tailWord_5188116).sum := by decide
  have hdescent : baseEnd_5188116 < baseStart_5188116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188172 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 7]
def baseStart_5188172 : Nat := 118140960795 + 5188172 * 2 ^ 59
def prefixEnd_5188172 : Nat := 4983230072969 + 3 ^ 40 * 5188172 * 2
def baseEnd_5188172 : Nat := 296002883799820054098893

theorem tailTrace_5188172 : CollatzResearch.WordTrace tailWord_5188172 prefixEnd_5188172 296002883799820054098893 := by
  unfold tailWord_5188172
  simp only [CollatzResearch.WordTrace]
  refine ⟨94614089280073194039567385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126152119040097592052756513 94614089280073194039567385)
  ·
    refine ⟨70960566960054895529675539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94614089280073194039567385 70960566960054895529675539)
    ·
      refine ⟨106440850440082343294513309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70960566960054895529675539 106440850440082343294513309)
      ·
        refine ⟨39915318915030878735442491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106440850440082343294513309 39915318915030878735442491)
        ·
          refine ⟨59872978372546318103163737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39915318915030878735442491 59872978372546318103163737)
          ·
            refine ⟨44904733779409738577372803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59872978372546318103163737 44904733779409738577372803)
            ·
              refine ⟨67357100669114607866059205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44904733779409738577372803 67357100669114607866059205)
              ·
                refine ⟨12629456375458988974886101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67357100669114607866059205 12629456375458988974886101)
                ·
                  refine ⟨296002883799820054098893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12629456375458988974886101 296002883799820054098893)
                  ·
                    rfl

theorem cell23_5188172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_5188172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188172 prefixEnd_5188172 := by exact prefixLift 5188172
  have htrace : WordTrace (prefixWord ++ tailWord_5188172) baseStart_5188172 baseEnd_5188172 := by
    simpa [prefixWord, tailWord_5188172, baseEnd_5188172] using wordTrace_append hprefix tailTrace_5188172
  have hstable : (prefixWord ++ tailWord_5188172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188172).length < 2 ^ (prefixWord ++ tailWord_5188172).sum := by decide
  have hdescent : baseEnd_5188172 < baseStart_5188172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188206 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_5188206 : Nat := 118140960795 + 5188206 * 2 ^ 59
def prefixEnd_5188206 : Nat := 4983230072969 + 3 ^ 40 * 5188206 * 2
def baseEnd_5188206 : Nat := 296004823615625928207209

theorem tailTrace_5188206 : CollatzResearch.WordTrace tailWord_5188206 prefixEnd_5188206 296004823615625928207209 := by
  unfold tailWord_5188206
  simp only [CollatzResearch.WordTrace]
  refine ⟨23653677330252901485734059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126152945761348807923914981 23653677330252901485734059)
  ·
    refine ⟨35480515995379352228601089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23653677330252901485734059 35480515995379352228601089)
    ·
      refine ⟨26610386996534514171450817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35480515995379352228601089 26610386996534514171450817)
      ·
        refine ⟨19957790247400885628588113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26610386996534514171450817 19957790247400885628588113)
        ·
          refine ⟨14968342685550664221441085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19957790247400885628588113 14968342685550664221441085)
          ·
            refine ⟨5613128507081499083040407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14968342685550664221441085 5613128507081499083040407)
            ·
              refine ⟨8419692760622248624560611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5613128507081499083040407 8419692760622248624560611)
              ·
                refine ⟨12629539140933372936840917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8419692760622248624560611 12629539140933372936840917)
                ·
                  refine ⟨296004823615625928207209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12629539140933372936840917 296004823615625928207209)
                  ·
                    rfl

theorem cell23_5188206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_5188206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188206 prefixEnd_5188206 := by exact prefixLift 5188206
  have htrace : WordTrace (prefixWord ++ tailWord_5188206) baseStart_5188206 baseEnd_5188206 := by
    simpa [prefixWord, tailWord_5188206, baseEnd_5188206] using wordTrace_append hprefix tailTrace_5188206
  have hstable : (prefixWord ++ tailWord_5188206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188206).length < 2 ^ (prefixWord ++ tailWord_5188206).sum := by decide
  have hdescent : baseEnd_5188206 < baseStart_5188206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188239 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 1, 6, 2]
def baseStart_5188239 : Nat := 118140960795 + 5188239 * 2 ^ 59
def prefixEnd_5188239 : Nat := 4983230072969 + 3 ^ 40 * 5188239 * 2
def baseEnd_5188239 : Nat := 2664060357402231724752229

theorem tailTrace_5188239 : CollatzResearch.WordTrace tailWord_5188239 prefixEnd_5188239 2664060357402231724752229 := by
  unfold tailWord_5188239
  simp only [CollatzResearch.WordTrace]
  refine ⟨189230622250903658521823771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126153748167269105681215847 189230622250903658521823771)
  ·
    refine ⟨283845933376355487782735657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189230622250903658521823771 283845933376355487782735657)
    ·
      refine ⟨212884450032266615837051743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283845933376355487782735657 212884450032266615837051743)
      ·
        refine ⟨319326675048399923755577615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212884450032266615837051743 319326675048399923755577615)
        ·
          refine ⟨478990012572599885633366423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319326675048399923755577615 478990012572599885633366423)
          ·
            refine ⟨718485018858899828450049635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478990012572599885633366423 718485018858899828450049635)
            ·
              refine ⟨1077727528288349742675074453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718485018858899828450049635 1077727528288349742675074453)
              ·
                refine ⟨50518477888516394187894115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1077727528288349742675074453 50518477888516394187894115)
                ·
                  refine ⟨75777716832774591281841173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50518477888516394187894115 75777716832774591281841173)
                  ·
                    refine ⟨3552080476536308966336305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75777716832774591281841173 3552080476536308966336305)
                    ·
                      refine ⟨2664060357402231724752229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552080476536308966336305 2664060357402231724752229)
                      ·
                        rfl

theorem cell23_5188239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 6, 2].length) (baseStart_5188239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188239 prefixEnd_5188239 := by exact prefixLift 5188239
  have htrace : WordTrace (prefixWord ++ tailWord_5188239) baseStart_5188239 baseEnd_5188239 := by
    simpa [prefixWord, tailWord_5188239, baseEnd_5188239] using wordTrace_append hprefix tailTrace_5188239
  have hstable : (prefixWord ++ tailWord_5188239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188239).length < 2 ^ (prefixWord ++ tailWord_5188239).sum := by decide
  have hdescent : baseEnd_5188239 < baseStart_5188239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188259 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 3]
def baseStart_5188259 : Nat := 118140960795 + 5188259 * 2 ^ 59
def prefixEnd_5188259 : Nat := 4983230072969 + 3 ^ 40 * 5188259 * 2
def baseEnd_5188259 : Nat := 2664070627015321646502137

theorem tailTrace_5188259 : CollatzResearch.WordTrace tailWord_5188259 prefixEnd_5188259 2664070627015321646502137 := by
  unfold tailWord_5188259
  simp only [CollatzResearch.WordTrace]
  refine ⟨189231351710831201937551831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126154234473887467958367887 189231351710831201937551831)
  ·
    refine ⟨283847027566246802906327747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189231351710831201937551831 283847027566246802906327747)
    ·
      refine ⟨425770541349370204359491621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283847027566246802906327747 425770541349370204359491621)
      ·
        refine ⟨79831976503006913317404679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 425770541349370204359491621 79831976503006913317404679)
        ·
          refine ⟨119747964754510369976107019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79831976503006913317404679 119747964754510369976107019)
          ·
            refine ⟨179621947131765554964160529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119747964754510369976107019 179621947131765554964160529)
            ·
              refine ⟨134716460348824166223120397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179621947131765554964160529 134716460348824166223120397)
              ·
                refine ⟨50518672630809062333670149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134716460348824166223120397 50518672630809062333670149)
                ·
                  refine ⟨9472251118276699187563153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50518672630809062333670149 9472251118276699187563153)
                  ·
                    refine ⟨7104188338707524390672365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9472251118276699187563153 7104188338707524390672365)
                    ·
                      refine ⟨2664070627015321646502137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7104188338707524390672365 2664070627015321646502137)
                      ·
                        rfl

theorem cell23_5188259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_5188259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188259 prefixEnd_5188259 := by exact prefixLift 5188259
  have htrace : WordTrace (prefixWord ++ tailWord_5188259) baseStart_5188259 baseEnd_5188259 := by
    simpa [prefixWord, tailWord_5188259, baseEnd_5188259] using wordTrace_append hprefix tailTrace_5188259
  have hstable : (prefixWord ++ tailWord_5188259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188259).length < 2 ^ (prefixWord ++ tailWord_5188259).sum := by decide
  have hdescent : baseEnd_5188259 < baseStart_5188259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188300 : List Nat := [2, 2, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_5188300 : Nat := 118140960795 + 5188300 * 2 ^ 59
def prefixEnd_5188300 : Nat := 4983230072969 + 3 ^ 40 * 5188300 * 2
def baseEnd_5188300 : Nat := 888030559907385328696483

theorem tailTrace_5188300 : CollatzResearch.WordTrace tailWord_5188300 prefixEnd_5188300 888030559907385328696483 := by
  unfold tailWord_5188300
  simp only [CollatzResearch.WordTrace]
  refine ⟨94616423551841332969897177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126155231402455110626529569 94616423551841332969897177)
  ·
    refine ⟨70962317663880999727422883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94616423551841332969897177 70962317663880999727422883)
    ·
      refine ⟨106443476495821499591134325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70962317663880999727422883 106443476495821499591134325)
      ·
        refine ⟨9979075921483265586668843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106443476495821499591134325 9979075921483265586668843)
        ·
          refine ⟨14968613882224898380003265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979075921483265586668843 14968613882224898380003265)
          ·
            refine ⟨11226460411668673785002449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14968613882224898380003265 11226460411668673785002449)
            ·
              refine ⟨8419845308751505338751837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11226460411668673785002449 8419845308751505338751837)
              ·
                refine ⟨3157441990781814502031939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8419845308751505338751837 3157441990781814502031939)
                ·
                  refine ⟨4736162986172721753047909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157441990781814502031939 4736162986172721753047909)
                  ·
                    refine ⟨888030559907385328696483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4736162986172721753047909 888030559907385328696483)
                    ·
                      rfl

theorem cell23_5188300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_5188300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188300 prefixEnd_5188300 := by exact prefixLift 5188300
  have htrace : WordTrace (prefixWord ++ tailWord_5188300) baseStart_5188300 baseEnd_5188300 := by
    simpa [prefixWord, tailWord_5188300, baseEnd_5188300] using wordTrace_append hprefix tailTrace_5188300
  have hstable : (prefixWord ++ tailWord_5188300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188300).length < 2 ^ (prefixWord ++ tailWord_5188300).sum := by decide
  have hdescent : baseEnd_5188300 < baseStart_5188300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188316 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5188316 : Nat := 118140960795 + 5188316 * 2 ^ 59
def prefixEnd_5188316 : Nat := 4983230072969 + 3 ^ 40 * 5188316 * 2
def baseEnd_5188316 : Nat := 2664099895412627923489375

theorem tailTrace_5188316 : CollatzResearch.WordTrace tailWord_5188316 prefixEnd_5188316 2664099895412627923489375 := by
  unfold tailWord_5188316
  simp only [CollatzResearch.WordTrace]
  refine ⟨94616715335812350336188401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126155620447749800448251201 94616715335812350336188401)
  ·
    refine ⟨70962536501859262752141301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94616715335812350336188401 70962536501859262752141301)
    ·
      refine ⟨6652737797049305883013247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70962536501859262752141301 6652737797049305883013247)
      ·
        refine ⟨9979106695573958824519871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6652737797049305883013247 9979106695573958824519871)
        ·
          refine ⟨14968660043360938236779807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979106695573958824519871 14968660043360938236779807)
          ·
            refine ⟨22452990065041407355169711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14968660043360938236779807 22452990065041407355169711)
            ·
              refine ⟨33679485097562111032754567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22452990065041407355169711 33679485097562111032754567)
              ·
                refine ⟨50519227646343166549131851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33679485097562111032754567 50519227646343166549131851)
                ·
                  refine ⟨75778841469514749823697777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50519227646343166549131851 75778841469514749823697777)
                  ·
                    refine ⟨56834131102136062367773333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75778841469514749823697777 56834131102136062367773333)
                    ·
                      refine ⟨2664099895412627923489375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56834131102136062367773333 2664099895412627923489375)
                      ·
                        rfl

theorem cell23_5188316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5188316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188316 prefixEnd_5188316 := by exact prefixLift 5188316
  have htrace : WordTrace (prefixWord ++ tailWord_5188316) baseStart_5188316 baseEnd_5188316 := by
    simpa [prefixWord, tailWord_5188316, baseEnd_5188316] using wordTrace_append hprefix tailTrace_5188316
  have hstable : (prefixWord ++ tailWord_5188316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188316).length < 2 ^ (prefixWord ++ tailWord_5188316).sum := by decide
  have hdescent : baseEnd_5188316 < baseStart_5188316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188323 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5188323 : Nat := 118140960795 + 5188323 * 2 ^ 59
def prefixEnd_5188323 : Nat := 4983230072969 + 3 ^ 40 * 5188323 * 2
def baseEnd_5188323 : Nat := 2664103489777209396101843

theorem tailTrace_5188323 : CollatzResearch.WordTrace tailWord_5188323 prefixEnd_5188323 2664103489777209396101843 := by
  unfold tailWord_5188323
  simp only [CollatzResearch.WordTrace]
  refine ⟨189233685982599340867881623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126155790655066227245254415 189233685982599340867881623)
  ·
    refine ⟨283850528973899011301822435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189233685982599340867881623 283850528973899011301822435)
    ·
      refine ⟨425775793460848516952733653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283850528973899011301822435 425775793460848516952733653)
      ·
        refine ⟨9979120159238637116079695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 425775793460848516952733653 9979120159238637116079695)
        ·
          refine ⟨14968680238857955674119543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979120159238637116079695 14968680238857955674119543)
          ·
            refine ⟨22453020358286933511179315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14968680238857955674119543 22453020358286933511179315)
            ·
              refine ⟨33679530537430400266768973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22453020358286933511179315 33679530537430400266768973)
              ·
                refine ⟨12629823951536400100038365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33679530537430400266768973 12629823951536400100038365)
                ·
                  refine ⟨4736183981826150037514387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12629823951536400100038365 4736183981826150037514387)
                  ·
                    refine ⟨7104275972739225056271581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4736183981826150037514387 7104275972739225056271581)
                    ·
                      refine ⟨2664103489777209396101843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7104275972739225056271581 2664103489777209396101843)
                      ·
                        rfl

theorem cell23_5188323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5188323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188323 prefixEnd_5188323 := by exact prefixLift 5188323
  have htrace : WordTrace (prefixWord ++ tailWord_5188323) baseStart_5188323 baseEnd_5188323 := by
    simpa [prefixWord, tailWord_5188323, baseEnd_5188323] using wordTrace_append hprefix tailTrace_5188323
  have hstable : (prefixWord ++ tailWord_5188323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188323).length < 2 ^ (prefixWord ++ tailWord_5188323).sum := by decide
  have hdescent : baseEnd_5188323 < baseStart_5188323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188329 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_5188329 : Nat := 118140960795 + 5188329 * 2 ^ 59
def prefixEnd_5188329 : Nat := 4983230072969 + 3 ^ 40 * 5188329 * 2
def baseEnd_5188329 : Nat := 2664106570661136372626815

theorem tailTrace_5188329 : CollatzResearch.WordTrace tailWord_5188329 prefixEnd_5188329 2664106570661136372626815 := by
  unfold tailWord_5188329
  simp only [CollatzResearch.WordTrace]
  refine ⟨189233904820577603892600041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126155936547051735928400027 189233904820577603892600041)
  ·
    refine ⟨141925428615433202919450031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189233904820577603892600041 141925428615433202919450031)
    ·
      refine ⟨212888142923149804379175047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141925428615433202919450031 212888142923149804379175047)
      ·
        refine ⟨319332214384724706568762571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212888142923149804379175047 319332214384724706568762571)
        ·
          refine ⟨478998321577087059853143857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319332214384724706568762571 478998321577087059853143857)
          ·
            refine ⟨359248741182815294889857893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478998321577087059853143857 359248741182815294889857893)
            ·
              refine ⟨67359138971777867791848355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 359248741182815294889857893 67359138971777867791848355)
              ·
                refine ⟨101038708457666801687772533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67359138971777867791848355 101038708457666801687772533)
                ·
                  refine ⟨9472378917906262658228675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101038708457666801687772533 9472378917906262658228675)
                  ·
                    refine ⟨14208568376859393987343013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9472378917906262658228675 14208568376859393987343013)
                    ·
                      refine ⟨2664106570661136372626815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14208568376859393987343013 2664106570661136372626815)
                      ·
                        rfl

theorem cell23_5188329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_5188329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188329 prefixEnd_5188329 := by exact prefixLift 5188329
  have htrace : WordTrace (prefixWord ++ tailWord_5188329) baseStart_5188329 baseEnd_5188329 := by
    simpa [prefixWord, tailWord_5188329, baseEnd_5188329] using wordTrace_append hprefix tailTrace_5188329
  have hstable : (prefixWord ++ tailWord_5188329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188329).length < 2 ^ (prefixWord ++ tailWord_5188329).sum := by decide
  have hdescent : baseEnd_5188329 < baseStart_5188329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188346 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_5188346 : Nat := 118140960795 + 5188346 * 2 ^ 59
def prefixEnd_5188346 : Nat := 4983230072969 + 3 ^ 40 * 5188346 * 2
def baseEnd_5188346 : Nat := 2664115299832262806114237

theorem tailTrace_5188346 : CollatzResearch.WordTrace tailWord_5188346 prefixEnd_5188346 2664115299832262806114237 := by
  unfold tailWord_5188346
  simp only [CollatzResearch.WordTrace]
  refine ⟨47308631215379003948992223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126156349907677343863979261 47308631215379003948992223)
  ·
    refine ⟨70962946823068505923488335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47308631215379003948992223 70962946823068505923488335)
    ·
      refine ⟨106444420234602758885232503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70962946823068505923488335 106444420234602758885232503)
      ·
        refine ⟨159666630351904138327848755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106444420234602758885232503 159666630351904138327848755)
        ·
          refine ⟨239499945527856207491773133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159666630351904138327848755 239499945527856207491773133)
          ·
            refine ⟨89812479572946077809414925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239499945527856207491773133 89812479572946077809414925)
            ·
              refine ⟨33679679839854779178530597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89812479572946077809414925 33679679839854779178530597)
              ·
                refine ⟨6314939969972771095974487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33679679839854779178530597 6314939969972771095974487)
                ·
                  refine ⟨9472409954959156643961731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6314939969972771095974487 9472409954959156643961731)
                  ·
                    refine ⟨14208614932438734965942597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9472409954959156643961731 14208614932438734965942597)
                    ·
                      refine ⟨2664115299832262806114237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14208614932438734965942597 2664115299832262806114237)
                      ·
                        rfl

theorem cell23_5188346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_5188346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188346 prefixEnd_5188346 := by exact prefixLift 5188346
  have htrace : WordTrace (prefixWord ++ tailWord_5188346) baseStart_5188346 baseEnd_5188346 := by
    simpa [prefixWord, tailWord_5188346, baseEnd_5188346] using wordTrace_append hprefix tailTrace_5188346
  have hstable : (prefixWord ++ tailWord_5188346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188346).length < 2 ^ (prefixWord ++ tailWord_5188346).sum := by decide
  have hdescent : baseEnd_5188346 < baseStart_5188346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188349 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_5188349 : Nat := 118140960795 + 5188349 * 2 ^ 59
def prefixEnd_5188349 : Nat := 4983230072969 + 3 ^ 40 * 5188349 * 2
def baseEnd_5188349 : Nat := 2664116840274226294376723

theorem tailTrace_5188349 : CollatzResearch.WordTrace tailWord_5188349 prefixEnd_5188349 2664116840274226294376723 := by
  unfold tailWord_5188349
  simp only [CollatzResearch.WordTrace]
  refine ⟨189234634280505147308328101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126156422853670098205552067 189234634280505147308328101)
  ·
    refine ⟨35481493927594715120311519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189234634280505147308328101 35481493927594715120311519)
    ·
      refine ⟨53222240891392072680467279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35481493927594715120311519 53222240891392072680467279)
      ·
        refine ⟨79833361337088109020700919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53222240891392072680467279 79833361337088109020700919)
        ·
          refine ⟨119750042005632163531051379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79833361337088109020700919 119750042005632163531051379)
          ·
            refine ⟨179625063008448245296577069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119750042005632163531051379 179625063008448245296577069)
            ·
              refine ⟨67359398628168091986216401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179625063008448245296577069 67359398628168091986216401)
              ·
                refine ⟨50519548971126068989662301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67359398628168091986216401 50519548971126068989662301)
                ·
                  refine ⟨18944830864172275871123363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50519548971126068989662301 18944830864172275871123363)
                  ·
                    refine ⟨28417246296258413806685045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18944830864172275871123363 28417246296258413806685045)
                    ·
                      refine ⟨2664116840274226294376723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28417246296258413806685045 2664116840274226294376723)
                      ·
                        rfl

theorem cell23_5188349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_5188349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188349 prefixEnd_5188349 := by exact prefixLift 5188349
  have htrace : WordTrace (prefixWord ++ tailWord_5188349) baseStart_5188349 baseEnd_5188349 := by
    simpa [prefixWord, tailWord_5188349, baseEnd_5188349] using wordTrace_append hprefix tailTrace_5188349
  have hstable : (prefixWord ++ tailWord_5188349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188349).length < 2 ^ (prefixWord ++ tailWord_5188349).sum := by decide
  have hdescent : baseEnd_5188349 < baseStart_5188349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188356 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_5188356 : Nat := 118140960795 + 5188356 * 2 ^ 59
def prefixEnd_5188356 : Nat := 4983230072969 + 3 ^ 40 * 5188356 * 2
def baseEnd_5188356 : Nat := 888040144879602588996397

theorem tailTrace_5188356 : CollatzResearch.WordTrace tailWord_5188356 prefixEnd_5188356 888040144879602588996397 := by
  unfold tailWord_5188356
  simp only [CollatzResearch.WordTrace]
  refine ⟨94617444795739893751916461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126156593060986525002555281 94617444795739893751916461)
  ·
    refine ⟨35481541798402460156968673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94617444795739893751916461 35481541798402460156968673)
    ·
      refine ⟨26611156348801845117726505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35481541798402460156968673 26611156348801845117726505)
      ·
        refine ⟨19958367261601383838294879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26611156348801845117726505 19958367261601383838294879)
        ·
          refine ⟨29937550892402075757442319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19958367261601383838294879 29937550892402075757442319)
          ·
            refine ⟨44906326338603113636163479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29937550892402075757442319 44906326338603113636163479)
            ·
              refine ⟨67359489507904670454245219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44906326338603113636163479 67359489507904670454245219)
              ·
                refine ⟨101039234261857005681367829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67359489507904670454245219 101039234261857005681367829)
                ·
                  refine ⟨4736214106024547141314117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101039234261857005681367829 4736214106024547141314117)
                  ·
                    refine ⟨888040144879602588996397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4736214106024547141314117 888040144879602588996397)
                    ·
                      rfl

theorem cell23_5188356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_5188356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188356 prefixEnd_5188356 := by exact prefixLift 5188356
  have htrace : WordTrace (prefixWord ++ tailWord_5188356) baseStart_5188356 baseEnd_5188356 := by
    simpa [prefixWord, tailWord_5188356, baseEnd_5188356] using wordTrace_append hprefix tailTrace_5188356
  have hstable : (prefixWord ++ tailWord_5188356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188356).length < 2 ^ (prefixWord ++ tailWord_5188356).sum := by decide
  have hdescent : baseEnd_5188356 < baseStart_5188356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188366 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_5188366 : Nat := 118140960795 + 5188366 * 2 ^ 59
def prefixEnd_5188366 : Nat := 4983230072969 + 3 ^ 40 * 5188366 * 2
def baseEnd_5188366 : Nat := 2664125569445352727864145

theorem tailTrace_5188366 : CollatzResearch.WordTrace tailWord_5188366 prefixEnd_5188366 2664125569445352727864145 := by
  unfold tailWord_5188366
  simp only [CollatzResearch.WordTrace]
  refine ⟨23654406790180444901462119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126156836214295706141131301 23654406790180444901462119)
  ·
    refine ⟨35481610185270667352193179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23654406790180444901462119 35481610185270667352193179)
    ·
      refine ⟨53222415277906001028289769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35481610185270667352193179 53222415277906001028289769)
      ·
        refine ⟨39916811458429500771217327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53222415277906001028289769 39916811458429500771217327)
        ·
          refine ⟨59875217187644251156825991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39916811458429500771217327 59875217187644251156825991)
          ·
            refine ⟨89812825781466376735238987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59875217187644251156825991 89812825781466376735238987)
            ·
              refine ⟨134719238672199565102858481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89812825781466376735238987 134719238672199565102858481)
              ·
                refine ⟨101039429004149673827143861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134719238672199565102858481 101039429004149673827143861)
                ·
                  refine ⟨9472446469139031921294737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101039429004149673827143861 9472446469139031921294737)
                  ·
                    refine ⟨7104334851854273940971053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9472446469139031921294737 7104334851854273940971053)
                    ·
                      refine ⟨2664125569445352727864145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7104334851854273940971053 2664125569445352727864145)
                      ·
                        rfl

theorem cell23_5188366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_5188366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188366 prefixEnd_5188366 := by exact prefixLift 5188366
  have htrace : WordTrace (prefixWord ++ tailWord_5188366) baseStart_5188366 baseEnd_5188366 := by
    simpa [prefixWord, tailWord_5188366, baseEnd_5188366] using wordTrace_append hprefix tailTrace_5188366
  have hstable : (prefixWord ++ tailWord_5188366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188366).length < 2 ^ (prefixWord ++ tailWord_5188366).sum := by decide
  have hdescent : baseEnd_5188366 < baseStart_5188366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188379 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 3]
def baseStart_5188379 : Nat := 118140960795 + 5188379 * 2 ^ 59
def prefixEnd_5188379 : Nat := 4983230072969 + 3 ^ 40 * 5188379 * 2
def baseEnd_5188379 : Nat := 2664132244693861177001585

theorem tailTrace_5188379 : CollatzResearch.WordTrace tailWord_5188379 prefixEnd_5188379 2664132244693861177001585 := by
  unfold tailWord_5188379
  simp only [CollatzResearch.WordTrace]
  refine ⟨189235728470396462431920191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126157152313597641621280127 189235728470396462431920191)
  ·
    refine ⟨283853592705594693647880287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189235728470396462431920191 283853592705594693647880287)
    ·
      refine ⟨425780389058392040471820431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283853592705594693647880287 425780389058392040471820431)
      ·
        refine ⟨638670583587588060707730647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425780389058392040471820431 638670583587588060707730647)
        ·
          refine ⟨958005875381382091061595971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638670583587588060707730647 958005875381382091061595971)
          ·
            refine ⟨1437008813072073136592393957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958005875381382091061595971 1437008813072073136592393957)
            ·
              refine ⟨269439152451013713111073867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1437008813072073136592393957 269439152451013713111073867)
              ·
                refine ⟨404158728676520569666610801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269439152451013713111073867 404158728676520569666610801)
                ·
                  refine ⟨303119046507390427249958101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404158728676520569666610801 303119046507390427249958101)
                  ·
                    refine ⟨7104352652516963138670893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 303119046507390427249958101 7104352652516963138670893)
                    ·
                      refine ⟨2664132244693861177001585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7104352652516963138670893 2664132244693861177001585)
                      ·
                        rfl

theorem cell23_5188379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 3].length) (baseStart_5188379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188379 prefixEnd_5188379 := by exact prefixLift 5188379
  have htrace : WordTrace (prefixWord ++ tailWord_5188379) baseStart_5188379 baseEnd_5188379 := by
    simpa [prefixWord, tailWord_5188379, baseEnd_5188379] using wordTrace_append hprefix tailTrace_5188379
  have hstable : (prefixWord ++ tailWord_5188379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188379).length < 2 ^ (prefixWord ++ tailWord_5188379).sum := by decide
  have hdescent : baseEnd_5188379 < baseStart_5188379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188380 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_5188380 : Nat := 118140960795 + 5188380 * 2 ^ 59
def prefixEnd_5188380 : Nat := 4983230072969 + 3 ^ 40 * 5188380 * 2
def baseEnd_5188380 : Nat := 2664132758174515673089081

theorem tailTrace_5188380 : CollatzResearch.WordTrace tailWord_5188380 prefixEnd_5188380 2664132758174515673089081 := by
  unfold tailWord_5188380
  simp only [CollatzResearch.WordTrace]
  refine ⟨94617882471696419801353297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126157176628928559735137729 94617882471696419801353297)
  ·
    refine ⟨70963411853772314851014973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94617882471696419801353297 70963411853772314851014973)
    ·
      refine ⟨26611279445164618069130615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70963411853772314851014973 26611279445164618069130615)
      ·
        refine ⟨39916919167746927103695923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26611279445164618069130615 39916919167746927103695923)
        ·
          refine ⟨59875378751620390655543885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39916919167746927103695923 59875378751620390655543885)
          ·
            refine ⟨22453267031857646495828957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59875378751620390655543885 22453267031857646495828957)
            ·
              refine ⟨8419975136946617435935859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22453267031857646495828957 8419975136946617435935859)
              ·
                refine ⟨12629962705419926153903789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8419975136946617435935859 12629962705419926153903789)
                ·
                  refine ⟨4736236014532472307713921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12629962705419926153903789 4736236014532472307713921)
                  ·
                    refine ⟨3552177010899354230785441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4736236014532472307713921 3552177010899354230785441)
                    ·
                      refine ⟨2664132758174515673089081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552177010899354230785441 2664132758174515673089081)
                      ·
                        rfl

theorem cell23_5188380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_5188380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188380 prefixEnd_5188380 := by exact prefixLift 5188380
  have htrace : WordTrace (prefixWord ++ tailWord_5188380) baseStart_5188380 baseEnd_5188380 := by
    simpa [prefixWord, tailWord_5188380, baseEnd_5188380] using wordTrace_append hprefix tailTrace_5188380
  have hstable : (prefixWord ++ tailWord_5188380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188380).length < 2 ^ (prefixWord ++ tailWord_5188380).sum := by decide
  have hdescent : baseEnd_5188380 < baseStart_5188380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188386 : List Nat := [3, 3, 1, 1, 2, 3, 2, 8]
def baseStart_5188386 : Nat := 118140960795 + 5188386 * 2 ^ 59
def prefixEnd_5188386 : Nat := 4983230072969 + 3 ^ 40 * 5188386 * 2
def baseEnd_5188386 : Nat := 98671697742905283319039

theorem tailTrace_5188386 : CollatzResearch.WordTrace tailWord_5188386 prefixEnd_5188386 98671697742905283319039 := by
  unfold tailWord_5188386
  simp only [CollatzResearch.WordTrace]
  refine ⟨47308995945342775656856253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126157322520914068418283341 47308995945342775656856253)
  ·
    refine ⟨17740873479503540871321095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47308995945342775656856253 17740873479503540871321095)
    ·
      refine ⟨26611310219255311306981643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17740873479503540871321095 26611310219255311306981643)
      ·
        refine ⟨39916965328882966960472465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26611310219255311306981643 39916965328882966960472465)
        ·
          refine ⟨29937723996662225220354349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39916965328882966960472465 29937723996662225220354349)
          ·
            refine ⟨11226646498748334457632881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29937723996662225220354349 11226646498748334457632881)
            ·
              refine ⟨8419984874061250843224661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11226646498748334457632881 8419984874061250843224661)
              ·
                refine ⟨98671697742905283319039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8419984874061250843224661 98671697742905283319039)
                ·
                  rfl

theorem cell23_5188386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 8].length) (baseStart_5188386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188386 prefixEnd_5188386 := by exact prefixLift 5188386
  have htrace : WordTrace (prefixWord ++ tailWord_5188386) baseStart_5188386 baseEnd_5188386 := by
    simpa [prefixWord, tailWord_5188386, baseEnd_5188386] using wordTrace_append hprefix tailTrace_5188386
  have hstable : (prefixWord ++ tailWord_5188386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188386).length < 2 ^ (prefixWord ++ tailWord_5188386).sum := by decide
  have hdescent : baseEnd_5188386 < baseStart_5188386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188389 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_5188389 : Nat := 118140960795 + 5188389 * 2 ^ 59
def prefixEnd_5188389 : Nat := 4983230072969 + 3 ^ 40 * 5188389 * 2
def baseEnd_5188389 : Nat := 2664137379500406137876539

theorem tailTrace_5188389 : CollatzResearch.WordTrace tailWord_5188389 prefixEnd_5188389 2664137379500406137876539 := by
  unfold tailWord_5188389
  simp only [CollatzResearch.WordTrace]
  refine ⟨189236093200360234139784221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126157395466906822759856147 189236093200360234139784221)
  ·
    refine ⟨70963534950135087802419083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189236093200360234139784221 70963534950135087802419083)
    ·
      refine ⟨106445302425202631703628625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70963534950135087802419083 106445302425202631703628625)
      ·
        refine ⟨79833976818901973777721469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106445302425202631703628625 79833976818901973777721469)
        ·
          refine ⟨29937741307088240166645551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79833976818901973777721469 29937741307088240166645551)
          ·
            refine ⟨44906611960632360249968327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29937741307088240166645551 44906611960632360249968327)
            ·
              refine ⟨67359917940948540374952491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44906611960632360249968327 67359917940948540374952491)
              ·
                refine ⟨101039876911422810562428737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67359917940948540374952491 101039876911422810562428737)
                ·
                  refine ⟨75779907683567107921821553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101039876911422810562428737 75779907683567107921821553)
                  ·
                    refine ⟨56834930762675330941366165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75779907683567107921821553 56834930762675330941366165)
                    ·
                      refine ⟨2664137379500406137876539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56834930762675330941366165 2664137379500406137876539)
                      ·
                        rfl

theorem cell23_5188389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_5188389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188389 prefixEnd_5188389 := by exact prefixLift 5188389
  have htrace : WordTrace (prefixWord ++ tailWord_5188389) baseStart_5188389 baseEnd_5188389 := by
    simpa [prefixWord, tailWord_5188389, baseEnd_5188389] using wordTrace_append hprefix tailTrace_5188389
  have hstable : (prefixWord ++ tailWord_5188389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188389).length < 2 ^ (prefixWord ++ tailWord_5188389).sum := by decide
  have hdescent : baseEnd_5188389 < baseStart_5188389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188396 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_5188396 : Nat := 118140960795 + 5188396 * 2 ^ 59
def prefixEnd_5188396 : Nat := 4983230072969 + 3 ^ 40 * 5188396 * 2
def baseEnd_5188396 : Nat := 2664140973864987610489007

theorem tailTrace_5188396 : CollatzResearch.WordTrace tailWord_5188396 prefixEnd_5188396 2664140973864987610489007 := by
  unfold tailWord_5188396
  simp only [CollatzResearch.WordTrace]
  refine ⟨94618174255667437167644521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126157565674223249556859361 94618174255667437167644521)
  ·
    refine ⟨70963630691750577875733391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94618174255667437167644521 70963630691750577875733391)
    ·
      refine ⟨106445446037625866813600087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70963630691750577875733391 106445446037625866813600087)
      ·
        refine ⟨159668169056438800220400131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106445446037625866813600087 159668169056438800220400131)
        ·
          refine ⟨239502253584658200330600197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159668169056438800220400131 239502253584658200330600197)
          ·
            refine ⟨44906672547123412561987537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239502253584658200330600197 44906672547123412561987537)
            ·
              refine ⟨33680004410342559421490653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44906672547123412561987537 33680004410342559421490653)
              ·
                refine ⟨12630001653878459783058995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33680004410342559421490653 12630001653878459783058995)
                ·
                  refine ⟨18945002480817689674588493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12630001653878459783058995 18945002480817689674588493)
                  ·
                    refine ⟨7104375930306633627970685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18945002480817689674588493 7104375930306633627970685)
                    ·
                      refine ⟨2664140973864987610489007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7104375930306633627970685 2664140973864987610489007)
                      ·
                        rfl

theorem cell23_5188396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_5188396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188396 prefixEnd_5188396 := by exact prefixLift 5188396
  have htrace : WordTrace (prefixWord ++ tailWord_5188396) baseStart_5188396 baseEnd_5188396 := by
    simpa [prefixWord, tailWord_5188396, baseEnd_5188396] using wordTrace_append hprefix tailTrace_5188396
  have hstable : (prefixWord ++ tailWord_5188396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188396).length < 2 ^ (prefixWord ++ tailWord_5188396).sum := by decide
  have hdescent : baseEnd_5188396 < baseStart_5188396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188417 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5188417 : Nat := 118140960795 + 5188417 * 2 ^ 59
def prefixEnd_5188417 : Nat := 4983230072969 + 3 ^ 40 * 5188417 * 2
def baseEnd_5188417 : Nat := 2664151756958732028326411

theorem tailTrace_5188417 : CollatzResearch.WordTrace tailWord_5188417 prefixEnd_5188417 2664151756958732028326411 := by
  unfold tailWord_5188417
  simp only [CollatzResearch.WordTrace]
  refine ⟨189237114444258794921803505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126158076296172529947869003 189237114444258794921803505)
  ·
    refine ⟨141927835833194096191352629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189237114444258794921803505 141927835833194096191352629)
    ·
      refine ⟨13305734609361946517939309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141927835833194096191352629 13305734609361946517939309)
      ·
        refine ⟨4989650478510729944227241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13305734609361946517939309 4989650478510729944227241)
        ·
          refine ⟨3742237858883047458170431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4989650478510729944227241 3742237858883047458170431)
          ·
            refine ⟨5613356788324571187255647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3742237858883047458170431 5613356788324571187255647)
            ·
              refine ⟨8420035182486856780883471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5613356788324571187255647 8420035182486856780883471)
              ·
                refine ⟨12630052773730285171325207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8420035182486856780883471 12630052773730285171325207)
                ·
                  refine ⟨18945079160595427756987811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12630052773730285171325207 18945079160595427756987811)
                  ·
                    refine ⟨28417618740893141635481717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18945079160595427756987811 28417618740893141635481717)
                    ·
                      refine ⟨2664151756958732028326411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28417618740893141635481717 2664151756958732028326411)
                      ·
                        rfl

theorem cell23_5188417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5188417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188417 prefixEnd_5188417 := by exact prefixLift 5188417
  have htrace : WordTrace (prefixWord ++ tailWord_5188417) baseStart_5188417 baseEnd_5188417 := by
    simpa [prefixWord, tailWord_5188417, baseEnd_5188417] using wordTrace_append hprefix tailTrace_5188417
  have hstable : (prefixWord ++ tailWord_5188417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188417).length < 2 ^ (prefixWord ++ tailWord_5188417).sum := by decide
  have hdescent : baseEnd_5188417 < baseStart_5188417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188453 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 1, 4, 2]
def baseStart_5188453 : Nat := 118140960795 + 5188453 * 2 ^ 59
def prefixEnd_5188453 : Nat := 4983230072969 + 3 ^ 40 * 5188453 * 2
def baseEnd_5188453 : Nat := 2664170242262293887476245

theorem tailTrace_5188453 : CollatzResearch.WordTrace tailWord_5188453 prefixEnd_5188453 2664170242262293887476245 := by
  unfold tailWord_5188453
  simp only [CollatzResearch.WordTrace]
  refine ⟨189238427472128373070114013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126158951648085582046742675 189238427472128373070114013)
  ·
    refine ⟨70964410302048139901292755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189238427472128373070114013 70964410302048139901292755)
    ·
      refine ⟨106446615453072209851939133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70964410302048139901292755 106446615453072209851939133)
      ·
        refine ⟨39917480794902078694477175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106446615453072209851939133 39917480794902078694477175)
        ·
          refine ⟨59876221192353118041715763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39917480794902078694477175 59876221192353118041715763)
          ·
            refine ⟨89814331788529677062573645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59876221192353118041715763 89814331788529677062573645)
            ·
              refine ⟨33680374420698628898465117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89814331788529677062573645 33680374420698628898465117)
              ·
                refine ⟨12630140407761985836924419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33680374420698628898465117 12630140407761985836924419)
                ·
                  refine ⟨18945210611642978755386629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12630140407761985836924419 18945210611642978755386629)
                  ·
                    refine ⟨3552226989683058516634993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18945210611642978755386629 3552226989683058516634993)
                    ·
                      refine ⟨2664170242262293887476245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552226989683058516634993 2664170242262293887476245)
                      ·
                        rfl

theorem cell23_5188453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_5188453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188453 prefixEnd_5188453 := by exact prefixLift 5188453
  have htrace : WordTrace (prefixWord ++ tailWord_5188453) baseStart_5188453 baseEnd_5188453 := by
    simpa [prefixWord, tailWord_5188453, baseEnd_5188453] using wordTrace_append hprefix tailTrace_5188453
  have hstable : (prefixWord ++ tailWord_5188453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188453).length < 2 ^ (prefixWord ++ tailWord_5188453).sum := by decide
  have hdescent : baseEnd_5188453 < baseStart_5188453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188459 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 9]
def baseStart_5188459 : Nat := 118140960795 + 5188459 * 2 ^ 59
def prefixEnd_5188459 : Nat := 4983230072969 + 3 ^ 40 * 5188459 * 2
def baseEnd_5188459 : Nat := 296019258127357873777913

theorem tailTrace_5188459 : CollatzResearch.WordTrace tailWord_5188459 prefixEnd_5188459 296019258127357873777913 := by
  unfold tailWord_5188459
  simp only [CollatzResearch.WordTrace]
  refine ⟨189238646310106636094832431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126159097540071090729888287 189238646310106636094832431)
  ·
    refine ⟨283857969465159954142248647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189238646310106636094832431 283857969465159954142248647)
    ·
      refine ⟨425786954197739931213372971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283857969465159954142248647 425786954197739931213372971)
      ·
        refine ⟨638680431296609896820059457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425786954197739931213372971 638680431296609896820059457)
        ·
          refine ⟨479010323472457422615044593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638680431296609896820059457 479010323472457422615044593)
          ·
            refine ⟨359257742604343066961283445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479010323472457422615044593 359257742604343066961283445)
            ·
              refine ⟨33680413369157162527620323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 359257742604343066961283445 33680413369157162527620323)
              ·
                refine ⟨50520620053735743791430485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33680413369157162527620323 50520620053735743791430485)
                ·
                  refine ⟨296019258127357873777913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50520620053735743791430485 296019258127357873777913)
                  ·
                    rfl

theorem cell23_5188459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 9].length) (baseStart_5188459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188459 prefixEnd_5188459 := by exact prefixLift 5188459
  have htrace : WordTrace (prefixWord ++ tailWord_5188459) baseStart_5188459 baseEnd_5188459 := by
    simpa [prefixWord, tailWord_5188459, baseEnd_5188459] using wordTrace_append hprefix tailTrace_5188459
  have hstable : (prefixWord ++ tailWord_5188459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188459).length < 2 ^ (prefixWord ++ tailWord_5188459).sum := by decide
  have hdescent : baseEnd_5188459 < baseStart_5188459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188487 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_5188487 : Nat := 118140960795 + 5188487 * 2 ^ 59
def prefixEnd_5188487 : Nat := 4983230072969 + 3 ^ 40 * 5188487 * 2
def baseEnd_5188487 : Nat := 2664187700604546754451089

theorem tailTrace_5188487 : CollatzResearch.WordTrace tailWord_5188487 prefixEnd_5188487 2664187700604546754451089 := by
  unfold tailWord_5188487
  simp only [CollatzResearch.WordTrace]
  refine ⟨189239667554005196876851715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126159778369336797917901143 189239667554005196876851715)
  ·
    refine ⟨283859501331007795315277573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189239667554005196876851715 283859501331007795315277573)
    ·
      refine ⟨53223656499563961621614545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283859501331007795315277573 53223656499563961621614545)
      ·
        refine ⟨39917742374672971216210909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53223656499563961621614545 39917742374672971216210909)
        ·
          refine ⟨14969153390502364206079091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39917742374672971216210909 14969153390502364206079091)
          ·
            refine ⟨22453730085753546309118637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14969153390502364206079091 22453730085753546309118637)
            ·
              refine ⟨8420148782157579865919489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22453730085753546309118637 8420148782157579865919489)
              ·
                refine ⟨6315111586618184899439617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8420148782157579865919489 6315111586618184899439617)
                ·
                  refine ⟨4736333689963638674579713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6315111586618184899439617 4736333689963638674579713)
                  ·
                    refine ⟨3552250267472729005934785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4736333689963638674579713 3552250267472729005934785)
                    ·
                      refine ⟨2664187700604546754451089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552250267472729005934785 2664187700604546754451089)
                      ·
                        rfl

theorem cell23_5188487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_5188487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188487 prefixEnd_5188487 := by exact prefixLift 5188487
  have htrace : WordTrace (prefixWord ++ tailWord_5188487) baseStart_5188487 baseEnd_5188487 := by
    simpa [prefixWord, tailWord_5188487, baseEnd_5188487] using wordTrace_append hprefix tailTrace_5188487
  have hstable : (prefixWord ++ tailWord_5188487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188487).length < 2 ^ (prefixWord ++ tailWord_5188487).sum := by decide
  have hdescent : baseEnd_5188487 < baseStart_5188487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188543 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 2, 4, 2]
def baseStart_5188543 : Nat := 118140960795 + 5188543 * 2 ^ 59
def prefixEnd_5188543 : Nat := 4983230072969 + 3 ^ 40 * 5188543 * 2
def baseEnd_5188543 : Nat := 2664216455521198535350831

theorem tailTrace_5188543 : CollatzResearch.WordTrace tailWord_5188543 prefixEnd_5188543 2664216455521198535350831 := by
  unfold tailWord_5188543
  simp only [CollatzResearch.WordTrace]
  refine ⟨189241710041802318440890283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126161140027868212293926855 189241710041802318440890283)
  ·
    refine ⟨283862565062703477661335425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189241710041802318440890283 283862565062703477661335425)
    ·
      refine ⟨212896923797027608246001569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283862565062703477661335425 212896923797027608246001569)
      ·
        refine ⟨159672692847770706184501177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212896923797027608246001569 159672692847770706184501177)
        ·
          refine ⟨119754519635828029638375883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159672692847770706184501177 119754519635828029638375883)
          ·
            refine ⟨179631779453742044457563825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119754519635828029638375883 179631779453742044457563825)
            ·
              refine ⟨134723834590306533343172869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179631779453742044457563825 134723834590306533343172869)
              ·
                refine ⟨25260718985682475001844913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134723834590306533343172869 25260718985682475001844913)
                ·
                  refine ⟨18945539239261856251383685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25260718985682475001844913 18945539239261856251383685)
                  ·
                    refine ⟨3552288607361598047134441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18945539239261856251383685 3552288607361598047134441)
                    ·
                      refine ⟨2664216455521198535350831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552288607361598047134441 2664216455521198535350831)
                      ·
                        rfl

theorem cell23_5188543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_5188543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188543 prefixEnd_5188543 := by exact prefixLift 5188543
  have htrace : WordTrace (prefixWord ++ tailWord_5188543) baseStart_5188543 baseEnd_5188543 := by
    simpa [prefixWord, tailWord_5188543, baseEnd_5188543] using wordTrace_append hprefix tailTrace_5188543
  have hstable : (prefixWord ++ tailWord_5188543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188543).length < 2 ^ (prefixWord ++ tailWord_5188543).sum := by decide
  have hdescent : baseEnd_5188543 < baseStart_5188543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188603 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 3, 5, 2]
def baseStart_5188603 : Nat := 118140960795 + 5188603 * 2 ^ 59
def prefixEnd_5188603 : Nat := 4983230072969 + 3 ^ 40 * 5188603 * 2
def baseEnd_5188603 : Nat := 2664247264360468300600555

theorem tailTrace_5188603 : CollatzResearch.WordTrace tailWord_5188603 prefixEnd_5188603 2664247264360468300600555 := by
  unfold tailWord_5188603
  simp only [CollatzResearch.WordTrace]
  refine ⟨189243898421584948688074463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126162598947723299125382975 189243898421584948688074463)
  ·
    refine ⟨283865847632377423032111695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189243898421584948688074463 283865847632377423032111695)
    ·
      refine ⟨425798771448566134548167543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283865847632377423032111695 425798771448566134548167543)
      ·
        refine ⟨638698157172849201822251315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425798771448566134548167543 638698157172849201822251315)
        ·
          refine ⟨958047235759273802733376973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638698157172849201822251315 958047235759273802733376973)
          ·
            refine ⟨359267713409727676025016365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 958047235759273802733376973 359267713409727676025016365)
            ·
              refine ⟨134725392528647878509381137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359267713409727676025016365 134725392528647878509381137)
              ·
                refine ⟨101044044396485908882035853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134725392528647878509381137 101044044396485908882035853)
                ·
                  refine ⟨37891516648682215830763445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101044044396485908882035853 37891516648682215830763445)
                  ·
                    refine ⟨3552329685813957734134073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37891516648682215830763445 3552329685813957734134073)
                    ·
                      refine ⟨2664247264360468300600555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552329685813957734134073 2664247264360468300600555)
                      ·
                        rfl

theorem cell23_5188603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5, 2].length) (baseStart_5188603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188603 prefixEnd_5188603 := by exact prefixLift 5188603
  have htrace : WordTrace (prefixWord ++ tailWord_5188603) baseStart_5188603 baseEnd_5188603 := by
    simpa [prefixWord, tailWord_5188603, baseEnd_5188603] using wordTrace_append hprefix tailTrace_5188603
  have hstable : (prefixWord ++ tailWord_5188603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188603).length < 2 ^ (prefixWord ++ tailWord_5188603).sum := by decide
  have hdescent : baseEnd_5188603 < baseStart_5188603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188604 : List Nat := [2, 2, 2, 1, 2, 5, 2, 2, 1, 4]
def baseStart_5188604 : Nat := 118140960795 + 5188604 * 2 ^ 59
def prefixEnd_5188604 : Nat := 4983230072969 + 3 ^ 40 * 5188604 * 2
def baseEnd_5188604 : Nat := 888082592613707598896017

theorem tailTrace_5188604 : CollatzResearch.WordTrace tailWord_5188604 prefixEnd_5188604 888082592613707598896017 := by
  unfold tailWord_5188604
  simp only [CollatzResearch.WordTrace]
  refine ⟨94621967447290662929430433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126162623263054217239240577 94621967447290662929430433)
  ·
    refine ⟨70966475585467997197072825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94621967447290662929430433 70966475585467997197072825)
    ·
      refine ⟨53224856689100997897804619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70966475585467997197072825 53224856689100997897804619)
      ·
        refine ⟨79837285033651496846706929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53224856689100997897804619 79837285033651496846706929)
        ·
          refine ⟨59877963775238622635030197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79837285033651496846706929 59877963775238622635030197)
          ·
            refine ⟨5613559103928620872034081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59877963775238622635030197 5613559103928620872034081)
            ·
              refine ⟨4210169327946465654025561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5613559103928620872034081 4210169327946465654025561)
              ·
                refine ⟨3157626995959849240519171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4210169327946465654025561 3157626995959849240519171)
                ·
                  refine ⟨4736440493939773860778757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157626995959849240519171 4736440493939773860778757)
                  ·
                    refine ⟨888082592613707598896017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4736440493939773860778757 888082592613707598896017)
                    ·
                      rfl

theorem cell23_5188604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_5188604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188604 prefixEnd_5188604 := by exact prefixLift 5188604
  have htrace : WordTrace (prefixWord ++ tailWord_5188604) baseStart_5188604 baseEnd_5188604 := by
    simpa [prefixWord, tailWord_5188604, baseEnd_5188604] using wordTrace_append hprefix tailTrace_5188604
  have hstable : (prefixWord ++ tailWord_5188604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188604).length < 2 ^ (prefixWord ++ tailWord_5188604).sum := by decide
  have hdescent : baseEnd_5188604 < baseStart_5188604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188633 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_5188633 : Nat := 118140960795 + 5188633 * 2 ^ 59
def prefixEnd_5188633 : Nat := 4983230072969 + 3 ^ 40 * 5188633 * 2
def baseEnd_5188633 : Nat := 2664262668780103183225417

theorem tailTrace_5188633 : CollatzResearch.WordTrace tailWord_5188633 prefixEnd_5188633 2664262668780103183225417 := by
  unfold tailWord_5188633
  simp only [CollatzResearch.WordTrace]
  refine ⟨189244992611476263811666553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126163328407650842541111035 189244992611476263811666553)
  ·
    refine ⟨141933744458607197858749915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189244992611476263811666553 141933744458607197858749915)
    ·
      refine ⟨212900616687910796788124873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141933744458607197858749915 212900616687910796788124873)
      ·
        refine ⟨159675462515933097591093655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212900616687910796788124873 159675462515933097591093655)
        ·
          refine ⟨239513193773899646386640483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159675462515933097591093655 239513193773899646386640483)
          ·
            refine ⟨359269790660849469579960725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239513193773899646386640483 359269790660849469579960725)
            ·
              refine ⟨16840771437227318886560659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 359269790660849469579960725 16840771437227318886560659)
              ·
                refine ⟨25261157155840978329840989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16840771437227318886560659 25261157155840978329840989)
                ·
                  refine ⟨9472933933440366873690371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25261157155840978329840989 9472933933440366873690371)
                  ·
                    refine ⟨14209400900160550310535557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9472933933440366873690371 14209400900160550310535557)
                    ·
                      refine ⟨2664262668780103183225417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14209400900160550310535557 2664262668780103183225417)
                      ·
                        rfl

theorem cell23_5188633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_5188633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188633 prefixEnd_5188633 := by exact prefixLift 5188633
  have htrace : WordTrace (prefixWord ++ tailWord_5188633) baseStart_5188633 baseEnd_5188633 := by
    simpa [prefixWord, tailWord_5188633, baseEnd_5188633] using wordTrace_append hprefix tailTrace_5188633
  have hstable : (prefixWord ++ tailWord_5188633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188633).length < 2 ^ (prefixWord ++ tailWord_5188633).sum := by decide
  have hdescent : baseEnd_5188633 < baseStart_5188633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188637 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_5188637 : Nat := 118140960795 + 5188637 * 2 ^ 59
def prefixEnd_5188637 : Nat := 4983230072969 + 3 ^ 40 * 5188637 * 2
def baseEnd_5188637 : Nat := 2664264722702721167575399

theorem tailTrace_5188637 : CollatzResearch.WordTrace tailWord_5188637 prefixEnd_5188637 2664264722702721167575399 := by
  unfold tailWord_5188637
  simp only [CollatzResearch.WordTrace]
  refine ⟨189245138503461772494812165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126163425668974514996541443 189245138503461772494812165)
  ·
    refine ⟨35483463469399082342777281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189245138503461772494812165 35483463469399082342777281)
    ·
      refine ⟨26612597602049311757082961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35483463469399082342777281 26612597602049311757082961)
      ·
        refine ⟨19959448201536983817812221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26612597602049311757082961 19959448201536983817812221)
        ·
          refine ⟨7484793075576368931679583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19959448201536983817812221 7484793075576368931679583)
          ·
            refine ⟨11227189613364553397519375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7484793075576368931679583 11227189613364553397519375)
            ·
              refine ⟨16840784420046830096279063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11227189613364553397519375 16840784420046830096279063)
              ·
                refine ⟨25261176630070245144418595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16840784420046830096279063 25261176630070245144418595)
                ·
                  refine ⟨37891764945105367716627893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25261176630070245144418595 37891764945105367716627893)
                  ·
                    refine ⟨3552352963603628223433865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37891764945105367716627893 3552352963603628223433865)
                    ·
                      refine ⟨2664264722702721167575399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552352963603628223433865 2664264722702721167575399)
                      ·
                        rfl

theorem cell23_5188637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_5188637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188637 prefixEnd_5188637 := by exact prefixLift 5188637
  have htrace : WordTrace (prefixWord ++ tailWord_5188637) baseStart_5188637 baseEnd_5188637 := by
    simpa [prefixWord, tailWord_5188637, baseEnd_5188637] using wordTrace_append hprefix tailTrace_5188637
  have hstable : (prefixWord ++ tailWord_5188637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188637).length < 2 ^ (prefixWord ++ tailWord_5188637).sum := by decide
  have hdescent : baseEnd_5188637 < baseStart_5188637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188643 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 1, 6]
def baseStart_5188643 : Nat := 118140960795 + 5188643 * 2 ^ 59
def prefixEnd_5188643 : Nat := 4983230072969 + 3 ^ 40 * 5188643 * 2
def baseEnd_5188643 : Nat := 888089267862216048033457

theorem tailTrace_5188643 : CollatzResearch.WordTrace tailWord_5188643 prefixEnd_5188643 888089267862216048033457 := by
  unfold tailWord_5188643
  simp only [CollatzResearch.WordTrace]
  refine ⟨189245357341440035519530583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126163571560960023679687055 189245357341440035519530583)
  ·
    refine ⟨283868036012160053279295875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189245357341440035519530583 283868036012160053279295875)
    ·
      refine ⟨425802054018240079918943813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283868036012160053279295875 425802054018240079918943813)
      ·
        refine ⟨79837885128420014984801965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 425802054018240079918943813 79837885128420014984801965)
        ·
          refine ⟨29939206923157505619300737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79837885128420014984801965 29939206923157505619300737)
          ·
            refine ⟨22454405192368129214475553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29939206923157505619300737 22454405192368129214475553)
            ·
              refine ⟨16840803894276096910856665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22454405192368129214475553 16840803894276096910856665)
              ·
                refine ⟨12630602920707072683142499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16840803894276096910856665 12630602920707072683142499)
                ·
                  refine ⟨18945904381060609024713749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12630602920707072683142499 18945904381060609024713749)
                  ·
                    refine ⟨888089267862216048033457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18945904381060609024713749 888089267862216048033457)
                    ·
                      rfl

theorem cell23_5188643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 6].length) (baseStart_5188643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188643 prefixEnd_5188643 := by exact prefixLift 5188643
  have htrace : WordTrace (prefixWord ++ tailWord_5188643) baseStart_5188643 baseEnd_5188643 := by
    simpa [prefixWord, tailWord_5188643, baseEnd_5188643] using wordTrace_append hprefix tailTrace_5188643
  have hstable : (prefixWord ++ tailWord_5188643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188643).length < 2 ^ (prefixWord ++ tailWord_5188643).sum := by decide
  have hdescent : baseEnd_5188643 < baseStart_5188643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188644 : List Nat := [2, 3, 1, 4, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5188644 : Nat := 118140960795 + 5188644 * 2 ^ 59
def prefixEnd_5188644 : Nat := 4983230072969 + 3 ^ 40 * 5188644 * 2
def baseEnd_5188644 : Nat := 2664268317067302640187867

theorem tailTrace_5188644 : CollatzResearch.WordTrace tailWord_5188644 prefixEnd_5188644 2664268317067302640187867 := by
  unfold tailWord_5188644
  simp only [CollatzResearch.WordTrace]
  refine ⟨94622696907218206345158493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126163595876290941793544657 94622696907218206345158493)
  ·
    refine ⟨35483511340206827379434435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94622696907218206345158493 35483511340206827379434435)
    ·
      refine ⟨53225267010310241069151653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35483511340206827379434435 53225267010310241069151653)
      ·
        refine ⟨9979737564433170200465935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53225267010310241069151653 9979737564433170200465935)
        ·
          refine ⟨14969606346649755300698903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979737564433170200465935 14969606346649755300698903)
          ·
            refine ⟨22454409519974632951048355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14969606346649755300698903 22454409519974632951048355)
            ·
              refine ⟨33681614279961949426572533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22454409519974632951048355 33681614279961949426572533)
              ·
                refine ⟨3157651338746432758741175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33681614279961949426572533 3157651338746432758741175)
                ·
                  refine ⟨4736477008119649138111763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157651338746432758741175 4736477008119649138111763)
                  ·
                    refine ⟨7104715512179473707167645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4736477008119649138111763 7104715512179473707167645)
                    ·
                      refine ⟨2664268317067302640187867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7104715512179473707167645 2664268317067302640187867)
                      ·
                        rfl

theorem cell23_5188644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5188644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188644 prefixEnd_5188644 := by exact prefixLift 5188644
  have htrace : WordTrace (prefixWord ++ tailWord_5188644) baseStart_5188644 baseEnd_5188644 := by
    simpa [prefixWord, tailWord_5188644, baseEnd_5188644] using wordTrace_append hprefix tailTrace_5188644
  have hstable : (prefixWord ++ tailWord_5188644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188644).length < 2 ^ (prefixWord ++ tailWord_5188644).sum := by decide
  have hdescent : baseEnd_5188644 < baseStart_5188644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188647 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 1, 5]
def baseStart_5188647 : Nat := 118140960795 + 5188647 * 2 ^ 59
def prefixEnd_5188647 : Nat := 4983230072969 + 3 ^ 40 * 5188647 * 2
def baseEnd_5188647 : Nat := 888089952503088709483451

theorem tailTrace_5188647 : CollatzResearch.WordTrace tailWord_5188647 prefixEnd_5188647 888089952503088709483451 := by
  unfold tailWord_5188647
  simp only [CollatzResearch.WordTrace]
  refine ⟨189245503233425544202676195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126163668822283696135117463 189245503233425544202676195)
  ·
    refine ⟨283868254850138316304014293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189245503233425544202676195 283868254850138316304014293)
    ·
      refine ⟨6653162223050116788375335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 283868254850138316304014293 6653162223050116788375335)
      ·
        refine ⟨9979743334575175182563003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6653162223050116788375335 9979743334575175182563003)
        ·
          refine ⟨14969615001862762773844505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979743334575175182563003 14969615001862762773844505)
          ·
            refine ⟨11227211251397072080383379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14969615001862762773844505 11227211251397072080383379)
            ·
              refine ⟨16840816877095608120575069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11227211251397072080383379 16840816877095608120575069)
              ·
                refine ⟨6315306328910853045215651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16840816877095608120575069 6315306328910853045215651)
                ·
                  refine ⟨9472959493366279567823477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6315306328910853045215651 9472959493366279567823477)
                  ·
                    refine ⟨888089952503088709483451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9472959493366279567823477 888089952503088709483451)
                    ·
                      rfl

theorem cell23_5188647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_5188647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188647 prefixEnd_5188647 := by exact prefixLift 5188647
  have htrace : WordTrace (prefixWord ++ tailWord_5188647) baseStart_5188647 baseEnd_5188647 := by
    simpa [prefixWord, tailWord_5188647, baseEnd_5188647] using wordTrace_append hprefix tailTrace_5188647
  have hstable : (prefixWord ++ tailWord_5188647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188647).length < 2 ^ (prefixWord ++ tailWord_5188647).sum := by decide
  have hdescent : baseEnd_5188647 < baseStart_5188647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188656 : List Nat := [2, 1, 1, 1, 2, 4, 12]
def baseStart_5188656 : Nat := 118140960795 + 5188656 * 2 ^ 59
def prefixEnd_5188656 : Nat := 4983230072969 + 3 ^ 40 * 5188656 * 2
def baseEnd_5188656 : Nat := 32892277516483414731331

theorem tailTrace_5188656 : CollatzResearch.WordTrace tailWord_5188656 prefixEnd_5188656 32892277516483414731331 := by
  unfold tailWord_5188656
  simp only [CollatzResearch.WordTrace]
  refine ⟨94622915745196469369876911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126163887660261959159835881 94622915745196469369876911)
  ·
    refine ⟨141934373617794704054815367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94622915745196469369876911 141934373617794704054815367)
    ·
      refine ⟨212901560426692056082223051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141934373617794704054815367 212901560426692056082223051)
      ·
        refine ⟨319352340640038084123334577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212901560426692056082223051 319352340640038084123334577)
        ·
          refine ⟨239514255480028563092500933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319352340640038084123334577 239514255480028563092500933)
          ·
            refine ⟨44908922902505355579843925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239514255480028563092500933 44908922902505355579843925)
            ·
              refine ⟨32892277516483414731331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44908922902505355579843925 32892277516483414731331)
              ·
                rfl

theorem cell23_5188656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 12].length) (baseStart_5188656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188656 prefixEnd_5188656 := by exact prefixLift 5188656
  have htrace : WordTrace (prefixWord ++ tailWord_5188656) baseStart_5188656 baseEnd_5188656 := by
    simpa [prefixWord, tailWord_5188656, baseEnd_5188656] using wordTrace_append hprefix tailTrace_5188656
  have hstable : (prefixWord ++ tailWord_5188656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188656).length < 2 ^ (prefixWord ++ tailWord_5188656).sum := by decide
  have hdescent : baseEnd_5188656 < baseStart_5188656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188670 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5188670 : Nat := 118140960795 + 5188670 * 2 ^ 59
def prefixEnd_5188670 : Nat := 4983230072969 + 3 ^ 40 * 5188670 * 2
def baseEnd_5188670 : Nat := 2664281667564319538462747

theorem tailTrace_5188670 : CollatzResearch.WordTrace tailWord_5188670 prefixEnd_5188670 2664281667564319538462747 := by
  unfold tailWord_5188670
  simp only [CollatzResearch.WordTrace]
  refine ⟨23655792764042777391345433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126164228074894812753842309 23655792764042777391345433)
  ·
    refine ⟨17741844573032083043509075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23655792764042777391345433 17741844573032083043509075)
    ·
      refine ⟨26612766859548124565263613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17741844573032083043509075 26612766859548124565263613)
      ·
        refine ⟨9979787572330546711973855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26612766859548124565263613 9979787572330546711973855)
        ·
          refine ⟨14969681358495820067960783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9979787572330546711973855 14969681358495820067960783)
          ·
            refine ⟨22454522037743730101941175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14969681358495820067960783 22454522037743730101941175)
            ·
              refine ⟨33681783056615595152911763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22454522037743730101941175 33681783056615595152911763)
              ·
                refine ⟨50522674584923392729367645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33681783056615595152911763 50522674584923392729367645)
                ·
                  refine ⟨18946002969346272273512867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50522674584923392729367645 18946002969346272273512867)
                  ·
                    refine ⟨28419004454019408410269301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18946002969346272273512867 28419004454019408410269301)
                    ·
                      refine ⟨2664281667564319538462747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28419004454019408410269301 2664281667564319538462747)
                      ·
                        rfl

theorem cell23_5188670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5188670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188670 prefixEnd_5188670 := by exact prefixLift 5188670
  have htrace : WordTrace (prefixWord ++ tailWord_5188670) baseStart_5188670 baseEnd_5188670 := by
    simpa [prefixWord, tailWord_5188670, baseEnd_5188670] using wordTrace_append hprefix tailTrace_5188670
  have hstable : (prefixWord ++ tailWord_5188670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188670).length < 2 ^ (prefixWord ++ tailWord_5188670).sum := by decide
  have hdescent : baseEnd_5188670 < baseStart_5188670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188690 : List Nat := [3, 2, 2, 1, 3, 1, 4, 7]
def baseStart_5188690 : Nat := 118140960795 + 5188690 * 2 ^ 59
def prefixEnd_5188690 : Nat := 4983230072969 + 3 ^ 40 * 5188690 * 2
def baseEnd_5188690 : Nat := 98677479154718868896765

theorem tailTrace_5188690 : CollatzResearch.WordTrace tailWord_5188690 prefixEnd_5188690 98677479154718868896765 := by
  unfold tailWord_5188690
  simp only [CollatzResearch.WordTrace]
  refine ⟨47311767893067440636622881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126164714381513175030994349 47311767893067440636622881)
  ·
    refine ⟨35483825919800580477467161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47311767893067440636622881 35483825919800580477467161)
    ·
      refine ⟨26612869439850435358100371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35483825919800580477467161 26612869439850435358100371)
      ·
        refine ⟨39919304159775653037150557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26612869439850435358100371 39919304159775653037150557)
        ·
          refine ⟨14969739059915869888931459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39919304159775653037150557 14969739059915869888931459)
          ·
            refine ⟨22454608589873804833397189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14969739059915869888931459 22454608589873804833397189)
            ·
              refine ⟨4210239110601338406261973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22454608589873804833397189 4210239110601338406261973)
              ·
                refine ⟨98677479154718868896765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4210239110601338406261973 98677479154718868896765)
                ·
                  rfl

theorem cell23_5188690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 7].length) (baseStart_5188690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188690 prefixEnd_5188690 := by exact prefixLift 5188690
  have htrace : WordTrace (prefixWord ++ tailWord_5188690) baseStart_5188690 baseEnd_5188690 := by
    simpa [prefixWord, tailWord_5188690, baseEnd_5188690] using wordTrace_append hprefix tailTrace_5188690
  have hstable : (prefixWord ++ tailWord_5188690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188690).length < 2 ^ (prefixWord ++ tailWord_5188690).sum := by decide
  have hdescent : baseEnd_5188690 < baseStart_5188690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188700 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_5188700 : Nat := 118140960795 + 5188700 * 2 ^ 59
def prefixEnd_5188700 : Nat := 4983230072969 + 3 ^ 40 * 5188700 * 2
def baseEnd_5188700 : Nat := 2664297071983954421087609

theorem tailTrace_5188700 : CollatzResearch.WordTrace tailWord_5188700 prefixEnd_5188700 2664297071983954421087609 := by
  unfold tailWord_5188700
  simp only [CollatzResearch.WordTrace]
  refine ⟨94623718151116767127177777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126164957534822356169570369 94623718151116767127177777)
  ·
    refine ⟨70967788613337575345383333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94623718151116767127177777 70967788613337575345383333)
    ·
      refine ⟨13306460365000795377259375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70967788613337575345383333 13306460365000795377259375)
      ·
        refine ⟨19959690547501193065889063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13306460365000795377259375 19959690547501193065889063)
        ·
          refine ⟨29939535821251789598833595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19959690547501193065889063 29939535821251789598833595)
          ·
            refine ⟨44909303731877684398250393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29939535821251789598833595 44909303731877684398250393)
            ·
              refine ⟨33681977798908263298687795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44909303731877684398250393 33681977798908263298687795)
              ·
                refine ⟨50522966698362394948031693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33681977798908263298687795 50522966698362394948031693)
                ·
                  refine ⟨18946112511885898105511885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50522966698362394948031693 18946112511885898105511885)
                  ·
                    refine ⟨7104792191957211789566957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18946112511885898105511885 7104792191957211789566957)
                    ·
                      refine ⟨2664297071983954421087609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7104792191957211789566957 2664297071983954421087609)
                      ·
                        rfl

theorem cell23_5188700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_5188700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188700 prefixEnd_5188700 := by exact prefixLift 5188700
  have htrace : WordTrace (prefixWord ++ tailWord_5188700) baseStart_5188700 baseEnd_5188700 := by
    simpa [prefixWord, tailWord_5188700, baseEnd_5188700] using wordTrace_append hprefix tailTrace_5188700
  have hstable : (prefixWord ++ tailWord_5188700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188700).length < 2 ^ (prefixWord ++ tailWord_5188700).sum := by decide
  have hdescent : baseEnd_5188700 < baseStart_5188700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188717 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_5188717 : Nat := 118140960795 + 5188717 * 2 ^ 59
def prefixEnd_5188717 : Nat := 4983230072969 + 3 ^ 40 * 5188717 * 2
def baseEnd_5188717 : Nat := 2664305801155080854575031

theorem tailTrace_5188717 : CollatzResearch.WordTrace tailWord_5188717 prefixEnd_5188717 2664305801155080854575031 := by
  unfold tailWord_5188717
  simp only [CollatzResearch.WordTrace]
  refine ⟨189248056343171946157724405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126165370895447964105149603 189248056343171946157724405)
  ·
    refine ⟨17742005282172369952286663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 189248056343171946157724405 17742005282172369952286663)
    ·
      refine ⟨26613007923258554928429995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17742005282172369952286663 26613007923258554928429995)
      ·
        refine ⟨39919511884887832392644993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26613007923258554928429995 39919511884887832392644993)
        ·
          refine ⟨29939633913665874294483745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39919511884887832392644993 29939633913665874294483745)
          ·
            refine ⟨22454725435249405720862809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29939633913665874294483745 22454725435249405720862809)
            ·
              refine ⟨16841044076437054290647107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22454725435249405720862809 16841044076437054290647107)
              ·
                refine ⟨25261566114655581435970661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16841044076437054290647107 25261566114655581435970661)
                ·
                  refine ⟨4736543646497921519244499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25261566114655581435970661 4736543646497921519244499)
                  ·
                    refine ⟨7104815469746882278866749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4736543646497921519244499 7104815469746882278866749)
                    ·
                      refine ⟨2664305801155080854575031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7104815469746882278866749 2664305801155080854575031)
                      ·
                        rfl

theorem cell23_5188717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_5188717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188717 prefixEnd_5188717 := by exact prefixLift 5188717
  have htrace : WordTrace (prefixWord ++ tailWord_5188717) baseStart_5188717 baseEnd_5188717 := by
    simpa [prefixWord, tailWord_5188717, baseEnd_5188717] using wordTrace_append hprefix tailTrace_5188717
  have hstable : (prefixWord ++ tailWord_5188717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188717).length < 2 ^ (prefixWord ++ tailWord_5188717).sum := by decide
  have hdescent : baseEnd_5188717 < baseStart_5188717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188718 : List Nat := [4, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_5188718 : Nat := 118140960795 + 5188718 * 2 ^ 59
def prefixEnd_5188718 : Nat := 4983230072969 + 3 ^ 40 * 5188718 * 2
def baseEnd_5188718 : Nat := 2664306314635735350662527

theorem tailTrace_5188718 : CollatzResearch.WordTrace tailWord_5188718 prefixEnd_5188718 2664306314635735350662527 := by
  unfold tailWord_5188718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23656011602021040416063851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126165395210778882219007205 23656011602021040416063851)
  ·
    refine ⟨35484017403031560624095777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23656011602021040416063851 35484017403031560624095777)
    ·
      refine ⟨26613013052273670468071833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35484017403031560624095777 26613013052273670468071833)
      ·
        refine ⟨19959759789205252851053875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26613013052273670468071833 19959759789205252851053875)
        ·
          refine ⟨29939639683807879276580813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19959759789205252851053875 29939639683807879276580813)
          ·
            refine ⟨11227364881427954728717805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29939639683807879276580813 11227364881427954728717805)
            ·
              refine ⟨4210261830535483023269177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11227364881427954728717805 4210261830535483023269177)
              ·
                refine ⟨3157696372901612267451883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4210261830535483023269177 3157696372901612267451883)
                ·
                  refine ⟨4736544559352418401177825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157696372901612267451883 4736544559352418401177825)
                  ·
                    refine ⟨3552408419514313800883369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4736544559352418401177825 3552408419514313800883369)
                    ·
                      refine ⟨2664306314635735350662527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552408419514313800883369 2664306314635735350662527)
                      ·
                        rfl

theorem cell23_5188718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_5188718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188718 prefixEnd_5188718 := by exact prefixLift 5188718
  have htrace : WordTrace (prefixWord ++ tailWord_5188718) baseStart_5188718 baseEnd_5188718 := by
    simpa [prefixWord, tailWord_5188718, baseEnd_5188718] using wordTrace_append hprefix tailTrace_5188718
  have hstable : (prefixWord ++ tailWord_5188718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188718).length < 2 ^ (prefixWord ++ tailWord_5188718).sum := by decide
  have hdescent : baseEnd_5188718 < baseStart_5188718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188733 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_5188733 : Nat := 118140960795 + 5188733 * 2 ^ 59
def prefixEnd_5188733 : Nat := 4983230072969 + 3 ^ 40 * 5188733 * 2
def baseEnd_5188733 : Nat := 888104672281850930658319

theorem tailTrace_5188733 : CollatzResearch.WordTrace tailWord_5188733 prefixEnd_5188733 888104672281850930658319 := by
  unfold tailWord_5188733
  simp only [CollatzResearch.WordTrace]
  refine ⟨189248639911113980890306853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126165759940742653926871235 189248639911113980890306853)
  ·
    refine ⟨35484119983333871416932535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189248639911113980890306853 35484119983333871416932535)
    ·
      refine ⟨53226179975000807125398803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35484119983333871416932535 53226179975000807125398803)
      ·
        refine ⟨79839269962501210688098205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53226179975000807125398803 79839269962501210688098205)
        ·
          refine ⟨29939726235937954008036827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79839269962501210688098205 29939726235937954008036827)
          ·
            refine ⟨44909589353906931012055241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29939726235937954008036827 44909589353906931012055241)
            ·
              refine ⟨33682192015430198259041431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44909589353906931012055241 33682192015430198259041431)
              ·
                refine ⟨50523288023145297388562147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33682192015430198259041431 50523288023145297388562147)
                ·
                  refine ⟨75784932034717946082843221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50523288023145297388562147 75784932034717946082843221)
                  ·
                    refine ⟨888104672281850930658319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75784932034717946082843221 888104672281850930658319)
                    ·
                      rfl

theorem cell23_5188733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_5188733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188733 prefixEnd_5188733 := by exact prefixLift 5188733
  have htrace : WordTrace (prefixWord ++ tailWord_5188733) baseStart_5188733 baseEnd_5188733 := by
    simpa [prefixWord, tailWord_5188733, baseEnd_5188733] using wordTrace_append hprefix tailTrace_5188733
  have hstable : (prefixWord ++ tailWord_5188733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188733).length < 2 ^ (prefixWord ++ tailWord_5188733).sum := by decide
  have hdescent : baseEnd_5188733 < baseStart_5188733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188744 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_5188744 : Nat := 118140960795 + 5188744 * 2 ^ 59
def prefixEnd_5188744 : Nat := 4983230072969 + 3 ^ 40 * 5188744 * 2
def baseEnd_5188744 : Nat := 2664319665132752248937407

theorem tailTrace_5188744 : CollatzResearch.WordTrace tailWord_5188744 prefixEnd_5188744 2664319665132752248937407 := by
  unfold tailWord_5188744
  simp only [CollatzResearch.WordTrace]
  refine ⟨94624520557037064884478643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126166027409382753179304857 94624520557037064884478643)
  ·
    refine ⟨141936780835555597326717965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94624520557037064884478643 141936780835555597326717965)
    ·
      refine ⟨53226292813333348997519237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141936780835555597326717965 53226292813333348997519237)
      ·
        refine ⟨9979929902500002937034857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53226292813333348997519237 9979929902500002937034857)
        ·
          refine ⟨7484947426875002202776143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9979929902500002937034857 7484947426875002202776143)
          ·
            refine ⟨11227421140312503304164215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7484947426875002202776143 11227421140312503304164215)
            ·
              refine ⟨16841131710468754956246323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11227421140312503304164215 16841131710468754956246323)
              ·
                refine ⟨25261697565703132434369485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16841131710468754956246323 25261697565703132434369485)
                ·
                  refine ⟨9473136587138674662888557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25261697565703132434369485 9473136587138674662888557)
                  ·
                    refine ⟨3552426220177002998583209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9473136587138674662888557 3552426220177002998583209)
                    ·
                      refine ⟨2664319665132752248937407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552426220177002998583209 2664319665132752248937407)
                      ·
                        rfl

theorem cell23_5188744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_5188744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188744 prefixEnd_5188744 := by exact prefixLift 5188744
  have htrace : WordTrace (prefixWord ++ tailWord_5188744) baseStart_5188744 baseEnd_5188744 := by
    simpa [prefixWord, tailWord_5188744, baseEnd_5188744] using wordTrace_append hprefix tailTrace_5188744
  have hstable : (prefixWord ++ tailWord_5188744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188744).length < 2 ^ (prefixWord ++ tailWord_5188744).sum := by decide
  have hdescent : baseEnd_5188744 < baseStart_5188744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188757 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_5188757 : Nat := 118140960795 + 5188757 * 2 ^ 59
def prefixEnd_5188757 : Nat := 4983230072969 + 3 ^ 40 * 5188757 * 2
def baseEnd_5188757 : Nat := 2664326340381260698074847

theorem tailTrace_5188757 : CollatzResearch.WordTrace tailWord_5188757 prefixEnd_5188757 2664326340381260698074847 := by
  unfold tailWord_5188757
  simp only [CollatzResearch.WordTrace]
  refine ⟨189249515263027032989180525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126166343508684688659453683 189249515263027032989180525)
  ·
    refine ⟨70968568223635137370942697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189249515263027032989180525 70968568223635137370942697)
    ·
      refine ⟨53226426167726353028207023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70968568223635137370942697 53226426167726353028207023)
      ·
        refine ⟨79839639251589529542310535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53226426167726353028207023 79839639251589529542310535)
        ·
          refine ⟨119759458877384294313465803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79839639251589529542310535 119759458877384294313465803)
          ·
            refine ⟨179639188316076441470198705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119759458877384294313465803 179639188316076441470198705)
            ·
              refine ⟨134729391237057331102649029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179639188316076441470198705 134729391237057331102649029)
              ·
                refine ⟨25261760856948249581746693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134729391237057331102649029 25261760856948249581746693)
                ·
                  refine ⟨4736580160677796796577505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25261760856948249581746693 4736580160677796796577505)
                  ·
                    refine ⟨3552435120508347597433129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4736580160677796796577505 3552435120508347597433129)
                    ·
                      refine ⟨2664326340381260698074847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552435120508347597433129 2664326340381260698074847)
                      ·
                        rfl

theorem cell23_5188757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_5188757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188757 prefixEnd_5188757 := by exact prefixLift 5188757
  have htrace : WordTrace (prefixWord ++ tailWord_5188757) baseStart_5188757 baseEnd_5188757 := by
    simpa [prefixWord, tailWord_5188757, baseEnd_5188757] using wordTrace_append hprefix tailTrace_5188757
  have hstable : (prefixWord ++ tailWord_5188757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188757).length < 2 ^ (prefixWord ++ tailWord_5188757).sum := by decide
  have hdescent : baseEnd_5188757 < baseStart_5188757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188760 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5188760 : Nat := 118140960795 + 5188760 * 2 ^ 59
def prefixEnd_5188760 : Nat := 4983230072969 + 3 ^ 40 * 5188760 * 2
def baseEnd_5188760 : Nat := 2664327880823224186337333

theorem tailTrace_5188760 : CollatzResearch.WordTrace tailWord_5188760 prefixEnd_5188760 2664327880823224186337333 := by
  unfold tailWord_5188760
  simp only [CollatzResearch.WordTrace]
  refine ⟨94624812341008082250769867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126166416454677443001026489 94624812341008082250769867)
  ·
    refine ⟨141937218511512123376154801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94624812341008082250769867 141937218511512123376154801)
    ·
      refine ⟨106452913883634092532116101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141937218511512123376154801 106452913883634092532116101)
      ·
        refine ⟨19959921353181392349771769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106452913883634092532116101 19959921353181392349771769)
        ·
          refine ⟨14969941014886044262328827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19959921353181392349771769 14969941014886044262328827)
          ·
            refine ⟨22454911522329066393493241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14969941014886044262328827 22454911522329066393493241)
            ·
              refine ⟨16841183641746799795119931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22454911522329066393493241 16841183641746799795119931)
              ·
                refine ⟨25261775462620199692679897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16841183641746799795119931 25261775462620199692679897)
                ·
                  refine ⟨18946331596965149769509923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25261775462620199692679897 18946331596965149769509923)
                  ·
                    refine ⟨28419497395447724654264885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18946331596965149769509923 28419497395447724654264885)
                    ·
                      refine ⟨2664327880823224186337333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28419497395447724654264885 2664327880823224186337333)
                      ·
                        rfl

theorem cell23_5188760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5188760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188760 prefixEnd_5188760 := by exact prefixLift 5188760
  have htrace : WordTrace (prefixWord ++ tailWord_5188760) baseStart_5188760 baseEnd_5188760 := by
    simpa [prefixWord, tailWord_5188760, baseEnd_5188760] using wordTrace_append hprefix tailTrace_5188760
  have hstable : (prefixWord ++ tailWord_5188760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188760).length < 2 ^ (prefixWord ++ tailWord_5188760).sum := by decide
  have hdescent : baseEnd_5188760 < baseStart_5188760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188803 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 5]
def baseStart_5188803 : Nat := 118140960795 + 5188803 * 2 ^ 59
def prefixEnd_5188803 : Nat := 4983230072969 + 3 ^ 40 * 5188803 * 2
def baseEnd_5188803 : Nat := 2664349960491367518099635

theorem tailTrace_5188803 : CollatzResearch.WordTrace tailWord_5188803 prefixEnd_5188803 2664349960491367518099635 := by
  unfold tailWord_5188803
  simp only [CollatzResearch.WordTrace]
  refine ⟨189251193020860382845355063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126167462013906921896903375 189251193020860382845355063)
  ·
    refine ⟨283876789531290574268032595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189251193020860382845355063 283876789531290574268032595)
    ·
      refine ⟨425815184296935861402048893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283876789531290574268032595 425815184296935861402048893)
      ·
        refine ⟨159680694111350948025768335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425815184296935861402048893 159680694111350948025768335)
        ·
          refine ⟨239521041167026422038652503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159680694111350948025768335 239521041167026422038652503)
          ·
            refine ⟨359281561750539633057978755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239521041167026422038652503 359281561750539633057978755)
            ·
              refine ⟨538922342625809449586968133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359281561750539633057978755 538922342625809449586968133)
              ·
                refine ⟨101047939242339271797556525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 538922342625809449586968133 101047939242339271797556525)
                ·
                  refine ⟨37892977215877226924083697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101047939242339271797556525 37892977215877226924083697)
                  ·
                    refine ⟨28419732911907920193062773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37892977215877226924083697 28419732911907920193062773)
                    ·
                      refine ⟨2664349960491367518099635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28419732911907920193062773 2664349960491367518099635)
                      ·
                        rfl

theorem cell23_5188803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_5188803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188803 prefixEnd_5188803 := by exact prefixLift 5188803
  have htrace : WordTrace (prefixWord ++ tailWord_5188803) baseStart_5188803 baseEnd_5188803 := by
    simpa [prefixWord, tailWord_5188803, baseEnd_5188803] using wordTrace_append hprefix tailTrace_5188803
  have hstable : (prefixWord ++ tailWord_5188803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188803).length < 2 ^ (prefixWord ++ tailWord_5188803).sum := by decide
  have hdescent : baseEnd_5188803 < baseStart_5188803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188810 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_5188810 : Nat := 118140960795 + 5188810 * 2 ^ 59
def prefixEnd_5188810 : Nat := 4983230072969 + 3 ^ 40 * 5188810 * 2
def baseEnd_5188810 : Nat := 888117851618649663570701

theorem tailTrace_5188810 : CollatzResearch.WordTrace tailWord_5188810 prefixEnd_5188810 888117851618649663570701 := by
  unfold tailWord_5188810
  simp only [CollatzResearch.WordTrace]
  refine ⟨47312862082958755760214971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126167632221223348693906589 47312862082958755760214971)
  ·
    refine ⟨70969293124438133640322457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47312862082958755760214971 70969293124438133640322457)
    ·
      refine ⟨53226969843328600230241843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70969293124438133640322457 53226969843328600230241843)
      ·
        refine ⟨79840454764992900345362765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53226969843328600230241843 79840454764992900345362765)
        ·
          refine ⟨29940170536872337629511037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79840454764992900345362765 29940170536872337629511037)
          ·
            refine ⟨11227563951327126611066639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29940170536872337629511037 11227563951327126611066639)
            ·
              refine ⟨16841345926990689916599959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11227563951327126611066639 16841345926990689916599959)
              ·
                refine ⟨25262018890486034874899939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16841345926990689916599959 25262018890486034874899939)
                ·
                  refine ⟨37893028335729052312349909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25262018890486034874899939 37893028335729052312349909)
                  ·
                    refine ⟨888117851618649663570701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37893028335729052312349909 888117851618649663570701)
                    ·
                      rfl

theorem cell23_5188810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_5188810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188810 prefixEnd_5188810 := by exact prefixLift 5188810
  have htrace : WordTrace (prefixWord ++ tailWord_5188810) baseStart_5188810 baseEnd_5188810 := by
    simpa [prefixWord, tailWord_5188810, baseEnd_5188810] using wordTrace_append hprefix tailTrace_5188810
  have hstable : (prefixWord ++ tailWord_5188810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188810).length < 2 ^ (prefixWord ++ tailWord_5188810).sum := by decide
  have hdescent : baseEnd_5188810 < baseStart_5188810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188814 : List Nat := [4, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_5188814 : Nat := 118140960795 + 5188814 * 2 ^ 59
def prefixEnd_5188814 : Nat := 4983230072969 + 3 ^ 40 * 5188814 * 2
def baseEnd_5188814 : Nat := 296039512086507441673565

theorem tailTrace_5188814 : CollatzResearch.WordTrace tailWord_5188814 prefixEnd_5188814 296039512086507441673565 := by
  unfold tailWord_5188814
  simp only [CollatzResearch.WordTrace]
  refine ⟨23656449277977566465500687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126167729482547021149336997 23656449277977566465500687)
  ·
    refine ⟨35484673916966349698251031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23656449277977566465500687 35484673916966349698251031)
    ·
      refine ⟨53227010875449524547376547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35484673916966349698251031 53227010875449524547376547)
      ·
        refine ⟨79840516313174286821064821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53227010875449524547376547 79840516313174286821064821)
        ·
          refine ⟨7485048404360089389474827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79840516313174286821064821 7485048404360089389474827)
          ·
            refine ⟨11227572606540134084212241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7485048404360089389474827 11227572606540134084212241)
            ·
              refine ⟨8420679454905100563159181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11227572606540134084212241 8420679454905100563159181)
              ·
                refine ⟨3157754795589412711184693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8420679454905100563159181 3157754795589412711184693)
                ·
                  refine ⟨296039512086507441673565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3157754795589412711184693 296039512086507441673565)
                  ·
                    rfl

theorem cell23_5188814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_5188814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188814 prefixEnd_5188814 := by exact prefixLift 5188814
  have htrace : WordTrace (prefixWord ++ tailWord_5188814) baseStart_5188814 baseEnd_5188814 := by
    simpa [prefixWord, tailWord_5188814, baseEnd_5188814] using wordTrace_append hprefix tailTrace_5188814
  have hstable : (prefixWord ++ tailWord_5188814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188814).length < 2 ^ (prefixWord ++ tailWord_5188814).sum := by decide
  have hdescent : baseEnd_5188814 < baseStart_5188814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188904 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 6]
def baseStart_5188904 : Nat := 118140960795 + 5188904 * 2 ^ 59
def prefixEnd_5188904 : Nat := 4983230072969 + 3 ^ 40 * 5188904 * 2
def baseEnd_5188904 : Nat := 296044646893052402548519

theorem tailTrace_5188904 : CollatzResearch.WordTrace tailWord_5188904 prefixEnd_5188904 296044646893052402548519 := by
  unfold tailWord_5188904
  simp only [CollatzResearch.WordTrace]
  refine ⟨94627438396747238547390883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126169917862329651396521177 94627438396747238547390883)
  ·
    refine ⟨141941157595120857821086325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94627438396747238547390883 141941157595120857821086325)
    ·
      refine ⟨13306983524542580420726843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141941157595120857821086325 13306983524542580420726843)
      ·
        refine ⟨19960475286813870631090265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13306983524542580420726843 19960475286813870631090265)
        ·
          refine ⟨14970356465110402973317699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19960475286813870631090265 14970356465110402973317699)
          ·
            refine ⟨22455534697665604459976549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14970356465110402973317699 22455534697665604459976549)
            ·
              refine ⟨4210412755812300836245603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22455534697665604459976549 4210412755812300836245603)
              ·
                refine ⟨6315619133718451254368405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210412755812300836245603 6315619133718451254368405)
                ·
                  refine ⟨296044646893052402548519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6315619133718451254368405 296044646893052402548519)
                  ·
                    rfl

theorem cell23_5188904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 6].length) (baseStart_5188904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188904 prefixEnd_5188904 := by exact prefixLift 5188904
  have htrace : WordTrace (prefixWord ++ tailWord_5188904) baseStart_5188904 baseEnd_5188904 := by
    simpa [prefixWord, tailWord_5188904, baseEnd_5188904] using wordTrace_append hprefix tailTrace_5188904
  have hstable : (prefixWord ++ tailWord_5188904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188904).length < 2 ^ (prefixWord ++ tailWord_5188904).sum := by decide
  have hdescent : baseEnd_5188904 < baseStart_5188904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188917 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_5188917 : Nat := 118140960795 + 5188917 * 2 ^ 59
def prefixEnd_5188917 : Nat := 4983230072969 + 3 ^ 40 * 5188917 * 2
def baseEnd_5188917 : Nat := 888136165761993357358037

theorem tailTrace_5188917 : CollatzResearch.WordTrace tailWord_5188917 prefixEnd_5188917 888136165761993357358037 := by
  unfold tailWord_5188917
  simp only [CollatzResearch.WordTrace]
  refine ⟨189255350942447380315005005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126170233961631586876670003 189255350942447380315005005)
  ·
    refine ⟨70970756603417767618126877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189255350942447380315005005 70970756603417767618126877)
    ·
      refine ⟨26614033726281662856797579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70970756603417767618126877 26614033726281662856797579)
      ·
        refine ⟨39921050589422494285196369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26614033726281662856797579 39921050589422494285196369)
        ·
          refine ⟨29940787942066870713897277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39921050589422494285196369 29940787942066870713897277)
          ·
            refine ⟨11227795478275076517711479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29940787942066870713897277 11227795478275076517711479)
            ·
              refine ⟨16841693217412614776567219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11227795478275076517711479 16841693217412614776567219)
              ·
                refine ⟨25262539826118922164850829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16841693217412614776567219 25262539826118922164850829)
                ·
                  refine ⟨9473452434794595811819061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25262539826118922164850829 9473452434794595811819061)
                  ·
                    refine ⟨888136165761993357358037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9473452434794595811819061 888136165761993357358037)
                    ·
                      rfl

theorem cell23_5188917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_5188917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188917 prefixEnd_5188917 := by exact prefixLift 5188917
  have htrace : WordTrace (prefixWord ++ tailWord_5188917) baseStart_5188917 baseEnd_5188917 := by
    simpa [prefixWord, tailWord_5188917, baseEnd_5188917] using wordTrace_append hprefix tailTrace_5188917
  have hstable : (prefixWord ++ tailWord_5188917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188917).length < 2 ^ (prefixWord ++ tailWord_5188917).sum := by decide
  have hdescent : baseEnd_5188917 < baseStart_5188917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188918 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5188918 : Nat := 118140960795 + 5188918 * 2 ^ 59
def prefixEnd_5188918 : Nat := 4983230072969 + 3 ^ 40 * 5188918 * 2
def baseEnd_5188918 : Nat := 2664409010766634568161607

theorem tailTrace_5188918 : CollatzResearch.WordTrace tailWord_5188918 prefixEnd_5188918 2664409010766634568161607 := by
  unfold tailWord_5188918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11828461713465234842861963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126170258276962504990527605 11828461713465234842861963)
  ·
    refine ⟨17742692570197852264292945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11828461713465234842861963 17742692570197852264292945)
    ·
      refine ⟨13307019427648389198219709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17742692570197852264292945 13307019427648389198219709)
      ·
        refine ⟨4990132285368145949332391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13307019427648389198219709 4990132285368145949332391)
        ·
          refine ⟨7485198428052218923998587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4990132285368145949332391 7485198428052218923998587)
          ·
            refine ⟨11227797642078328385997881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7485198428052218923998587 11227797642078328385997881)
            ·
              refine ⟨8420848231558746289498411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11227797642078328385997881 8420848231558746289498411)
              ·
                refine ⟨12631272347338119434247617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8420848231558746289498411 12631272347338119434247617)
                ·
                  refine ⟨9473454260503589575685713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12631272347338119434247617 9473454260503589575685713)
                  ·
                    refine ⟨7105090695377692181764285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9473454260503589575685713 7105090695377692181764285)
                    ·
                      refine ⟨2664409010766634568161607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7105090695377692181764285 2664409010766634568161607)
                      ·
                        rfl

theorem cell23_5188918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5188918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188918 prefixEnd_5188918 := by exact prefixLift 5188918
  have htrace : WordTrace (prefixWord ++ tailWord_5188918) baseStart_5188918 baseEnd_5188918 := by
    simpa [prefixWord, tailWord_5188918, baseEnd_5188918] using wordTrace_append hprefix tailTrace_5188918
  have hstable : (prefixWord ++ tailWord_5188918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188918).length < 2 ^ (prefixWord ++ tailWord_5188918).sum := by decide
  have hdescent : baseEnd_5188918 < baseStart_5188918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188924 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_5188924 : Nat := 118140960795 + 5188924 * 2 ^ 59
def prefixEnd_5188924 : Nat := 4983230072969 + 3 ^ 40 * 5188924 * 2
def baseEnd_5188924 : Nat := 2664412091650561544686579

theorem tailTrace_5188924 : CollatzResearch.WordTrace tailWord_5188924 prefixEnd_5188924 2664412091650561544686579 := by
  unfold tailWord_5188924
  simp only [CollatzResearch.WordTrace]
  refine ⟨94627803126711010255254913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126170404168948013673673217 94627803126711010255254913)
  ·
    refine ⟨70970852345033257691441185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94627803126711010255254913 70970852345033257691441185)
    ·
      refine ⟨53228139258774943268580889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70970852345033257691441185 53228139258774943268580889)
      ·
        refine ⟨39921104444081207451435667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53228139258774943268580889 39921104444081207451435667)
        ·
          refine ⟨59881656666121811177153501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39921104444081207451435667 59881656666121811177153501)
          ·
            refine ⟨22455621249795679191432563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59881656666121811177153501 22455621249795679191432563)
            ·
              refine ⟨33683431874693518787148845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22455621249795679191432563 33683431874693518787148845)
              ·
                refine ⟨12631286953010069545180817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33683431874693518787148845 12631286953010069545180817)
                ·
                  refine ⟨9473465214757552158885613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12631286953010069545180817 9473465214757552158885613)
                  ·
                    refine ⟨3552549455534082059582105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9473465214757552158885613 3552549455534082059582105)
                    ·
                      refine ⟨2664412091650561544686579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552549455534082059582105 2664412091650561544686579)
                      ·
                        rfl

theorem cell23_5188924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_5188924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188924 prefixEnd_5188924 := by exact prefixLift 5188924
  have htrace : WordTrace (prefixWord ++ tailWord_5188924) baseStart_5188924 baseEnd_5188924 := by
    simpa [prefixWord, tailWord_5188924, baseEnd_5188924] using wordTrace_append hprefix tailTrace_5188924
  have hstable : (prefixWord ++ tailWord_5188924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188924).length < 2 ^ (prefixWord ++ tailWord_5188924).sum := by decide
  have hdescent : baseEnd_5188924 < baseStart_5188924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188937 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 4]
def baseStart_5188937 : Nat := 118140960795 + 5188937 * 2 ^ 59
def prefixEnd_5188937 : Nat := 4983230072969 + 3 ^ 40 * 5188937 * 2
def baseEnd_5188937 : Nat := 2664418766899069993824019

theorem tailTrace_5188937 : CollatzResearch.WordTrace tailWord_5188937 prefixEnd_5188937 2664418766899069993824019 := by
  unfold tailWord_5188937
  simp only [CollatzResearch.WordTrace]
  refine ⟨189256080402374923730733065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126170720268249949153822043 189256080402374923730733065)
  ·
    refine ⟨141942060301781192798049799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189256080402374923730733065 141942060301781192798049799)
    ·
      refine ⟨212913090452671789197074699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141942060301781192798049799 212913090452671789197074699)
      ·
        refine ⟨319369635679007683795612049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212913090452671789197074699 319369635679007683795612049)
        ·
          refine ⟨239527226759255762846709037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319369635679007683795612049 239527226759255762846709037)
          ·
            refine ⟨89822710034720911067515889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239527226759255762846709037 89822710034720911067515889)
            ·
              refine ⟨67367032526040683300636917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89822710034720911067515889 67367032526040683300636917)
              ·
                refine ⟨6315659299316314059434711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67367032526040683300636917 6315659299316314059434711)
                ·
                  refine ⟨9473488948974471089152067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6315659299316314059434711 9473488948974471089152067)
                  ·
                    refine ⟨14210233423461706633728101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9473488948974471089152067 14210233423461706633728101)
                    ·
                      refine ⟨2664418766899069993824019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14210233423461706633728101 2664418766899069993824019)
                      ·
                        rfl

theorem cell23_5188937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 4].length) (baseStart_5188937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188937 prefixEnd_5188937 := by exact prefixLift 5188937
  have htrace : WordTrace (prefixWord ++ tailWord_5188937) baseStart_5188937 baseEnd_5188937 := by
    simpa [prefixWord, tailWord_5188937, baseEnd_5188937] using wordTrace_append hprefix tailTrace_5188937
  have hstable : (prefixWord ++ tailWord_5188937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188937).length < 2 ^ (prefixWord ++ tailWord_5188937).sum := by decide
  have hdescent : baseEnd_5188937 < baseStart_5188937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188964 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_5188964 : Nat := 118140960795 + 5188964 * 2 ^ 59
def prefixEnd_5188964 : Nat := 4983230072969 + 3 ^ 40 * 5188964 * 2
def baseEnd_5188964 : Nat := 888144210292247129395465

theorem tailTrace_5188964 : CollatzResearch.WordTrace tailWord_5188964 prefixEnd_5188964 888144210292247129395465 := by
  unfold tailWord_5188964
  simp only [CollatzResearch.WordTrace]
  refine ⟨94628532586638553670982973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126171376782184738227977297 94628532586638553670982973)
  ·
    refine ⟨35485699719989457626618615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94628532586638553670982973 35485699719989457626618615)
    ·
      refine ⟨53228549579984186439927923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35485699719989457626618615 53228549579984186439927923)
      ·
        refine ⟨79842824369976279659891885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53228549579984186439927923 79842824369976279659891885)
        ·
          refine ⟨29941059138741104872459457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79842824369976279659891885 29941059138741104872459457)
          ·
            refine ⟨22455794354055828654344593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29941059138741104872459457 22455794354055828654344593)
            ·
              refine ⟨16841845765541871490758445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22455794354055828654344593 16841845765541871490758445)
              ·
                refine ⟨6315692162078201809034417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16841845765541871490758445 6315692162078201809034417)
                ·
                  refine ⟨4736769121558651356775813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6315692162078201809034417 4736769121558651356775813)
                  ·
                    refine ⟨888144210292247129395465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4736769121558651356775813 888144210292247129395465)
                    ·
                      rfl

theorem cell23_5188964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_5188964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188964 prefixEnd_5188964 := by exact prefixLift 5188964
  have htrace : WordTrace (prefixWord ++ tailWord_5188964) baseStart_5188964 baseEnd_5188964 := by
    simpa [prefixWord, tailWord_5188964, baseEnd_5188964] using wordTrace_append hprefix tailTrace_5188964
  have hstable : (prefixWord ++ tailWord_5188964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188964).length < 2 ^ (prefixWord ++ tailWord_5188964).sum := by decide
  have hdescent : baseEnd_5188964 < baseStart_5188964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188987 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 3]
def baseStart_5188987 : Nat := 118140960795 + 5188987 * 2 ^ 59
def prefixEnd_5188987 : Nat := 4983230072969 + 3 ^ 40 * 5188987 * 2
def baseEnd_5188987 : Nat := 2664444440931794798198789

theorem tailTrace_5188987 : CollatzResearch.WordTrace tailWord_5188987 prefixEnd_5188987 2664444440931794798198789 := by
  unfold tailWord_5188987
  simp only [CollatzResearch.WordTrace]
  refine ⟨189257904052193782270053215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126171936034795854846702143 189257904052193782270053215)
  ·
    refine ⟨283886856078290673405079823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189257904052193782270053215 283886856078290673405079823)
    ·
      refine ⟨425830284117436010107619735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283886856078290673405079823 425830284117436010107619735)
      ·
        refine ⟨638745426176154015161429603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425830284117436010107619735 638745426176154015161429603)
        ·
          refine ⟨958118139264231022742144405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638745426176154015161429603 958118139264231022742144405)
          ·
            refine ⟨44911787778010829191038019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 958118139264231022742144405 44911787778010829191038019)
            ·
              refine ⟨67367681667016243786557029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44911787778010829191038019 67367681667016243786557029)
              ·
                refine ⟨12631440312565545709979443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67367681667016243786557029 12631440312565545709979443)
                ·
                  refine ⟨18947160468848318564969165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12631440312565545709979443 18947160468848318564969165)
                  ·
                    refine ⟨7105185175818119461863437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18947160468848318564969165 7105185175818119461863437)
                    ·
                      refine ⟨2664444440931794798198789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7105185175818119461863437 2664444440931794798198789)
                      ·
                        rfl

theorem cell23_5188987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 3].length) (baseStart_5188987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188987 prefixEnd_5188987 := by exact prefixLift 5188987
  have htrace : WordTrace (prefixWord ++ tailWord_5188987) baseStart_5188987 baseEnd_5188987 := by
    simpa [prefixWord, tailWord_5188987, baseEnd_5188987] using wordTrace_append hprefix tailTrace_5188987
  have hstable : (prefixWord ++ tailWord_5188987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188987).length < 2 ^ (prefixWord ++ tailWord_5188987).sum := by decide
  have hdescent : baseEnd_5188987 < baseStart_5188987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188988 : List Nat := [2, 2, 2, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_5188988 : Nat := 118140960795 + 5188988 * 2 ^ 59
def prefixEnd_5188988 : Nat := 4983230072969 + 3 ^ 40 * 5188988 * 2
def baseEnd_5188988 : Nat := 2664444954412449294286285

theorem tailTrace_5188988 : CollatzResearch.WordTrace tailWord_5188988 prefixEnd_5188988 2664444954412449294286285 := by
  unfold tailWord_5188988
  simp only [CollatzResearch.WordTrace]
  refine ⟨94628970262595079720419809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126171960350126772960559745 94628970262595079720419809)
  ·
    refine ⟨70971727696946309790314857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94628970262595079720419809 70971727696946309790314857)
    ·
      refine ⟨53228795772709732342736143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70971727696946309790314857 53228795772709732342736143)
      ·
        refine ⟨79843193659064598514104215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53228795772709732342736143 79843193659064598514104215)
        ·
          refine ⟨119764790488596897771156323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79843193659064598514104215 119764790488596897771156323)
          ·
            refine ⟨179647185732895346656734485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119764790488596897771156323 179647185732895346656734485)
            ·
              refine ⟨8420961831229469374534429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179647185732895346656734485 8420961831229469374534429)
              ·
                refine ⟨3157860686711051015450411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8420961831229469374534429 3157860686711051015450411)
                ·
                  refine ⟨4736791030066576523175617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3157860686711051015450411 4736791030066576523175617)
                  ·
                    refine ⟨3552593272549932392381713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4736791030066576523175617 3552593272549932392381713)
                    ·
                      refine ⟨2664444954412449294286285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552593272549932392381713 2664444954412449294286285)
                      ·
                        rfl

theorem cell23_5188988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_5188988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188988 prefixEnd_5188988 := by exact prefixLift 5188988
  have htrace : WordTrace (prefixWord ++ tailWord_5188988) baseStart_5188988 baseEnd_5188988 := by
    simpa [prefixWord, tailWord_5188988, baseEnd_5188988] using wordTrace_append hprefix tailTrace_5188988
  have hstable : (prefixWord ++ tailWord_5188988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188988).length < 2 ^ (prefixWord ++ tailWord_5188988).sum := by decide
  have hdescent : baseEnd_5188988 < baseStart_5188988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5188994 : List Nat := [3, 4, 2, 1, 1, 2, 10]
def baseStart_5188994 : Nat := 118140960795 + 5188994 * 2 ^ 59
def prefixEnd_5188994 : Nat := 4983230072969 + 3 ^ 40 * 5188994 * 2
def baseEnd_5188994 : Nat := 32894420188844151491497

theorem tailTrace_5188994 : CollatzResearch.WordTrace tailWord_5188994 prefixEnd_5188994 32894420188844151491497 := by
  unfold tailWord_5188994
  simp only [CollatzResearch.WordTrace]
  refine ⟨47314539840792105616389509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126172106242112281643705357 47314539840792105616389509)
  ·
    refine ⟨8871476220148519803073033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47314539840792105616389509 8871476220148519803073033)
    ·
      refine ⟨6653607165111389852304775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8871476220148519803073033 6653607165111389852304775)
      ·
        refine ⟨9980410747667084778457163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6653607165111389852304775 9980410747667084778457163)
        ·
          refine ⟨14970616121500627167685745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9980410747667084778457163 14970616121500627167685745)
          ·
            refine ⟨11227962091125470375764309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14970616121500627167685745 11227962091125470375764309)
            ·
              refine ⟨32894420188844151491497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11227962091125470375764309 32894420188844151491497)
              ·
                rfl

theorem cell23_5188994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 10].length) (baseStart_5188994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5188994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5188994 prefixEnd_5188994 := by exact prefixLift 5188994
  have htrace : WordTrace (prefixWord ++ tailWord_5188994) baseStart_5188994 baseEnd_5188994 := by
    simpa [prefixWord, tailWord_5188994, baseEnd_5188994] using wordTrace_append hprefix tailTrace_5188994
  have hstable : (prefixWord ++ tailWord_5188994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5188994).length < 2 ^ (prefixWord ++ tailWord_5188994).sum := by decide
  have hdescent : baseEnd_5188994 < baseStart_5188994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5188994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189004 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_5189004 : Nat := 118140960795 + 5189004 * 2 ^ 59
def prefixEnd_5189004 : Nat := 4983230072969 + 3 ^ 40 * 5189004 * 2
def baseEnd_5189004 : Nat := 2664453170102921231686211

theorem tailTrace_5189004 : CollatzResearch.WordTrace tailWord_5189004 prefixEnd_5189004 2664453170102921231686211 := by
  unfold tailWord_5189004
  simp only [CollatzResearch.WordTrace]
  refine ⟨94629262046566097086711033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126172349395421462782281377 94629262046566097086711033)
  ·
    refine ⟨70971946534924572815033275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94629262046566097086711033 70971946534924572815033275)
    ·
      refine ⟨106457919802386859222549913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70971946534924572815033275 106457919802386859222549913)
      ·
        refine ⟨79843439851790144416912435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106457919802386859222549913 79843439851790144416912435)
        ·
          refine ⟨119765159777685216625368653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79843439851790144416912435 119765159777685216625368653)
          ·
            refine ⟨44911934916631956234513245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119765159777685216625368653 44911934916631956234513245)
            ·
              refine ⟨16841975593736983587942467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44911934916631956234513245 16841975593736983587942467)
              ·
                refine ⟨25262963390605475381913701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16841975593736983587942467 25262963390605475381913701)
                ·
                  refine ⟨4736805635738526634108819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25262963390605475381913701 4736805635738526634108819)
                  ·
                    refine ⟨7105208453607789951163229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4736805635738526634108819 7105208453607789951163229)
                    ·
                      refine ⟨2664453170102921231686211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7105208453607789951163229 2664453170102921231686211)
                      ·
                        rfl

theorem cell23_5189004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_5189004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189004 prefixEnd_5189004 := by exact prefixLift 5189004
  have htrace : WordTrace (prefixWord ++ tailWord_5189004) baseStart_5189004 baseEnd_5189004 := by
    simpa [prefixWord, tailWord_5189004, baseEnd_5189004] using wordTrace_append hprefix tailTrace_5189004
  have hstable : (prefixWord ++ tailWord_5189004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189004).length < 2 ^ (prefixWord ++ tailWord_5189004).sum := by decide
  have hdescent : baseEnd_5189004 < baseStart_5189004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189021 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_5189021 : Nat := 118140960795 + 5189021 * 2 ^ 59
def prefixEnd_5189021 : Nat := 4983230072969 + 3 ^ 40 * 5189021 * 2
def baseEnd_5189021 : Nat := 2664461899274047665173633

theorem tailTrace_5189021 : CollatzResearch.WordTrace tailWord_5189021 prefixEnd_5189021 2664461899274047665173633 := by
  unfold tailWord_5189021
  simp only [CollatzResearch.WordTrace]
  refine ⟨189259144134070606076790917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126172762756047070717860611 189259144134070606076790917)
  ·
    refine ⟨35486089525138238639398297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189259144134070606076790917 35486089525138238639398297)
    ·
      refine ⟨26614567143853678979548723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35486089525138238639398297 26614567143853678979548723)
      ·
        refine ⟨39921850715780518469323085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26614567143853678979548723 39921850715780518469323085)
        ·
          refine ⟨14970694018417694425996157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39921850715780518469323085 14970694018417694425996157)
          ·
            refine ⟨5614010256906635409748559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14970694018417694425996157 5614010256906635409748559)
            ·
              refine ⟨8421015385359953114622839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5614010256906635409748559 8421015385359953114622839)
              ·
                refine ⟨12631523078039929671934259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421015385359953114622839 12631523078039929671934259)
                ·
                  refine ⟨18947284617059894507901389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12631523078039929671934259 18947284617059894507901389)
                  ·
                    refine ⟨7105231731397460440463021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18947284617059894507901389 7105231731397460440463021)
                    ·
                      refine ⟨2664461899274047665173633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7105231731397460440463021 2664461899274047665173633)
                      ·
                        rfl

theorem cell23_5189021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_5189021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189021 prefixEnd_5189021 := by exact prefixLift 5189021
  have htrace : WordTrace (prefixWord ++ tailWord_5189021) baseStart_5189021 baseEnd_5189021 := by
    simpa [prefixWord, tailWord_5189021, baseEnd_5189021] using wordTrace_append hprefix tailTrace_5189021
  have hstable : (prefixWord ++ tailWord_5189021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189021).length < 2 ^ (prefixWord ++ tailWord_5189021).sum := by decide
  have hdescent : baseEnd_5189021 < baseStart_5189021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189047 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_5189047 : Nat := 118140960795 + 5189047 * 2 ^ 59
def prefixEnd_5189047 : Nat := 4983230072969 + 3 ^ 40 * 5189047 * 2
def baseEnd_5189047 : Nat := 2664475249771064563448513

theorem tailTrace_5189047 : CollatzResearch.WordTrace tailWord_5189047 prefixEnd_5189047 2664475249771064563448513 := by
  unfold tailWord_5189047
  simp only [CollatzResearch.WordTrace]
  refine ⟨189260092431976412517237395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126173394954650941678158263 189260092431976412517237395)
  ·
    refine ⟨283890138647964618775856093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189260092431976412517237395 283890138647964618775856093)
    ·
      refine ⟨106458801992986732040946035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283890138647964618775856093 106458801992986732040946035)
      ·
        refine ⟨159688202989480098061419053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106458801992986732040946035 159688202989480098061419053)
        ·
          refine ⟨59883076121055036773032145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159688202989480098061419053 59883076121055036773032145)
          ·
            refine ⟨44912307090791277579774109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59883076121055036773032145 44912307090791277579774109)
            ·
              refine ⟨16842115159046729092415291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44912307090791277579774109 16842115159046729092415291)
              ·
                refine ⟨25263172738570093638622937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16842115159046729092415291 25263172738570093638622937)
                ·
                  refine ⟨18947379553927570228967203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25263172738570093638622937 18947379553927570228967203)
                  ·
                    refine ⟨28421069330891355343450805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18947379553927570228967203 28421069330891355343450805)
                    ·
                      refine ⟨2664475249771064563448513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28421069330891355343450805 2664475249771064563448513)
                      ·
                        rfl

theorem cell23_5189047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_5189047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189047 prefixEnd_5189047 := by exact prefixLift 5189047
  have htrace : WordTrace (prefixWord ++ tailWord_5189047) baseStart_5189047 baseEnd_5189047 := by
    simpa [prefixWord, tailWord_5189047, baseEnd_5189047] using wordTrace_append hprefix tailTrace_5189047
  have hstable : (prefixWord ++ tailWord_5189047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189047).length < 2 ^ (prefixWord ++ tailWord_5189047).sum := by decide
  have hdescent : baseEnd_5189047 < baseStart_5189047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189067 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 7]
def baseStart_5189067 : Nat := 118140960795 + 5189067 * 2 ^ 59
def prefixEnd_5189067 : Nat := 4983230072969 + 3 ^ 40 * 5189067 * 2
def baseEnd_5189067 : Nat := 296053946598239387244269

theorem tailTrace_5189067 : CollatzResearch.WordTrace tailWord_5189067 prefixEnd_5189067 296053946598239387244269 := by
  unfold tailWord_5189067
  simp only [CollatzResearch.WordTrace]
  refine ⟨189260821891903955932965455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126173881261269303955310303 189260821891903955932965455)
  ·
    refine ⟨283891232837855933899448183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189260821891903955932965455 283891232837855933899448183)
    ·
      refine ⟨425836849256783900849172275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283891232837855933899448183 425836849256783900849172275)
      ·
        refine ⟨638755273885175851273758413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425836849256783900849172275 638755273885175851273758413)
        ·
          refine ⟨239533227706940944227659405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638755273885175851273758413 239533227706940944227659405)
          ·
            refine ⟨89824960390102854085372277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239533227706940944227659405 89824960390102854085372277)
            ·
              refine ⟨8421090036572142570503651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89824960390102854085372277 8421090036572142570503651)
              ·
                refine ⟨12631635054858213855755477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421090036572142570503651 12631635054858213855755477)
                ·
                  refine ⟨296053946598239387244269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12631635054858213855755477 296053946598239387244269)
                  ·
                    rfl

theorem cell23_5189067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 7].length) (baseStart_5189067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189067 prefixEnd_5189067 := by exact prefixLift 5189067
  have htrace : WordTrace (prefixWord ++ tailWord_5189067) baseStart_5189067 baseEnd_5189067 := by
    simpa [prefixWord, tailWord_5189067, baseEnd_5189067] using wordTrace_append hprefix tailTrace_5189067
  have hstable : (prefixWord ++ tailWord_5189067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189067).length < 2 ^ (prefixWord ++ tailWord_5189067).sum := by decide
  have hdescent : baseEnd_5189067 < baseStart_5189067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189157 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 8]
def baseStart_5189157 : Nat := 118140960795 + 5189157 * 2 ^ 59
def prefixEnd_5189157 : Nat := 4983230072969 + 3 ^ 40 * 5189157 * 2
def baseEnd_5189157 : Nat := 296059081404784348119223

theorem tailTrace_5189157 : CollatzResearch.WordTrace tailWord_5189157 prefixEnd_5189157 296059081404784348119223 := by
  unfold tailWord_5189157
  simp only [CollatzResearch.WordTrace]
  refine ⟨189264104461577901303741725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126176069641051934202494483 189264104461577901303741725)
  ·
    refine ⟨70974039173091712988903147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189264104461577901303741725 70974039173091712988903147)
    ·
      refine ⟨106461058759637569483354721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70974039173091712988903147 106461058759637569483354721)
      ·
        refine ⟨79845794069728177112516041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106461058759637569483354721 79845794069728177112516041)
        ·
          refine ⟨59884345552296132834387031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79845794069728177112516041 59884345552296132834387031)
          ·
            refine ⟨89826518328444199251580547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59884345552296132834387031 89826518328444199251580547)
            ·
              refine ⟨134739777492666298877370821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89826518328444199251580547 134739777492666298877370821)
              ·
                refine ⟨25263708279874931039507029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134739777492666298877370821 25263708279874931039507029)
                ·
                  refine ⟨296059081404784348119223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25263708279874931039507029 296059081404784348119223)
                  ·
                    rfl

theorem cell23_5189157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_5189157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189157 prefixEnd_5189157 := by exact prefixLift 5189157
  have htrace : WordTrace (prefixWord ++ tailWord_5189157) baseStart_5189157 baseEnd_5189157 := by
    simpa [prefixWord, tailWord_5189157, baseEnd_5189157] using wordTrace_append hprefix tailTrace_5189157
  have hstable : (prefixWord ++ tailWord_5189157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189157).length < 2 ^ (prefixWord ++ tailWord_5189157).sum := by decide
  have hdescent : baseEnd_5189157 < baseStart_5189157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189201 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_5189201 : Nat := 118140960795 + 5189201 * 2 ^ 59
def prefixEnd_5189201 : Nat := 4983230072969 + 3 ^ 40 * 5189201 * 2
def baseEnd_5189201 : Nat := 2664554325791856960922805

theorem tailTrace_5189201 : CollatzResearch.WordTrace tailWord_5189201 prefixEnd_5189201 2664554325791856960922805 := by
  unfold tailWord_5189201
  simp only [CollatzResearch.WordTrace]
  refine ⟨189265709273418496818343457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126177139515612331212228971 189265709273418496818343457)
  ·
    refine ⟨141949281955063872613757593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189265709273418496818343457 141949281955063872613757593)
    ·
      refine ⟨106461961466297904460318195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141949281955063872613757593 106461961466297904460318195)
      ·
        refine ⟨159692942199446856690477293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106461961466297904460318195 159692942199446856690477293)
        ·
          refine ⟨59884853324792571258928985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159692942199446856690477293 59884853324792571258928985)
          ·
            refine ⟨44913639993594428444196739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59884853324792571258928985 44913639993594428444196739)
            ·
              refine ⟨67370459990391642666295109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44913639993594428444196739 67370459990391642666295109)
              ·
                refine ⟨12631961248198432999930333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67370459990391642666295109 12631961248198432999930333)
                ·
                  refine ⟨4736985468074412374973875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12631961248198432999930333 4736985468074412374973875)
                  ·
                    refine ⟨7105478202111618562460813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4736985468074412374973875 7105478202111618562460813)
                    ·
                      refine ⟨2664554325791856960922805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7105478202111618562460813 2664554325791856960922805)
                      ·
                        rfl

theorem cell23_5189201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_5189201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189201 prefixEnd_5189201 := by exact prefixLift 5189201
  have htrace : WordTrace (prefixWord ++ tailWord_5189201) baseStart_5189201 baseEnd_5189201 := by
    simpa [prefixWord, tailWord_5189201, baseEnd_5189201] using wordTrace_append hprefix tailTrace_5189201
  have hstable : (prefixWord ++ tailWord_5189201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189201).length < 2 ^ (prefixWord ++ tailWord_5189201).sum := by decide
  have hdescent : baseEnd_5189201 < baseStart_5189201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189221 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_5189221 : Nat := 118140960795 + 5189221 * 2 ^ 59
def prefixEnd_5189221 : Nat := 4983230072969 + 3 ^ 40 * 5189221 * 2
def baseEnd_5189221 : Nat := 888188198468315627557571

theorem tailTrace_5189221 : CollatzResearch.WordTrace tailWord_5189221 prefixEnd_5189221 888188198468315627557571 := by
  unfold tailWord_5189221
  simp only [CollatzResearch.WordTrace]
  refine ⟨189266438733346040234071517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126177625822230693489381011 189266438733346040234071517)
  ·
    refine ⟨70974914525004765087776819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189266438733346040234071517 70974914525004765087776819)
    ·
      refine ⟨106462371787507147631665229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70974914525004765087776819 106462371787507147631665229)
      ·
        refine ⟨39923389420315180361874461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106462371787507147631665229 39923389420315180361874461)
        ·
          refine ⟨14971271032618192635702923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39923389420315180361874461 14971271032618192635702923)
          ·
            refine ⟨22456906548927288953554385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14971271032618192635702923 22456906548927288953554385)
            ·
              refine ⟨16842679911695466715165789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22456906548927288953554385 16842679911695466715165789)
              ·
                refine ⟨6316004966885800018187171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16842679911695466715165789 6316004966885800018187171)
                ·
                  refine ⟨9474007450328700027280757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316004966885800018187171 9474007450328700027280757)
                  ·
                    refine ⟨888188198468315627557571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9474007450328700027280757 888188198468315627557571)
                    ·
                      rfl

theorem cell23_5189221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_5189221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189221 prefixEnd_5189221 := by exact prefixLift 5189221
  have htrace : WordTrace (prefixWord ++ tailWord_5189221) baseStart_5189221 baseEnd_5189221 := by
    simpa [prefixWord, tailWord_5189221, baseEnd_5189221] using wordTrace_append hprefix tailTrace_5189221
  have hstable : (prefixWord ++ tailWord_5189221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189221).length < 2 ^ (prefixWord ++ tailWord_5189221).sum := by decide
  have hdescent : baseEnd_5189221 < baseStart_5189221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189244 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_5189244 : Nat := 118140960795 + 5189244 * 2 ^ 59
def prefixEnd_5189244 : Nat := 4983230072969 + 3 ^ 40 * 5189244 * 2
def baseEnd_5189244 : Nat := 2664576405460000292685107

theorem tailTrace_5189244 : CollatzResearch.WordTrace tailWord_5189244 prefixEnd_5189244 2664576405460000292685107 := by
  unfold tailWord_5189244
  simp only [CollatzResearch.WordTrace]
  refine ⟨94633638806131357581079393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126178185074841810108105857 94633638806131357581079393)
  ·
    refine ⟨70975229104598518185809545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94633638806131357581079393 70975229104598518185809545)
    ·
      refine ⟨53231421828448888639357159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70975229104598518185809545 53231421828448888639357159)
      ·
        refine ⟨79847132742673332959035739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53231421828448888639357159 79847132742673332959035739)
        ·
          refine ⟨119770699114009999438553609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79847132742673332959035739 119770699114009999438553609)
          ·
            refine ⟨89828024335507499578915207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119770699114009999438553609 89828024335507499578915207)
            ·
              refine ⟨134742036503261249368372811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89828024335507499578915207 134742036503261249368372811)
              ·
                refine ⟨202113054754891874052559217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134742036503261249368372811 202113054754891874052559217)
                ·
                  refine ⟨151584791066168905539419413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202113054754891874052559217 151584791066168905539419413)
                  ·
                    refine ⟨7105537081226667447160285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 151584791066168905539419413 7105537081226667447160285)
                    ·
                      refine ⟨2664576405460000292685107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7105537081226667447160285 2664576405460000292685107)
                      ·
                        rfl

theorem cell23_5189244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_5189244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189244 prefixEnd_5189244 := by exact prefixLift 5189244
  have htrace : WordTrace (prefixWord ++ tailWord_5189244) baseStart_5189244 baseEnd_5189244 := by
    simpa [prefixWord, tailWord_5189244, baseEnd_5189244] using wordTrace_append hprefix tailTrace_5189244
  have hstable : (prefixWord ++ tailWord_5189244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189244).length < 2 ^ (prefixWord ++ tailWord_5189244).sum := by decide
  have hdescent : baseEnd_5189244 < baseStart_5189244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189258 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_5189258 : Nat := 118140960795 + 5189258 * 2 ^ 59
def prefixEnd_5189258 : Nat := 4983230072969 + 3 ^ 40 * 5189258 * 2
def baseEnd_5189258 : Nat := 2664583594189163237910043

theorem tailTrace_5189258 : CollatzResearch.WordTrace tailWord_5189258 prefixEnd_5189258 2664583594189163237910043 := by
  unfold tailWord_5189258
  simp only [CollatzResearch.WordTrace]
  refine ⟨47316947058552998888292107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126178525489474663702112285 47316947058552998888292107)
  ·
    refine ⟨70975420587829498332438161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47316947058552998888292107 70975420587829498332438161)
    ·
      refine ⟨53231565440872123749328621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70975420587829498332438161 53231565440872123749328621)
      ·
        refine ⟨19961837040327046405998233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53231565440872123749328621 19961837040327046405998233)
        ·
          refine ⟨14971377780245284804498675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19961837040327046405998233 14971377780245284804498675)
          ·
            refine ⟨22457066670367927206748013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14971377780245284804498675 22457066670367927206748013)
            ·
              refine ⟨8421400001387972702530505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22457066670367927206748013 8421400001387972702530505)
              ·
                refine ⟨6316050001040979526897879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8421400001387972702530505 6316050001040979526897879)
                ·
                  refine ⟨9474075001561469290346819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6316050001040979526897879 9474075001561469290346819)
                  ·
                    refine ⟨14211112502342203935520229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9474075001561469290346819 14211112502342203935520229)
                    ·
                      refine ⟨2664583594189163237910043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14211112502342203935520229 2664583594189163237910043)
                      ·
                        rfl

theorem cell23_5189258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_5189258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189258 prefixEnd_5189258 := by exact prefixLift 5189258
  have htrace : WordTrace (prefixWord ++ tailWord_5189258) baseStart_5189258 baseEnd_5189258 := by
    simpa [prefixWord, tailWord_5189258, baseEnd_5189258] using wordTrace_append hprefix tailTrace_5189258
  have hstable : (prefixWord ++ tailWord_5189258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189258).length < 2 ^ (prefixWord ++ tailWord_5189258).sum := by decide
  have hdescent : baseEnd_5189258 < baseStart_5189258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189268 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5189268 : Nat := 118140960795 + 5189268 * 2 ^ 59
def prefixEnd_5189268 : Nat := 4983230072969 + 3 ^ 40 * 5189268 * 2
def baseEnd_5189268 : Nat := 888196242998569399594999

theorem tailTrace_5189268 : CollatzResearch.WordTrace tailWord_5189268 prefixEnd_5189268 888196242998569399594999 := by
  unfold tailWord_5189268
  simp only [CollatzResearch.WordTrace]
  refine ⟨94634076482087883630516229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126178768642783844840688305 94634076482087883630516229)
  ·
    refine ⟨17743889340391478180721793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94634076482087883630516229 17743889340391478180721793)
    ·
      refine ⟨13307917005293608635541345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17743889340391478180721793 13307917005293608635541345)
      ·
        refine ⟨9980937753970206476656009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13307917005293608635541345 9980937753970206476656009)
        ·
          refine ⟨7485703315477654857492007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9980937753970206476656009 7485703315477654857492007)
          ·
            refine ⟨11228554973216482286238011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7485703315477654857492007 11228554973216482286238011)
            ·
              refine ⟨16842832459824723429357017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11228554973216482286238011 16842832459824723429357017)
              ·
                refine ⟨12632124344868542572017763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16842832459824723429357017 12632124344868542572017763)
                ·
                  refine ⟨18948186517302813858026645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12632124344868542572017763 18948186517302813858026645)
                  ·
                    refine ⟨888196242998569399594999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18948186517302813858026645 888196242998569399594999)
                    ·
                      rfl

theorem cell23_5189268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5189268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189268 prefixEnd_5189268 := by exact prefixLift 5189268
  have htrace : WordTrace (prefixWord ++ tailWord_5189268) baseStart_5189268 baseEnd_5189268 := by
    simpa [prefixWord, tailWord_5189268, baseEnd_5189268] using wordTrace_append hprefix tailTrace_5189268
  have hstable : (prefixWord ++ tailWord_5189268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189268).length < 2 ^ (prefixWord ++ tailWord_5189268).sum := by decide
  have hdescent : baseEnd_5189268 < baseStart_5189268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189271 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_5189271 : Nat := 118140960795 + 5189271 * 2 ^ 59
def prefixEnd_5189271 : Nat := 4983230072969 + 3 ^ 40 * 5189271 * 2
def baseEnd_5189271 : Nat := 2664590269437671687047483

theorem tailTrace_5189271 : CollatzResearch.WordTrace tailWord_5189271 prefixEnd_5189271 2664590269437671687047483 := by
  unfold tailWord_5189271
  simp only [CollatzResearch.WordTrace]
  refine ⟨189268262383164898773391667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126178841588776599182261111 189268262383164898773391667)
  ·
    refine ⟨283902393574747348160087501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189268262383164898773391667 283902393574747348160087501)
    ·
      refine ⟨106463397590530255560032813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283902393574747348160087501 106463397590530255560032813)
      ·
        refine ⟨39923774096448845835012305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106463397590530255560032813 39923774096448845835012305)
        ·
          refine ⟨29942830572336634376259229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39923774096448845835012305 29942830572336634376259229)
          ·
            refine ⟨11228561464626237891097211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29942830572336634376259229 11228561464626237891097211)
            ·
              refine ⟨16842842196939356836645817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11228561464626237891097211 16842842196939356836645817)
              ·
                refine ⟨12632131647704517627484363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16842842196939356836645817 12632131647704517627484363)
                ·
                  refine ⟨18948197471556776441226545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12632131647704517627484363 18948197471556776441226545)
                  ·
                    refine ⟨14211148103667582330919909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18948197471556776441226545 14211148103667582330919909)
                    ·
                      refine ⟨2664590269437671687047483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14211148103667582330919909 2664590269437671687047483)
                      ·
                        rfl

theorem cell23_5189271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_5189271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189271 prefixEnd_5189271 := by exact prefixLift 5189271
  have htrace : WordTrace (prefixWord ++ tailWord_5189271) baseStart_5189271 baseEnd_5189271 := by
    simpa [prefixWord, tailWord_5189271, baseEnd_5189271] using wordTrace_append hprefix tailTrace_5189271
  have hstable : (prefixWord ++ tailWord_5189271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189271).length < 2 ^ (prefixWord ++ tailWord_5189271).sum := by decide
  have hdescent : baseEnd_5189271 < baseStart_5189271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189278 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_5189278 : Nat := 118140960795 + 5189278 * 2 ^ 59
def prefixEnd_5189278 : Nat := 4983230072969 + 3 ^ 40 * 5189278 * 2
def baseEnd_5189278 : Nat := 2664593863802253159659951

theorem tailTrace_5189278 : CollatzResearch.WordTrace tailWord_5189278 prefixEnd_5189278 2664593863802253159659951 := by
  unfold tailWord_5189278
  simp only [CollatzResearch.WordTrace]
  refine ⟨23658564711767442371112061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126179011796093025979264325 23658564711767442371112061)
  ·
    refine ⟨8871961766912790889167023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23658564711767442371112061 8871961766912790889167023)
    ·
      refine ⟨13307942650369186333750535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8871961766912790889167023 13307942650369186333750535)
      ·
        refine ⟨19961913975553779500625803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13307942650369186333750535 19961913975553779500625803)
        ·
          refine ⟨29942870963330669250938705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19961913975553779500625803 29942870963330669250938705)
          ·
            refine ⟨22457153222498001938204029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29942870963330669250938705 22457153222498001938204029)
            ·
              refine ⟨8421432458436750726826511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22457153222498001938204029 8421432458436750726826511)
              ·
                refine ⟨12632148687655126090239767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421432458436750726826511 12632148687655126090239767)
                ·
                  refine ⟨18948223031482689135359651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12632148687655126090239767 18948223031482689135359651)
                  ·
                    refine ⟨28422334547224033703039477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18948223031482689135359651 28422334547224033703039477)
                    ·
                      refine ⟨2664593863802253159659951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28422334547224033703039477 2664593863802253159659951)
                      ·
                        rfl

theorem cell23_5189278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_5189278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189278 prefixEnd_5189278 := by exact prefixLift 5189278
  have htrace : WordTrace (prefixWord ++ tailWord_5189278) baseStart_5189278 baseEnd_5189278 := by
    simpa [prefixWord, tailWord_5189278, baseEnd_5189278] using wordTrace_append hprefix tailTrace_5189278
  have hstable : (prefixWord ++ tailWord_5189278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189278).length < 2 ^ (prefixWord ++ tailWord_5189278).sum := by decide
  have hdescent : baseEnd_5189278 < baseStart_5189278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189308 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_5189308 : Nat := 118140960795 + 5189308 * 2 ^ 59
def prefixEnd_5189308 : Nat := 4983230072969 + 3 ^ 40 * 5189308 * 2
def baseEnd_5189308 : Nat := 2664609268221888042284813

theorem tailTrace_5189308 : CollatzResearch.WordTrace tailWord_5189308 prefixEnd_5189308 2664609268221888042284813 := by
  unfold tailWord_5189308
  simp only [CollatzResearch.WordTrace]
  refine ⟨94634805942015427046244289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126179741256020569394992385 94634805942015427046244289)
  ·
    refine ⟨70976104456511570284683217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94634805942015427046244289 70976104456511570284683217)
    ·
      refine ⟨53232078342383677713512413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70976104456511570284683217 53232078342383677713512413)
      ·
        refine ⟨19962029378393879142567155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53232078342383677713512413 19962029378393879142567155)
        ·
          refine ⟨29943044067590818713850733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19962029378393879142567155 29943044067590818713850733)
          ·
            refine ⟨11228641525346557017694025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29943044067590818713850733 11228641525346557017694025)
            ·
              refine ⟨8421481144009917763270519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11228641525346557017694025 8421481144009917763270519)
              ·
                refine ⟨12632221716014876644905779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421481144009917763270519 12632221716014876644905779)
                ·
                  refine ⟨18948332574022314967358669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12632221716014876644905779 18948332574022314967358669)
                  ·
                    refine ⟨7105624715258368112759501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18948332574022314967358669 7105624715258368112759501)
                    ·
                      refine ⟨2664609268221888042284813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7105624715258368112759501 2664609268221888042284813)
                      ·
                        rfl

theorem cell23_5189308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_5189308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189308 prefixEnd_5189308 := by exact prefixLift 5189308
  have htrace : WordTrace (prefixWord ++ tailWord_5189308) baseStart_5189308 baseEnd_5189308 := by
    simpa [prefixWord, tailWord_5189308, baseEnd_5189308] using wordTrace_append hprefix tailTrace_5189308
  have hstable : (prefixWord ++ tailWord_5189308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189308).length < 2 ^ (prefixWord ++ tailWord_5189308).sum := by decide
  have hdescent : baseEnd_5189308 < baseStart_5189308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189325 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_5189325 : Nat := 118140960795 + 5189325 * 2 ^ 59
def prefixEnd_5189325 : Nat := 4983230072969 + 3 ^ 40 * 5189325 * 2
def baseEnd_5189325 : Nat := 2664617997393014475772235

theorem tailTrace_5189325 : CollatzResearch.WordTrace tailWord_5189325 prefixEnd_5189325 2664617997393014475772235 := by
  unfold tailWord_5189325
  simp only [CollatzResearch.WordTrace]
  refine ⟨189270231924969265995857429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126180154616646177330571619 189270231924969265995857429)
  ·
    refine ⟨8872042121482934343555817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 189270231924969265995857429 8872042121482934343555817)
    ·
      refine ⟨6654031591112200757666863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8872042121482934343555817 6654031591112200757666863)
      ·
        refine ⟨9981047386668301136500295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6654031591112200757666863 9981047386668301136500295)
        ·
          refine ⟨14971571080002451704750443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9981047386668301136500295 14971571080002451704750443)
          ·
            refine ⟨22457356620003677557125665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14971571080002451704750443 22457356620003677557125665)
            ·
              refine ⟨16843017465002758167844249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22457356620003677557125665 16843017465002758167844249)
              ·
                refine ⟨12632263098752068625883187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16843017465002758167844249 12632263098752068625883187)
                ·
                  refine ⟨18948394648128102938824781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12632263098752068625883187 18948394648128102938824781)
                  ·
                    refine ⟨7105647993048038602059293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18948394648128102938824781 7105647993048038602059293)
                    ·
                      refine ⟨2664617997393014475772235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7105647993048038602059293 2664617997393014475772235)
                      ·
                        rfl

theorem cell23_5189325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_5189325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189325 prefixEnd_5189325 := by exact prefixLift 5189325
  have htrace : WordTrace (prefixWord ++ tailWord_5189325) baseStart_5189325 baseEnd_5189325 := by
    simpa [prefixWord, tailWord_5189325, baseEnd_5189325] using wordTrace_append hprefix tailTrace_5189325
  have hstable : (prefixWord ++ tailWord_5189325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189325).length < 2 ^ (prefixWord ++ tailWord_5189325).sum := by decide
  have hdescent : baseEnd_5189325 < baseStart_5189325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189331 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 7, 4, 2]
def baseStart_5189331 : Nat := 118140960795 + 5189331 * 2 ^ 59
def prefixEnd_5189331 : Nat := 4983230072969 + 3 ^ 40 * 5189331 * 2
def baseEnd_5189331 : Nat := 2664621078276941452297207

theorem tailTrace_5189331 : CollatzResearch.WordTrace tailWord_5189331 prefixEnd_5189331 2664621078276941452297207 := by
  unfold tailWord_5189331
  simp only [CollatzResearch.WordTrace]
  refine ⟨189270450762947529020575847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126180300508631686013717231 189270450762947529020575847)
  ·
    refine ⟨283905676144421293530863771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189270450762947529020575847 283905676144421293530863771)
    ·
      refine ⟨425858514216631940296295657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283905676144421293530863771 425858514216631940296295657)
      ·
        refine ⟨319393885662473955222221743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425858514216631940296295657 319393885662473955222221743)
        ·
          refine ⟨479090828493710932833332615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319393885662473955222221743 479090828493710932833332615)
          ·
            refine ⟨718636242740566399249998923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479090828493710932833332615 718636242740566399249998923)
            ·
              refine ⟨1077954364110849598874998385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718636242740566399249998923 1077954364110849598874998385)
              ·
                refine ⟨808465773083137199156248789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077954364110849598874998385 808465773083137199156248789)
                ·
                  refine ⟨18948416556636028105224581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 808465773083137199156248789 18948416556636028105224581)
                  ·
                    refine ⟨3552828104369255269729609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18948416556636028105224581 3552828104369255269729609)
                    ·
                      refine ⟨2664621078276941452297207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552828104369255269729609 2664621078276941452297207)
                      ·
                        rfl

theorem cell23_5189331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 4, 2].length) (baseStart_5189331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189331 prefixEnd_5189331 := by exact prefixLift 5189331
  have htrace : WordTrace (prefixWord ++ tailWord_5189331) baseStart_5189331 baseEnd_5189331 := by
    simpa [prefixWord, tailWord_5189331, baseEnd_5189331] using wordTrace_append hprefix tailTrace_5189331
  have hstable : (prefixWord ++ tailWord_5189331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189331).length < 2 ^ (prefixWord ++ tailWord_5189331).sum := by decide
  have hdescent : baseEnd_5189331 < baseStart_5189331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189361 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_5189361 : Nat := 118140960795 + 5189361 * 2 ^ 59
def prefixEnd_5189361 : Nat := 4983230072969 + 3 ^ 40 * 5189361 * 2
def baseEnd_5189361 : Nat := 2664636482696576334922069

theorem tailTrace_5189361 : CollatzResearch.WordTrace tailWord_5189361 prefixEnd_5189361 2664636482696576334922069 := by
  unfold tailWord_5189361
  simp only [CollatzResearch.WordTrace]
  refine ⟨189271544952838844144167937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126181029968559229429445291 189271544952838844144167937)
  ·
    refine ⟨141953658714629133108125953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189271544952838844144167937 141953658714629133108125953)
    ·
      refine ⟨106465244035971849831094465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141953658714629133108125953 106465244035971849831094465)
      ·
        refine ⟨79848933026978887373320849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106465244035971849831094465 79848933026978887373320849)
        ·
          refine ⟨59886699770234165529990637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79848933026978887373320849 59886699770234165529990637)
          ·
            refine ⟨22457512413837812073746489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59886699770234165529990637 22457512413837812073746489)
            ·
              refine ⟨16843134310378359055309867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22457512413837812073746489 16843134310378359055309867)
              ·
                refine ⟨25264701465567538582964801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16843134310378359055309867 25264701465567538582964801)
                ·
                  refine ⟨18948526099175653937223601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25264701465567538582964801 18948526099175653937223601)
                  ·
                    refine ⟨14211394574381740452917701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18948526099175653937223601 14211394574381740452917701)
                    ·
                      refine ⟨2664636482696576334922069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14211394574381740452917701 2664636482696576334922069)
                      ·
                        rfl

theorem cell23_5189361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_5189361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189361 prefixEnd_5189361 := by exact prefixLift 5189361
  have htrace : WordTrace (prefixWord ++ tailWord_5189361) baseStart_5189361 baseEnd_5189361 := by
    simpa [prefixWord, tailWord_5189361, baseEnd_5189361] using wordTrace_append hprefix tailTrace_5189361
  have hstable : (prefixWord ++ tailWord_5189361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189361).length < 2 ^ (prefixWord ++ tailWord_5189361).sum := by decide
  have hdescent : baseEnd_5189361 < baseStart_5189361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189388 : List Nat := [2, 2, 1, 2, 2, 1, 5, 3, 5]
def baseStart_5189388 : Nat := 118140960795 + 5189388 * 2 ^ 59
def prefixEnd_5189388 : Nat := 4983230072969 + 3 ^ 40 * 5189388 * 2
def baseEnd_5189388 : Nat := 296072260741583081031605

theorem tailTrace_5189388 : CollatzResearch.WordTrace tailWord_5189388 prefixEnd_5189388 296072260741583081031605 := by
  unfold tailWord_5189388
  simp only [CollatzResearch.WordTrace]
  refine ⟨94636264861870513877700409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126181686482494018503600545 94636264861870513877700409)
  ·
    refine ⟨70977198646402885408275307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94636264861870513877700409 70977198646402885408275307)
    ·
      refine ⟨106465797969604328112412961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70977198646402885408275307 106465797969604328112412961)
      ·
        refine ⟨79849348477203246084309721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106465797969604328112412961 79849348477203246084309721)
        ·
          refine ⟨59887011357902434563232291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79849348477203246084309721 59887011357902434563232291)
          ·
            refine ⟨89830517036853651844848437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59887011357902434563232291 89830517036853651844848437)
            ·
              refine ⟨8421610972205029860454541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89830517036853651844848437 8421610972205029860454541)
              ·
                refine ⟨3158104114576886197670453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8421610972205029860454541 3158104114576886197670453)
                ·
                  refine ⟨296072260741583081031605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3158104114576886197670453 296072260741583081031605)
                  ·
                    rfl

theorem cell23_5189388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_5189388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189388 prefixEnd_5189388 := by exact prefixLift 5189388
  have htrace : WordTrace (prefixWord ++ tailWord_5189388) baseStart_5189388 baseEnd_5189388 := by
    simpa [prefixWord, tailWord_5189388, baseEnd_5189388] using wordTrace_append hprefix tailTrace_5189388
  have hstable : (prefixWord ++ tailWord_5189388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189388).length < 2 ^ (prefixWord ++ tailWord_5189388).sum := by decide
  have hdescent : baseEnd_5189388 < baseStart_5189388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189408 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 2, 5, 2]
def baseStart_5189408 : Nat := 118140960795 + 5189408 * 2 ^ 59
def prefixEnd_5189408 : Nat := 4983230072969 + 3 ^ 40 * 5189408 * 2
def baseEnd_5189408 : Nat := 2664660616287337651034353

theorem tailTrace_5189408 : CollatzResearch.WordTrace tailWord_5189408 prefixEnd_5189408 2664660616287337651034353 := by
  unfold tailWord_5189408
  simp only [CollatzResearch.WordTrace]
  refine ⟨94636629591834285585564439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126182172789112380780752585 94636629591834285585564439)
  ·
    refine ⟨141954944387751428378346659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94636629591834285585564439 141954944387751428378346659)
    ·
      refine ⟨212932416581627142567519989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141954944387751428378346659 212932416581627142567519989)
      ·
        refine ⟨19962414054527544615704999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 212932416581627142567519989 19962414054527544615704999)
        ·
          refine ⟨29943621081791316923557499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19962414054527544615704999 29943621081791316923557499)
          ·
            refine ⟨44915431622686975385336249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29943621081791316923557499 44915431622686975385336249)
            ·
              refine ⟨33686573717015231539002187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44915431622686975385336249 33686573717015231539002187)
              ·
                refine ⟨50529860575522847308503281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33686573717015231539002187 50529860575522847308503281)
                ·
                  refine ⟨37897395431642135481377461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50529860575522847308503281 37897395431642135481377461)
                  ·
                    refine ⟨3552880821716450201379137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37897395431642135481377461 3552880821716450201379137)
                    ·
                      refine ⟨2664660616287337651034353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552880821716450201379137 2664660616287337651034353)
                      ·
                        rfl

theorem cell23_5189408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_5189408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189408 prefixEnd_5189408 := by exact prefixLift 5189408
  have htrace : WordTrace (prefixWord ++ tailWord_5189408) baseStart_5189408 baseEnd_5189408 := by
    simpa [prefixWord, tailWord_5189408, baseEnd_5189408] using wordTrace_append hprefix tailTrace_5189408
  have hstable : (prefixWord ++ tailWord_5189408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189408).length < 2 ^ (prefixWord ++ tailWord_5189408).sum := by decide
  have hdescent : baseEnd_5189408 < baseStart_5189408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189465 : List Nat := [1, 2, 1, 2, 2, 3, 3, 4, 1, 4]
def baseStart_5189465 : Nat := 118140960795 + 5189465 * 2 ^ 59
def prefixEnd_5189465 : Nat := 4983230072969 + 3 ^ 40 * 5189465 * 2
def baseEnd_5189465 : Nat := 888229961561547976007197

theorem tailTrace_5189465 : CollatzResearch.WordTrace tailWord_5189465 prefixEnd_5189465 888229961561547976007197 := by
  unfold tailWord_5189465
  simp only [CollatzResearch.WordTrace]
  refine ⟨189275338144462069905953849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126183558762974713270635899 189275338144462069905953849)
  ·
    refine ⟨141956503608346552429465387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189275338144462069905953849 141956503608346552429465387)
    ·
      refine ⟨212934755412519828644198081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141956503608346552429465387 212934755412519828644198081)
      ·
        refine ⟨159701066559389871483148561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212934755412519828644198081 159701066559389871483148561)
        ·
          refine ⟨119775799919542403612361421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159701066559389871483148561 119775799919542403612361421)
          ·
            refine ⟨44915924969828401354635533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119775799919542403612361421 44915924969828401354635533)
            ·
              refine ⟨16843471863685650507988325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44915924969828401354635533 16843471863685650507988325)
              ·
                refine ⟨3158150974441059470247811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16843471863685650507988325 3158150974441059470247811)
                ·
                  refine ⟨4737226461661589205371717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158150974441059470247811 4737226461661589205371717)
                  ·
                    refine ⟨888229961561547976007197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4737226461661589205371717 888229961561547976007197)
                    ·
                      rfl

theorem cell23_5189465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 4].length) (baseStart_5189465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189465 prefixEnd_5189465 := by exact prefixLift 5189465
  have htrace : WordTrace (prefixWord ++ tailWord_5189465) baseStart_5189465 baseEnd_5189465 := by
    simpa [prefixWord, tailWord_5189465, baseEnd_5189465] using wordTrace_append hprefix tailTrace_5189465
  have hstable : (prefixWord ++ tailWord_5189465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189465).length < 2 ^ (prefixWord ++ tailWord_5189465).sum := by decide
  have hdescent : baseEnd_5189465 < baseStart_5189465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189482 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_5189482 : Nat := 118140960795 + 5189482 * 2 ^ 59
def prefixEnd_5189482 : Nat := 4983230072969 + 3 ^ 40 * 5189482 * 2
def baseEnd_5189482 : Nat := 888232871285256787169671

theorem tailTrace_5189482 : CollatzResearch.WordTrace tailWord_5189482 prefixEnd_5189482 888232871285256787169671 := by
  unfold tailWord_5189482
  simp only [CollatzResearch.WordTrace]
  refine ⟨47318989546350120452330675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126183972123600321206215133 47318989546350120452330675)
  ·
    refine ⟨70978484319525180678496013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47318989546350120452330675 70978484319525180678496013)
    ·
      refine ⟨26616931619821942754436005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70978484319525180678496013 26616931619821942754436005)
      ·
        refine ⟨4990674678716614266456751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26616931619821942754436005 4990674678716614266456751)
        ·
          refine ⟨7486012018074921399685127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4990674678716614266456751 7486012018074921399685127)
          ·
            refine ⟨11229018027112382099527691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7486012018074921399685127 11229018027112382099527691)
            ·
              refine ⟨16843527040668573149291537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11229018027112382099527691 16843527040668573149291537)
              ·
                refine ⟨12632645280501429861968653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16843527040668573149291537 12632645280501429861968653)
                ·
                  refine ⟨4737241980188036198238245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12632645280501429861968653 4737241980188036198238245)
                  ·
                    refine ⟨888232871285256787169671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4737241980188036198238245 888232871285256787169671)
                    ·
                      rfl

theorem cell23_5189482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_5189482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189482 prefixEnd_5189482 := by exact prefixLift 5189482
  have htrace : WordTrace (prefixWord ++ tailWord_5189482) baseStart_5189482 baseEnd_5189482 := by
    simpa [prefixWord, tailWord_5189482, baseEnd_5189482] using wordTrace_append hprefix tailTrace_5189482
  have hstable : (prefixWord ++ tailWord_5189482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189482).length < 2 ^ (prefixWord ++ tailWord_5189482).sum := by decide
  have hdescent : baseEnd_5189482 < baseStart_5189482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189501 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_5189501 : Nat := 118140960795 + 5189501 * 2 ^ 59
def prefixEnd_5189501 : Nat := 4983230072969 + 3 ^ 40 * 5189501 * 2
def baseEnd_5189501 : Nat := 2664708369988205787171425

theorem tailTrace_5189501 : CollatzResearch.WordTrace tailWord_5189501 prefixEnd_5189501 2664708369988205787171425 := by
  unfold tailWord_5189501
  simp only [CollatzResearch.WordTrace]
  refine ⟨189276651172331648054264357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126184434114887765369509571 189276651172331648054264357)
  ·
    refine ⟨35489372094812184010174567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189276651172331648054264357 35489372094812184010174567)
    ·
      refine ⟨53234058142218276015261851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35489372094812184010174567 53234058142218276015261851)
      ·
        refine ⟨79851087213327414022892777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53234058142218276015261851 79851087213327414022892777)
        ·
          refine ⟨59888315409995560517169583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79851087213327414022892777 59888315409995560517169583)
          ·
            refine ⟨89832473114993340775754375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59888315409995560517169583 89832473114993340775754375)
            ·
              refine ⟨134748709672490011163631563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89832473114993340775754375 134748709672490011163631563)
              ·
                refine ⟨202123064508735016745447345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134748709672490011163631563 202123064508735016745447345)
                ·
                  refine ⟨151592298381551262559085509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202123064508735016745447345 151592298381551262559085509)
                  ·
                    refine ⟨28423555946540861729828533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151592298381551262559085509 28423555946540861729828533)
                    ·
                      refine ⟨2664708369988205787171425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28423555946540861729828533 2664708369988205787171425)
                      ·
                        rfl

theorem cell23_5189501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_5189501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189501 prefixEnd_5189501 := by exact prefixLift 5189501
  have htrace : WordTrace (prefixWord ++ tailWord_5189501) baseStart_5189501 baseEnd_5189501 := by
    simpa [prefixWord, tailWord_5189501, baseEnd_5189501] using wordTrace_append hprefix tailTrace_5189501
  have hstable : (prefixWord ++ tailWord_5189501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189501).length < 2 ^ (prefixWord ++ tailWord_5189501).sum := by decide
  have hdescent : baseEnd_5189501 < baseStart_5189501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189512 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 6]
def baseStart_5189512 : Nat := 118140960795 + 5189512 * 2 ^ 59
def prefixEnd_5189512 : Nat := 4983230072969 + 3 ^ 40 * 5189512 * 2
def baseEnd_5189512 : Nat := 296079335363933916014875

theorem tailTrace_5189512 : CollatzResearch.WordTrace tailWord_5189512 prefixEnd_5189512 296079335363933916014875 := by
  unfold tailWord_5189512
  simp only [CollatzResearch.WordTrace]
  refine ⟨94638526187645898466457395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126184701583527864621943193 94638526187645898466457395)
  ·
    refine ⟨141957789281468847699686093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94638526187645898466457395 141957789281468847699686093)
    ·
      refine ⟨53234170980550817887382285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141957789281468847699686093 53234170980550817887382285)
      ·
        refine ⟨19962814117706556707768357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53234170980550817887382285 19962814117706556707768357)
        ·
          refine ⟨3743027647069979382706567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19962814117706556707768357 3743027647069979382706567)
          ·
            refine ⟨5614541470604969074059851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3743027647069979382706567 5614541470604969074059851)
            ·
              refine ⟨8421812205907453611089777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5614541470604969074059851 8421812205907453611089777)
              ·
                refine ⟨6316359154430590208317333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8421812205907453611089777 6316359154430590208317333)
                ·
                  refine ⟨296079335363933916014875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6316359154430590208317333 296079335363933916014875)
                  ·
                    rfl

theorem cell23_5189512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 6].length) (baseStart_5189512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189512 prefixEnd_5189512 := by exact prefixLift 5189512
  have htrace : WordTrace (prefixWord ++ tailWord_5189512) baseStart_5189512 baseEnd_5189512 := by
    simpa [prefixWord, tailWord_5189512, baseEnd_5189512] using wordTrace_append hprefix tailTrace_5189512
  have hstable : (prefixWord ++ tailWord_5189512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189512).length < 2 ^ (prefixWord ++ tailWord_5189512).sum := by decide
  have hdescent : baseEnd_5189512 < baseStart_5189512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189521 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 3, 6]
def baseStart_5189521 : Nat := 118140960795 + 5189521 * 2 ^ 59
def prefixEnd_5189521 : Nat := 4983230072969 + 3 ^ 40 * 5189521 * 2
def baseEnd_5189521 : Nat := 888239546533765236307111

theorem tailTrace_5189521 : CollatzResearch.WordTrace tailWord_5189521 prefixEnd_5189521 888239546533765236307111 := by
  unfold tailWord_5189521
  simp only [CollatzResearch.WordTrace]
  refine ⟨189277380632259191469992417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126184920421506127646661611 189277380632259191469992417)
  ·
    refine ⟨141958035474194393602494313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189277380632259191469992417 141958035474194393602494313)
    ·
      refine ⟨106468526605645795201870735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141958035474194393602494313 106468526605645795201870735)
      ·
        refine ⟨159702789908468692802806103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106468526605645795201870735 159702789908468692802806103)
        ·
          refine ⟨239554184862703039204209155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159702789908468692802806103 239554184862703039204209155)
          ·
            refine ⟨359331277294054558806313733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239554184862703039204209155 359331277294054558806313733)
            ·
              refine ⟨67374614492635229776183825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 359331277294054558806313733 67374614492635229776183825)
              ·
                refine ⟨50530960869476422332137869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67374614492635229776183825 50530960869476422332137869)
                ·
                  refine ⟨18949110326053658374551701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50530960869476422332137869 18949110326053658374551701)
                  ·
                    refine ⟨888239546533765236307111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18949110326053658374551701 888239546533765236307111)
                    ·
                      rfl

theorem cell23_5189521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_5189521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189521 prefixEnd_5189521 := by exact prefixLift 5189521
  have htrace : WordTrace (prefixWord ++ tailWord_5189521) baseStart_5189521 baseEnd_5189521 := by
    simpa [prefixWord, tailWord_5189521, baseEnd_5189521] using wordTrace_append hprefix tailTrace_5189521
  have hstable : (prefixWord ++ tailWord_5189521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189521).length < 2 ^ (prefixWord ++ tailWord_5189521).sum := by decide
  have hdescent : baseEnd_5189521 < baseStart_5189521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189522 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5189522 : Nat := 118140960795 + 5189522 * 2 ^ 59
def prefixEnd_5189522 : Nat := 4983230072969 + 3 ^ 40 * 5189522 * 2
def baseEnd_5189522 : Nat := 2664719153081950205008829

theorem tailTrace_5189522 : CollatzResearch.WordTrace tailWord_5189522 prefixEnd_5189522 2664719153081950205008829 := by
  unfold tailWord_5189522
  simp only [CollatzResearch.WordTrace]
  refine ⟨47319354276313892160194705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126184944736837045760519213 47319354276313892160194705)
  ·
    refine ⟨35489515707235419120146029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47319354276313892160194705 35489515707235419120146029)
    ·
      refine ⟨13308568390213282170054761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35489515707235419120146029 13308568390213282170054761)
      ·
        refine ⟨9981426292659961627541071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13308568390213282170054761 9981426292659961627541071)
        ·
          refine ⟨14972139438989942441311607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9981426292659961627541071 14972139438989942441311607)
          ·
            refine ⟨22458209158484913661967411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14972139438989942441311607 22458209158484913661967411)
            ·
              refine ⟨33687313737727370492951117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22458209158484913661967411 33687313737727370492951117)
              ·
                refine ⟨12632742651647763934856669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33687313737727370492951117 12632742651647763934856669)
                ·
                  refine ⟨4737278494367911475571251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12632742651647763934856669 4737278494367911475571251)
                  ·
                    refine ⟨7105917741551867213356877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4737278494367911475571251 7105917741551867213356877)
                    ·
                      refine ⟨2664719153081950205008829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7105917741551867213356877 2664719153081950205008829)
                      ·
                        rfl

theorem cell23_5189522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5189522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189522 prefixEnd_5189522 := by exact prefixLift 5189522
  have htrace : WordTrace (prefixWord ++ tailWord_5189522) baseStart_5189522 baseEnd_5189522 := by
    simpa [prefixWord, tailWord_5189522, baseEnd_5189522] using wordTrace_append hprefix tailTrace_5189522
  have hstable : (prefixWord ++ tailWord_5189522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189522).length < 2 ^ (prefixWord ++ tailWord_5189522).sum := by decide
  have hdescent : baseEnd_5189522 < baseStart_5189522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189545 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 5, 2, 2]
def baseStart_5189545 : Nat := 118140960795 + 5189545 * 2 ^ 59
def prefixEnd_5189545 : Nat := 4983230072969 + 3 ^ 40 * 5189545 * 2
def baseEnd_5189545 : Nat := 2664730963137003615021223

theorem tailTrace_5189545 : CollatzResearch.WordTrace tailWord_5189545 prefixEnd_5189545 2664730963137003615021223 := by
  unfold tailWord_5189545
  simp only [CollatzResearch.WordTrace]
  refine ⟨189278255984172243568866089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126185503989448162379244059 189278255984172243568866089)
  ·
    refine ⟨141958691988129182676649567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189278255984172243568866089 141958691988129182676649567)
    ·
      refine ⟨212938037982193774014974351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141958691988129182676649567 212938037982193774014974351)
      ·
        refine ⟨319407056973290661022461527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212938037982193774014974351 319407056973290661022461527)
        ·
          refine ⟨479110585459935991533692291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319407056973290661022461527 479110585459935991533692291)
          ·
            refine ⟨718665878189903987300538437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479110585459935991533692291 718665878189903987300538437)
            ·
              refine ⟨134749852160606997618850957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 718665878189903987300538437 134749852160606997618850957)
              ·
                refine ⟨50531194560227624107069109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134749852160606997618850957 50531194560227624107069109)
                ·
                  refine ⟨4737299490021339760037729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50531194560227624107069109 4737299490021339760037729)
                  ·
                    refine ⟨3552974617516004820028297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4737299490021339760037729 3552974617516004820028297)
                    ·
                      refine ⟨2664730963137003615021223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3552974617516004820028297 2664730963137003615021223)
                      ·
                        rfl

theorem cell23_5189545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 2, 2].length) (baseStart_5189545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189545 prefixEnd_5189545 := by exact prefixLift 5189545
  have htrace : WordTrace (prefixWord ++ tailWord_5189545) baseStart_5189545 baseEnd_5189545 := by
    simpa [prefixWord, tailWord_5189545, baseEnd_5189545] using wordTrace_append hprefix tailTrace_5189545
  have hstable : (prefixWord ++ tailWord_5189545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189545).length < 2 ^ (prefixWord ++ tailWord_5189545).sum := by decide
  have hdescent : baseEnd_5189545 < baseStart_5189545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189550 : List Nat := [4, 1, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5189550 : Nat := 118140960795 + 5189550 * 2 ^ 59
def prefixEnd_5189550 : Nat := 4983230072969 + 3 ^ 40 * 5189550 * 2
def baseEnd_5189550 : Nat := 888244510180092031819567

theorem tailTrace_5189550 : CollatzResearch.WordTrace tailWord_5189550 prefixEnd_5189550 888244510180092031819567 := by
  unfold tailWord_5189550
  simp only [CollatzResearch.WordTrace]
  refine ⟨23659804793644266177849763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126185625566102752948532069 23659804793644266177849763)
  ·
    refine ⟨35489707190466399266774645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23659804793644266177849763 35489707190466399266774645)
    ·
      refine ⟨3327160049106224931260123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35489707190466399266774645 3327160049106224931260123)
      ·
        refine ⟨4990740073659337396890185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3327160049106224931260123 4990740073659337396890185)
        ·
          refine ⟨3743055055244503047667639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4990740073659337396890185 3743055055244503047667639)
          ·
            refine ⟨5614582582866754571501459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3743055055244503047667639 5614582582866754571501459)
            ·
              refine ⟨8421873874300131857252189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5614582582866754571501459 8421873874300131857252189)
              ·
                refine ⟨3158202702862549446469571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8421873874300131857252189 3158202702862549446469571)
                ·
                  refine ⟨4737304054293824169704357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158202702862549446469571 4737304054293824169704357)
                  ·
                    refine ⟨888244510180092031819567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4737304054293824169704357 888244510180092031819567)
                    ·
                      rfl

theorem cell23_5189550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5189550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189550 prefixEnd_5189550 := by exact prefixLift 5189550
  have htrace : WordTrace (prefixWord ++ tailWord_5189550) baseStart_5189550 baseEnd_5189550 := by
    simpa [prefixWord, tailWord_5189550, baseEnd_5189550] using wordTrace_append hprefix tailTrace_5189550
  have hstable : (prefixWord ++ tailWord_5189550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189550).length < 2 ^ (prefixWord ++ tailWord_5189550).sum := by decide
  have hdescent : baseEnd_5189550 < baseStart_5189550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189551 : List Nat := [1, 1, 2, 1, 2, 2, 5, 9]
def baseStart_5189551 : Nat := 118140960795 + 5189551 * 2 ^ 59
def prefixEnd_5189551 : Nat := 4983230072969 + 3 ^ 40 * 5189551 * 2
def baseEnd_5189551 : Nat := 98693853482256688575785

theorem tailTrace_5189551 : CollatzResearch.WordTrace tailWord_5189551 prefixEnd_5189551 98693853482256688575785 := by
  unfold tailWord_5189551
  simp only [CollatzResearch.WordTrace]
  refine ⟨189278474822150506593584507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126185649881433671062389671 189278474822150506593584507)
  ·
    refine ⟨283917712233225759890376761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189278474822150506593584507 283917712233225759890376761)
    ·
      refine ⟨212938284174919319917782571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283917712233225759890376761 212938284174919319917782571)
      ·
        refine ⟨319407426262378979876673857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212938284174919319917782571 319407426262378979876673857)
        ·
          refine ⟨239555569696784234907505393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319407426262378979876673857 239555569696784234907505393)
          ·
            refine ⟨179666677272588176180629045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239555569696784234907505393 179666677272588176180629045)
            ·
              refine ⟨16843750994305141516933973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 179666677272588176180629045 16843750994305141516933973)
              ·
                refine ⟨98693853482256688575785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16843750994305141516933973 98693853482256688575785)
                ·
                  rfl

theorem cell23_5189551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 9].length) (baseStart_5189551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189551 prefixEnd_5189551 := by exact prefixLift 5189551
  have htrace : WordTrace (prefixWord ++ tailWord_5189551) baseStart_5189551 baseEnd_5189551 := by
    simpa [prefixWord, tailWord_5189551, baseEnd_5189551] using wordTrace_append hprefix tailTrace_5189551
  have hstable : (prefixWord ++ tailWord_5189551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189551).length < 2 ^ (prefixWord ++ tailWord_5189551).sum := by decide
  have hdescent : baseEnd_5189551 < baseStart_5189551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189565 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_5189565 : Nat := 118140960795 + 5189565 * 2 ^ 59
def prefixEnd_5189565 : Nat := 4983230072969 + 3 ^ 40 * 5189565 * 2
def baseEnd_5189565 : Nat := 2664741232750093536771131

theorem tailTrace_5189565 : CollatzResearch.WordTrace tailWord_5189565 prefixEnd_5189565 2664741232750093536771131 := by
  unfold tailWord_5189565
  simp only [CollatzResearch.WordTrace]
  refine ⟨189278985444099786984594149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126185990296066524656396099 189278985444099786984594149)
  ·
    refine ⟨35489809770768710059611403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189278985444099786984594149 35489809770768710059611403)
    ·
      refine ⟨53234714656153065089417105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35489809770768710059611403 53234714656153065089417105)
      ·
        refine ⟨39926035992114798817062829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53234714656153065089417105 39926035992114798817062829)
        ·
          refine ⟨14972263497043049556398561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39926035992114798817062829 14972263497043049556398561)
          ·
            refine ⟨11229197622782287167298921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14972263497043049556398561 11229197622782287167298921)
            ·
              refine ⟨8421898217086715375474191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11229197622782287167298921 8421898217086715375474191)
              ·
                refine ⟨12632847325630073063211287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421898217086715375474191 12632847325630073063211287)
                ·
                  refine ⟨18949270988445109594816931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12632847325630073063211287 18949270988445109594816931)
                  ·
                    refine ⟨28423906482667664392225397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18949270988445109594816931 28423906482667664392225397)
                    ·
                      refine ⟨2664741232750093536771131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28423906482667664392225397 2664741232750093536771131)
                      ·
                        rfl

theorem cell23_5189565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_5189565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189565 prefixEnd_5189565 := by exact prefixLift 5189565
  have htrace : WordTrace (prefixWord ++ tailWord_5189565) baseStart_5189565 baseEnd_5189565 := by
    simpa [prefixWord, tailWord_5189565, baseEnd_5189565] using wordTrace_append hprefix tailTrace_5189565
  have hstable : (prefixWord ++ tailWord_5189565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189565).length < 2 ^ (prefixWord ++ tailWord_5189565).sum := by decide
  have hdescent : baseEnd_5189565 < baseStart_5189565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189571 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 6]
def baseStart_5189571 : Nat := 118140960795 + 5189571 * 2 ^ 59
def prefixEnd_5189571 : Nat := 4983230072969 + 3 ^ 40 * 5189571 * 2
def baseEnd_5189571 : Nat := 2664744313634020513296103

theorem tailTrace_5189571 : CollatzResearch.WordTrace tailWord_5189571 prefixEnd_5189571 2664744313634020513296103 := by
  unfold tailWord_5189571
  simp only [CollatzResearch.WordTrace]
  refine ⟨189279204282078050009312567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126186136188052033339541711 189279204282078050009312567)
  ·
    refine ⟨283918806423117075013968851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189279204282078050009312567 283918806423117075013968851)
    ·
      refine ⟨425878209634675612520953277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283918806423117075013968851 425878209634675612520953277)
      ·
        refine ⟨159704328613003354695357479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425878209634675612520953277 159704328613003354695357479)
        ·
          refine ⟨239556492919505032043036219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159704328613003354695357479 239556492919505032043036219)
          ·
            refine ⟨359334739379257548064554329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239556492919505032043036219 359334739379257548064554329)
            ·
              refine ⟨269501054534443161048415747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359334739379257548064554329 269501054534443161048415747)
              ·
                refine ⟨404251581801664741572623621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269501054534443161048415747 404251581801664741572623621)
                ·
                  refine ⟨75797171587812139044866929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404251581801664741572623621 75797171587812139044866929)
                  ·
                    refine ⟨56847878690859104283650197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75797171587812139044866929 56847878690859104283650197)
                    ·
                      refine ⟨2664744313634020513296103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56847878690859104283650197 2664744313634020513296103)
                      ·
                        rfl

theorem cell23_5189571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_5189571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189571 prefixEnd_5189571 := by exact prefixLift 5189571
  have htrace : WordTrace (prefixWord ++ tailWord_5189571) baseStart_5189571 baseEnd_5189571 := by
    simpa [prefixWord, tailWord_5189571, baseEnd_5189571] using wordTrace_append hprefix tailTrace_5189571
  have hstable : (prefixWord ++ tailWord_5189571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189571).length < 2 ^ (prefixWord ++ tailWord_5189571).sum := by decide
  have hdescent : baseEnd_5189571 < baseStart_5189571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189588 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5189588 : Nat := 118140960795 + 5189588 * 2 ^ 59
def prefixEnd_5189588 : Nat := 4983230072969 + 3 ^ 40 * 5189588 * 2
def baseEnd_5189588 : Nat := 2664753042805146946783525

theorem tailTrace_5189588 : CollatzResearch.WordTrace tailWord_5189588 prefixEnd_5189588 2664753042805146946783525 := by
  unfold tailWord_5189588
  simp only [CollatzResearch.WordTrace]
  refine ⟨94639912161508230956340709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126186549548677641275120945 94639912161508230956340709)
  ·
    refine ⟨17744983530282793304313883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94639912161508230956340709 17744983530282793304313883)
    ·
      refine ⟨26617475295424189956470825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17744983530282793304313883 26617475295424189956470825)
      ·
        refine ⟨19963106471568142467353119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26617475295424189956470825 19963106471568142467353119)
        ·
          refine ⟨29944659707352213701029679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19963106471568142467353119 29944659707352213701029679)
          ·
            refine ⟨44916989561028320551544519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29944659707352213701029679 44916989561028320551544519)
            ·
              refine ⟨67375484341542480827316779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44916989561028320551544519 67375484341542480827316779)
              ·
                refine ⟨101063226512313721240975169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67375484341542480827316779 101063226512313721240975169)
                ·
                  refine ⟨75797419884235290930731377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101063226512313721240975169 75797419884235290930731377)
                  ·
                    refine ⟨56848064913176468198048533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75797419884235290930731377 56848064913176468198048533)
                    ·
                      refine ⟨2664753042805146946783525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56848064913176468198048533 2664753042805146946783525)
                      ·
                        rfl

theorem cell23_5189588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5189588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189588 prefixEnd_5189588 := by exact prefixLift 5189588
  have htrace : WordTrace (prefixWord ++ tailWord_5189588) baseStart_5189588 baseEnd_5189588 := by
    simpa [prefixWord, tailWord_5189588, baseEnd_5189588] using wordTrace_append hprefix tailTrace_5189588
  have hstable : (prefixWord ++ tailWord_5189588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189588).length < 2 ^ (prefixWord ++ tailWord_5189588).sum := by decide
  have hdescent : baseEnd_5189588 < baseStart_5189588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189589 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_5189589 : Nat := 118140960795 + 5189589 * 2 ^ 59
def prefixEnd_5189589 : Nat := 4983230072969 + 3 ^ 40 * 5189589 * 2
def baseEnd_5189589 : Nat := 888251185428600480957007

theorem tailTrace_5189589 : CollatzResearch.WordTrace tailWord_5189589 prefixEnd_5189589 888251185428600480957007 := by
  unfold tailWord_5189589
  simp only [CollatzResearch.WordTrace]
  refine ⟨189279860796012839083467821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126186573864008559388978547 189279860796012839083467821)
  ·
    refine ⟨70979947798504814656300433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189279860796012839083467821 70979947798504814656300433)
    ·
      refine ⟨53234960848878610992225325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70979947798504814656300433 53234960848878610992225325)
      ·
        refine ⟨19963110318329479122084497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53234960848878610992225325 19963110318329479122084497)
        ·
          refine ⟨14972332738747109341563373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19963110318329479122084497 14972332738747109341563373)
          ·
            refine ⟨5614624777030166003086265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14972332738747109341563373 5614624777030166003086265)
            ·
              refine ⟨4210968582772624502314699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5614624777030166003086265 4210968582772624502314699)
              ·
                refine ⟨6316452874158936753472049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210968582772624502314699 6316452874158936753472049)
                ·
                  refine ⟨4737339655619202565104037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6316452874158936753472049 4737339655619202565104037)
                  ·
                    refine ⟨888251185428600480957007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4737339655619202565104037 888251185428600480957007)
                    ·
                      rfl

theorem cell23_5189589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_5189589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189589 prefixEnd_5189589 := by exact prefixLift 5189589
  have htrace : WordTrace (prefixWord ++ tailWord_5189589) baseStart_5189589 baseEnd_5189589 := by
    simpa [prefixWord, tailWord_5189589, baseEnd_5189589] using wordTrace_append hprefix tailTrace_5189589
  have hstable : (prefixWord ++ tailWord_5189589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189589).length < 2 ^ (prefixWord ++ tailWord_5189589).sum := by decide
  have hdescent : baseEnd_5189589 < baseStart_5189589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189628 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_5189628 : Nat := 118140960795 + 5189628 * 2 ^ 59
def prefixEnd_5189628 : Nat := 4983230072969 + 3 ^ 40 * 5189628 * 2
def baseEnd_5189628 : Nat := 888257860677108930094447

theorem tailTrace_5189628 : CollatzResearch.WordTrace tailWord_5189628 prefixEnd_5189628 888257860677108930094447 := by
  unfold tailWord_5189628
  simp only [CollatzResearch.WordTrace]
  refine ⟨94640641621435774372068769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126187522161914365829425025 94640641621435774372068769)
  ·
    refine ⟨70980481216076830779051577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94640641621435774372068769 70980481216076830779051577)
    ·
      refine ⟨53235360912057623084288683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70980481216076830779051577 53235360912057623084288683)
      ·
        refine ⟨79853041368086434626433025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53235360912057623084288683 79853041368086434626433025)
        ·
          refine ⟨59889781026064825969824769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79853041368086434626433025 59889781026064825969824769)
          ·
            refine ⟨44917335769548619477368577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59889781026064825969824769 44917335769548619477368577)
            ·
              refine ⟨33688001827161464608026433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44917335769548619477368577 33688001827161464608026433)
              ·
                refine ⟨25266001370371098456019825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33688001827161464608026433 25266001370371098456019825)
                ·
                  refine ⟨18949501027778323842014869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25266001370371098456019825 18949501027778323842014869)
                  ·
                    refine ⟨888257860677108930094447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18949501027778323842014869 888257860677108930094447)
                    ·
                      rfl

theorem cell23_5189628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_5189628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189628 prefixEnd_5189628 := by exact prefixLift 5189628
  have htrace : WordTrace (prefixWord ++ tailWord_5189628) baseStart_5189628 baseEnd_5189628 := by
    simpa [prefixWord, tailWord_5189628, baseEnd_5189628] using wordTrace_append hprefix tailTrace_5189628
  have hstable : (prefixWord ++ tailWord_5189628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189628).length < 2 ^ (prefixWord ++ tailWord_5189628).sum := by decide
  have hdescent : baseEnd_5189628 < baseStart_5189628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189630 : List Nat := [4, 2, 2, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_5189630 : Nat := 118140960795 + 5189630 * 2 ^ 59
def prefixEnd_5189630 : Nat := 4983230072969 + 3 ^ 40 * 5189630 * 2
def baseEnd_5189630 : Nat := 2664774608992635782458333

theorem tailTrace_5189630 : CollatzResearch.WordTrace tailWord_5189630 prefixEnd_5189630 2664774608992635782458333 := by
  unfold tailWord_5189630
  simp only [CollatzResearch.WordTrace]
  refine ⟨23660169523608037885713793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126187570792576202057140229 23660169523608037885713793)
  ·
    refine ⟨17745127142706028414285345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23660169523608037885713793 17745127142706028414285345)
    ·
      refine ⟨13308845357029521310714009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17745127142706028414285345 13308845357029521310714009)
      ·
        refine ⟨9981634017772140983035507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13308845357029521310714009 9981634017772140983035507)
        ·
          refine ⟨14972451026658211474553261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9981634017772140983035507 14972451026658211474553261)
          ·
            refine ⟨5614669134996829302957473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14972451026658211474553261 5614669134996829302957473)
            ·
              refine ⟨4211001851247621977218105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5614669134996829302957473 4211001851247621977218105)
              ·
                refine ⟨3158251388435716482913579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4211001851247621977218105 3158251388435716482913579)
                ·
                  refine ⟨4737377082653574724370369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3158251388435716482913579 4737377082653574724370369)
                  ·
                    refine ⟨3553032811990181043277777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4737377082653574724370369 3553032811990181043277777)
                    ·
                      refine ⟨2664774608992635782458333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553032811990181043277777 2664774608992635782458333)
                      ·
                        rfl

theorem cell23_5189630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_5189630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189630 prefixEnd_5189630 := by exact prefixLift 5189630
  have htrace : WordTrace (prefixWord ++ tailWord_5189630) baseStart_5189630 baseEnd_5189630 := by
    simpa [prefixWord, tailWord_5189630, baseEnd_5189630] using wordTrace_append hprefix tailTrace_5189630
  have hstable : (prefixWord ++ tailWord_5189630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189630).length < 2 ^ (prefixWord ++ tailWord_5189630).sum := by decide
  have hdescent : baseEnd_5189630 < baseStart_5189630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189648 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_5189648 : Nat := 118140960795 + 5189648 * 2 ^ 59
def prefixEnd_5189648 : Nat := 4983230072969 + 3 ^ 40 * 5189648 * 2
def baseEnd_5189648 : Nat := 2664783851644416712033249

theorem tailTrace_5189648 : CollatzResearch.WordTrace tailWord_5189648 prefixEnd_5189648 2664783851644416712033249 := by
  unfold tailWord_5189648
  simp only [CollatzResearch.WordTrace]
  refine ⟨94641006351399546079932799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126188008468532728106577065 94641006351399546079932799)
  ·
    refine ⟨141961509527099319119899199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94641006351399546079932799 141961509527099319119899199)
    ·
      refine ⟨212942264290648978679848799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141961509527099319119899199 212942264290648978679848799)
      ·
        refine ⟨319413396435973468019773199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212942264290648978679848799 319413396435973468019773199)
        ·
          refine ⟨479120094653960202029659799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319413396435973468019773199 479120094653960202029659799)
          ·
            refine ⟨718680141980940303044489699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479120094653960202029659799 718680141980940303044489699)
            ·
              refine ⟨1078020212971410454566734549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718680141980940303044489699 1078020212971410454566734549)
              ·
                refine ⟨25266098741517432528907841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1078020212971410454566734549 25266098741517432528907841)
                ·
                  refine ⟨18949574056138074396680881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25266098741517432528907841 18949574056138074396680881)
                  ·
                    refine ⟨14212180542103555797510661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18949574056138074396680881 14212180542103555797510661)
                    ·
                      refine ⟨2664783851644416712033249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14212180542103555797510661 2664783851644416712033249)
                      ·
                        rfl

theorem cell23_5189648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_5189648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189648 prefixEnd_5189648 := by exact prefixLift 5189648
  have htrace : WordTrace (prefixWord ++ tailWord_5189648) baseStart_5189648 baseEnd_5189648 := by
    simpa [prefixWord, tailWord_5189648, baseEnd_5189648] using wordTrace_append hprefix tailTrace_5189648
  have hstable : (prefixWord ++ tailWord_5189648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189648).length < 2 ^ (prefixWord ++ tailWord_5189648).sum := by decide
  have hdescent : baseEnd_5189648 < baseStart_5189648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189658 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 9]
def baseStart_5189658 : Nat := 118140960795 + 5189658 * 2 ^ 59
def prefixEnd_5189658 : Nat := 4983230072969 + 3 ^ 40 * 5189658 * 2
def baseEnd_5189658 : Nat := 296087665161217963656467

theorem tailTrace_5189658 : CollatzResearch.WordTrace tailWord_5189658 prefixEnd_5189658 296087665161217963656467 := by
  unfold tailWord_5189658
  simp only [CollatzResearch.WordTrace]
  refine ⟨47320594358190715966932407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126188251621841909245153085 47320594358190715966932407)
  ·
    refine ⟨70980891537286073950398611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47320594358190715966932407 70980891537286073950398611)
    ·
      refine ⟨106471337305929110925597917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70980891537286073950398611 106471337305929110925597917)
      ·
        refine ⟨39926751489723416597099219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106471337305929110925597917 39926751489723416597099219)
        ·
          refine ⟨59890127234585124895648829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39926751489723416597099219 59890127234585124895648829)
          ·
            refine ⟨22458797712969421835868311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59890127234585124895648829 22458797712969421835868311)
            ·
              refine ⟨33688196569454132753802467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22458797712969421835868311 33688196569454132753802467)
              ·
                refine ⟨50532294854181199130703701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33688196569454132753802467 50532294854181199130703701)
                ·
                  refine ⟨296087665161217963656467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50532294854181199130703701 296087665161217963656467)
                  ·
                    rfl

theorem cell23_5189658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_5189658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189658 prefixEnd_5189658 := by exact prefixLift 5189658
  have htrace : WordTrace (prefixWord ++ tailWord_5189658) baseStart_5189658 baseEnd_5189658 := by
    simpa [prefixWord, tailWord_5189658, baseEnd_5189658] using wordTrace_append hprefix tailTrace_5189658
  have hstable : (prefixWord ++ tailWord_5189658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189658).length < 2 ^ (prefixWord ++ tailWord_5189658).sum := by decide
  have hdescent : baseEnd_5189658 < baseStart_5189658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189685 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_5189685 : Nat := 118140960795 + 5189685 * 2 ^ 59
def prefixEnd_5189685 : Nat := 4983230072969 + 3 ^ 40 * 5189685 * 2
def baseEnd_5189685 : Nat := 2664802850428633067270579

theorem tailTrace_5189685 : CollatzResearch.WordTrace tailWord_5189685 prefixEnd_5189685 2664802850428633067270579 := by
  unfold tailWord_5189685
  simp only [CollatzResearch.WordTrace]
  refine ⟨189283362203665047478962509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126188908135776698319308339 189283362203665047478962509)
  ·
    refine ⟨70981260826374392804610941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 189283362203665047478962509 70981260826374392804610941)
    ·
      refine ⟨26617972809890397301729103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70981260826374392804610941 26617972809890397301729103)
      ·
        refine ⟨39926959214835595952593655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26617972809890397301729103 39926959214835595952593655)
        ·
          refine ⟨59890438822253393928890483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39926959214835595952593655 59890438822253393928890483)
          ·
            refine ⟨89835658233380090893335725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59890438822253393928890483 89835658233380090893335725)
            ·
              refine ⟨33688371837517534085000897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89835658233380090893335725 33688371837517534085000897)
              ·
                refine ⟨25266278878138150563750673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33688371837517534085000897 25266278878138150563750673)
                ·
                  refine ⟨18949709158603612922813005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25266278878138150563750673 18949709158603612922813005)
                  ·
                    refine ⟨7106140934476354846054877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18949709158603612922813005 7106140934476354846054877)
                    ·
                      refine ⟨2664802850428633067270579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7106140934476354846054877 2664802850428633067270579)
                      ·
                        rfl

theorem cell23_5189685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_5189685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189685 prefixEnd_5189685 := by exact prefixLift 5189685
  have htrace : WordTrace (prefixWord ++ tailWord_5189685) baseStart_5189685 baseEnd_5189685 := by
    simpa [prefixWord, tailWord_5189685, baseEnd_5189685] using wordTrace_append hprefix tailTrace_5189685
  have hstable : (prefixWord ++ tailWord_5189685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189685).length < 2 ^ (prefixWord ++ tailWord_5189685).sum := by decide
  have hdescent : baseEnd_5189685 < baseStart_5189685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189695 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 1, 7, 2]
def baseStart_5189695 : Nat := 118140960795 + 5189695 * 2 ^ 59
def prefixEnd_5189695 : Nat := 4983230072969 + 3 ^ 40 * 5189695 * 2
def baseEnd_5189695 : Nat := 2664807985235178028145533

theorem tailTrace_5189695 : CollatzResearch.WordTrace tailWord_5189695 prefixEnd_5189695 2664807985235178028145533 := by
  unfold tailWord_5189695
  simp only [CollatzResearch.WordTrace]
  refine ⟨189283726933628819186826539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126189151289085879457884359 189283726933628819186826539)
  ·
    refine ⟨283925590400443228780239809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189283726933628819186826539 283925590400443228780239809)
    ·
      refine ⟨212944192800332421585179857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283925590400443228780239809 212944192800332421585179857)
      ·
        refine ⟨159708144600249316188884893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212944192800332421585179857 159708144600249316188884893)
        ·
          refine ⟨59890554225093493570831835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159708144600249316188884893 59890554225093493570831835)
          ·
            refine ⟨89835831337640240356247753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59890554225093493570831835 89835831337640240356247753)
            ·
              refine ⟨67376873503230180267185815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89835831337640240356247753 67376873503230180267185815)
              ·
                refine ⟨101065310254845270400778723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67376873503230180267185815 101065310254845270400778723)
                ·
                  refine ⟨151597965382267905601168085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101065310254845270400778723 151597965382267905601168085)
                  ·
                    refine ⟨3553077313646904037527377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 151597965382267905601168085 3553077313646904037527377)
                    ·
                      refine ⟨2664807985235178028145533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3553077313646904037527377 2664807985235178028145533)
                      ·
                        rfl

theorem cell23_5189695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_5189695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189695 prefixEnd_5189695 := by exact prefixLift 5189695
  have htrace : WordTrace (prefixWord ++ tailWord_5189695) baseStart_5189695 baseEnd_5189695 := by
    simpa [prefixWord, tailWord_5189695, baseEnd_5189695] using wordTrace_append hprefix tailTrace_5189695
  have hstable : (prefixWord ++ tailWord_5189695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189695).length < 2 ^ (prefixWord ++ tailWord_5189695).sum := by decide
  have hdescent : baseEnd_5189695 < baseStart_5189695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189742 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_5189742 : Nat := 118140960795 + 5189742 * 2 ^ 59
def prefixEnd_5189742 : Nat := 4983230072969 + 3 ^ 40 * 5189742 * 2
def baseEnd_5189742 : Nat := 2664832118825939344257817

theorem tailTrace_5189742 : CollatzResearch.WordTrace tailWord_5189742 prefixEnd_5189742 2664832118825939344257817 := by
  unfold tailWord_5189742
  simp only [CollatzResearch.WordTrace]
  refine ⟨23660680145557318276723435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126190294109639030809191653 23660680145557318276723435)
  ·
    refine ⟨35491020218335977415085153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23660680145557318276723435 35491020218335977415085153)
    ·
      refine ⟨26618265163751983061313865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35491020218335977415085153 26618265163751983061313865)
      ·
        refine ⟨19963698872813987295985399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26618265163751983061313865 19963698872813987295985399)
        ·
          refine ⟨29945548309220980943978099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19963698872813987295985399 29945548309220980943978099)
          ·
            refine ⟨44918322463831471415967149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29945548309220980943978099 44918322463831471415967149)
            ·
              refine ⟨16844370923936801780987681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44918322463831471415967149 16844370923936801780987681)
              ·
                refine ⟨12633278192952601335740761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16844370923936801780987681 12633278192952601335740761)
                ·
                  refine ⟨9474958644714451001805571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12633278192952601335740761 9474958644714451001805571)
                  ·
                    refine ⟨14212437967071676502708357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9474958644714451001805571 14212437967071676502708357)
                    ·
                      refine ⟨2664832118825939344257817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14212437967071676502708357 2664832118825939344257817)
                      ·
                        rfl

theorem cell23_5189742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_5189742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189742 prefixEnd_5189742 := by exact prefixLift 5189742
  have htrace : WordTrace (prefixWord ++ tailWord_5189742) baseStart_5189742 baseEnd_5189742 := by
    simpa [prefixWord, tailWord_5189742, baseEnd_5189742] using wordTrace_append hprefix tailTrace_5189742
  have hstable : (prefixWord ++ tailWord_5189742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189742).length < 2 ^ (prefixWord ++ tailWord_5189742).sum := by decide
  have hdescent : baseEnd_5189742 < baseStart_5189742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5189799 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 6]
def baseStart_5189799 : Nat := 118140960795 + 5189799 * 2 ^ 59
def prefixEnd_5189799 : Nat := 4983230072969 + 3 ^ 40 * 5189799 * 2
def baseEnd_5189799 : Nat := 296095709691471735693895

theorem tailTrace_5189799 : CollatzResearch.WordTrace tailWord_5189799 prefixEnd_5189799 296095709691471735693895 := by
  unfold tailWord_5189799
  simp only [CollatzResearch.WordTrace]
  refine ⟨189287520125252044948612451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126191680083501363299074967 189287520125252044948612451)
  ·
    refine ⟨283931280187878067422918677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189287520125252044948612451 283931280187878067422918677)
    ·
      refine ⟨13309278758806784410449313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 283931280187878067422918677 13309278758806784410449313)
      ·
        refine ⟨9981959069105088307836985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13309278758806784410449313 9981959069105088307836985)
        ·
          refine ⟨7486469301828816230877739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9981959069105088307836985 7486469301828816230877739)
          ·
            refine ⟨11229703952743224346316609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7486469301828816230877739 11229703952743224346316609)
            ·
              refine ⟨8422277964557418259737457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11229703952743224346316609 8422277964557418259737457)
              ·
                refine ⟨6316708473418063694803093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8422277964557418259737457 6316708473418063694803093)
                ·
                  refine ⟨296095709691471735693895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6316708473418063694803093 296095709691471735693895)
                  ·
                    rfl

theorem cell23_5189799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 6].length) (baseStart_5189799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5189799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5189799 prefixEnd_5189799 := by exact prefixLift 5189799
  have htrace : WordTrace (prefixWord ++ tailWord_5189799) baseStart_5189799 baseEnd_5189799 := by
    simpa [prefixWord, tailWord_5189799, baseEnd_5189799] using wordTrace_append hprefix tailTrace_5189799
  have hstable : (prefixWord ++ tailWord_5189799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5189799).length < 2 ^ (prefixWord ++ tailWord_5189799).sum := by decide
  have hdescent : baseEnd_5189799 < baseStart_5189799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5189799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
