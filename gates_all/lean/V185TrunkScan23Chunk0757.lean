import V185TrunkScan23Chunk0756

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4476283 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 5, 4]
def baseStart_4476283 : Nat := 118140960795 + 4476283 * 2 ^ 59
def prefixEnd_4476283 : Nat := 4983230072969 + 3 ^ 40 * 4476283 * 2
def baseEnd_4476283 : Nat := 766161574849938418625485

theorem tailTrace_4476283 : CollatzResearch.WordTrace tailWord_4476283 prefixEnd_4476283 766161574849938418625485 := by
  unfold tailWord_4476283
  simp only [CollatzResearch.WordTrace]
  refine ⟨163263453642198654117489503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108842302428132436078326335 163263453642198654117489503)
  ·
    refine ⟨244895180463297981176234255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163263453642198654117489503 244895180463297981176234255)
    ·
      refine ⟨367342770694946971764351383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244895180463297981176234255 367342770694946971764351383)
      ·
        refine ⟨551014156042420457646527075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367342770694946971764351383 551014156042420457646527075)
        ·
          refine ⟨826521234063630686469790613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551014156042420457646527075 826521234063630686469790613)
          ·
            refine ⟨38743182846732688428271435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 826521234063630686469790613 38743182846732688428271435)
            ·
              refine ⟨58114774270099032642407153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38743182846732688428271435 58114774270099032642407153)
              ·
                refine ⟨43586080702574274481805365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58114774270099032642407153 43586080702574274481805365)
                ·
                  refine ⟨4086195065866338232669253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43586080702574274481805365 4086195065866338232669253)
                  ·
                    refine ⟨766161574849938418625485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4086195065866338232669253 766161574849938418625485)
                    ·
                      rfl

theorem cell23_4476283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 5, 4].length) (baseStart_4476283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476283 prefixEnd_4476283 := by exact prefixLift 4476283
  have htrace : WordTrace (prefixWord ++ tailWord_4476283) baseStart_4476283 baseEnd_4476283 := by
    simpa [prefixWord, tailWord_4476283, baseEnd_4476283] using wordTrace_append hprefix tailTrace_4476283
  have hstable : (prefixWord ++ tailWord_4476283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476283).length < 2 ^ (prefixWord ++ tailWord_4476283).sum := by decide
  have hdescent : baseEnd_4476283 < baseStart_4476283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476300 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_4476300 : Nat := 118140960795 + 4476300 * 2 ^ 59
def prefixEnd_4476300 : Nat := 4983230072969 + 3 ^ 40 * 4476300 * 2
def baseEnd_4476300 : Nat := 766164484573647229787959

theorem tailTrace_4476300 : CollatzResearch.WordTrace tailWord_4476300 prefixEnd_4476300 766164484573647229787959 := by
  unfold tailWord_4476300
  simp only [CollatzResearch.WordTrace]
  refine ⟨81632036841568533010429177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108842715788758044013905569 81632036841568533010429177)
  ·
    refine ⟨61224027631176399757821883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81632036841568533010429177 61224027631176399757821883)
    ·
      refine ⟨91836041446764599636732825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61224027631176399757821883 91836041446764599636732825)
      ·
        refine ⟨68877031085073449727549619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91836041446764599636732825 68877031085073449727549619)
        ·
          refine ⟨103315546627610174591324429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68877031085073449727549619 103315546627610174591324429)
          ·
            refine ⟨38743329985353815471746661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103315546627610174591324429 38743329985353815471746661)
            ·
              refine ⟨7264374372253840400952499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38743329985353815471746661 7264374372253840400952499)
              ·
                refine ⟨10896561558380760601428749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7264374372253840400952499 10896561558380760601428749)
                ·
                  refine ⟨4086210584392785225535781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10896561558380760601428749 4086210584392785225535781)
                  ·
                    refine ⟨766164484573647229787959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4086210584392785225535781 766164484573647229787959)
                    ·
                      rfl

theorem cell23_4476300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_4476300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476300 prefixEnd_4476300 := by exact prefixLift 4476300
  have htrace : WordTrace (prefixWord ++ tailWord_4476300) baseStart_4476300 baseEnd_4476300 := by
    simpa [prefixWord, tailWord_4476300, baseEnd_4476300] using wordTrace_append hprefix tailTrace_4476300
  have hstable : (prefixWord ++ tailWord_4476300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476300).length < 2 ^ (prefixWord ++ tailWord_4476300).sum := by decide
  have hdescent : baseEnd_4476300 < baseStart_4476300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476323 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 3]
def baseStart_4476323 : Nat := 118140960795 + 4476323 * 2 ^ 59
def prefixEnd_4476323 : Nat := 4983230072969 + 3 ^ 40 * 4476323 * 2
def baseEnd_4476323 : Nat := 2298505263775995099376271

theorem tailTrace_4476323 : CollatzResearch.WordTrace tailWord_4476323 prefixEnd_4476323 2298505263775995099376271 := by
  unfold tailWord_4476323
  simp only [CollatzResearch.WordTrace]
  refine ⟨163264912562053740948945623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108843275041369160632630415 163264912562053740948945623)
  ·
    refine ⟨244897368843080611423418435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163264912562053740948945623 244897368843080611423418435)
    ·
      refine ⟨367346053264620917135127653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244897368843080611423418435 367346053264620917135127653)
      ·
        refine ⟨68877384987116421962836435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 367346053264620917135127653 68877384987116421962836435)
        ·
          refine ⟨103316077480674632944254653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68877384987116421962836435 103316077480674632944254653)
          ·
            refine ⟨38743529055252987354095495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103316077480674632944254653 38743529055252987354095495)
            ·
              refine ⟨58115293582879481031143243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38743529055252987354095495 58115293582879481031143243)
              ·
                refine ⟨87172940374319221546714865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58115293582879481031143243 87172940374319221546714865)
                ·
                  refine ⟨65379705280739416160036149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87172940374319221546714865 65379705280739416160036149)
                  ·
                    refine ⟨6129347370069320265003389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65379705280739416160036149 6129347370069320265003389)
                    ·
                      refine ⟨2298505263775995099376271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6129347370069320265003389 2298505263775995099376271)
                      ·
                        rfl

theorem cell23_4476323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_4476323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476323 prefixEnd_4476323 := by exact prefixLift 4476323
  have htrace : WordTrace (prefixWord ++ tailWord_4476323) baseStart_4476323 baseEnd_4476323 := by
    simpa [prefixWord, tailWord_4476323, baseEnd_4476323] using wordTrace_append hprefix tailTrace_4476323
  have hstable : (prefixWord ++ tailWord_4476323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476323).length < 2 ^ (prefixWord ++ tailWord_4476323).sum := by decide
  have hdescent : baseEnd_4476323 < baseStart_4476323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476377 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 1, 5]
def baseStart_4476377 : Nat := 118140960795 + 4476377 * 2 ^ 59
def prefixEnd_4476377 : Nat := 4983230072969 + 3 ^ 40 * 4476377 * 2
def baseEnd_4476377 : Nat := 766177663910445962700341

theorem tailTrace_4476377 : CollatzResearch.WordTrace tailWord_4476377 prefixEnd_4476377 766177663910445962700341 := by
  unfold tailWord_4476377
  simp only [CollatzResearch.WordTrace]
  refine ⟨163266882103858108171411385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108844588069238738780940923 163266882103858108171411385)
  ·
    refine ⟨122450161577893581128558539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163266882103858108171411385 122450161577893581128558539)
    ·
      refine ⟨183675242366840371692837809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122450161577893581128558539 183675242366840371692837809)
      ·
        refine ⟨137756431775130278769628357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183675242366840371692837809 137756431775130278769628357)
        ·
          refine ⟨25829330957836927269305317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137756431775130278769628357 25829330957836927269305317)
          ·
            refine ⟨4842999554594423862994747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25829330957836927269305317 4842999554594423862994747)
            ·
              refine ⟨7264499331891635794492121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842999554594423862994747 7264499331891635794492121)
              ·
                refine ⟨5448374498918726845869091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7264499331891635794492121 5448374498918726845869091)
                ·
                  refine ⟨8172561748378090268803637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448374498918726845869091 8172561748378090268803637)
                  ·
                    refine ⟨766177663910445962700341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8172561748378090268803637 766177663910445962700341)
                    ·
                      rfl

theorem cell23_4476377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_4476377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476377 prefixEnd_4476377 := by exact prefixLift 4476377
  have htrace : WordTrace (prefixWord ++ tailWord_4476377) baseStart_4476377 baseEnd_4476377 := by
    simpa [prefixWord, tailWord_4476377, baseEnd_4476377] using wordTrace_append hprefix tailTrace_4476377
  have hstable : (prefixWord ++ tailWord_4476377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476377).length < 2 ^ (prefixWord ++ tailWord_4476377).sum := by decide
  have hdescent : baseEnd_4476377 < baseStart_4476377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476394 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_4476394 : Nat := 118140960795 + 4476394 * 2 ^ 59
def prefixEnd_4476394 : Nat := 4983230072969 + 3 ^ 40 * 4476394 * 2
def baseEnd_4476394 : Nat := 766180573634154773862815

theorem tailTrace_4476394 : CollatzResearch.WordTrace tailWord_4476394 prefixEnd_4476394 766180573634154773862815 := by
  unfold tailWord_4476394
  simp only [CollatzResearch.WordTrace]
  refine ⟨40816875536199130018695059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108845001429864346716520157 40816875536199130018695059)
  ·
    refine ⟨61225313304298695028042589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40816875536199130018695059 61225313304298695028042589)
    ·
      refine ⟨22959492489112010635515971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61225313304298695028042589 22959492489112010635515971)
      ·
        refine ⟨34439238733668015953273957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22959492489112010635515971 34439238733668015953273957)
        ·
          refine ⟨6457357262562752991238867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34439238733668015953273957 6457357262562752991238867)
          ·
            refine ⟨9686035893844129486858301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6457357262562752991238867 9686035893844129486858301)
            ·
              refine ⟨3632263460191548557571863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9686035893844129486858301 3632263460191548557571863)
              ·
                refine ⟨5448395190287322836357795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632263460191548557571863 5448395190287322836357795)
                ·
                  refine ⟨8172592785430984254536693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448395190287322836357795 8172592785430984254536693)
                  ·
                    refine ⟨766180573634154773862815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8172592785430984254536693 766180573634154773862815)
                    ·
                      rfl

theorem cell23_4476394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_4476394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476394 prefixEnd_4476394 := by exact prefixLift 4476394
  have htrace : WordTrace (prefixWord ++ tailWord_4476394) baseStart_4476394 baseEnd_4476394 := by
    simpa [prefixWord, tailWord_4476394, baseEnd_4476394] using wordTrace_append hprefix tailTrace_4476394
  have hstable : (prefixWord ++ tailWord_4476394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476394).length < 2 ^ (prefixWord ++ tailWord_4476394).sum := by decide
  have hdescent : baseEnd_4476394 < baseStart_4476394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476400 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 5]
def baseStart_4476400 : Nat := 118140960795 + 4476400 * 2 ^ 59
def prefixEnd_4476400 : Nat := 4983230072969 + 3 ^ 40 * 4476400 * 2
def baseEnd_4476400 : Nat := 2298544801786391298113417

theorem tailTrace_4476400 : CollatzResearch.WordTrace tailWord_4476400 prefixEnd_4476400 2298544801786391298113417 := by
  unfold tailWord_4476400
  simp only [CollatzResearch.WordTrace]
  refine ⟨81633860491387391549749327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108845147321849855399665769 81633860491387391549749327)
  ·
    refine ⟨122450790737081087324623991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81633860491387391549749327 122450790737081087324623991)
    ·
      refine ⟨183676186105621630986935987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122450790737081087324623991 183676186105621630986935987)
      ·
        refine ⟨275514279158432446480403981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183676186105621630986935987 275514279158432446480403981)
        ·
          refine ⟨103317854684412167430151493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275514279158432446480403981 103317854684412167430151493)
          ·
            refine ⟨19372097753327281393153405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103317854684412167430151493 19372097753327281393153405)
            ·
              refine ⟨7264536657497730522432527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19372097753327281393153405 7264536657497730522432527)
              ·
                refine ⟨10896804986246595783648791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7264536657497730522432527 10896804986246595783648791)
                ·
                  refine ⟨16345207479369893675473187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10896804986246595783648791 16345207479369893675473187)
                  ·
                    refine ⟨24517811219054840513209781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16345207479369893675473187 24517811219054840513209781)
                    ·
                      refine ⟨2298544801786391298113417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24517811219054840513209781 2298544801786391298113417)
                      ·
                        rfl

theorem cell23_4476400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_4476400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476400 prefixEnd_4476400 := by exact prefixLift 4476400
  have htrace : WordTrace (prefixWord ++ tailWord_4476400) baseStart_4476400 baseEnd_4476400 := by
    simpa [prefixWord, tailWord_4476400, baseEnd_4476400] using wordTrace_append hprefix tailTrace_4476400
  have hstable : (prefixWord ++ tailWord_4476400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476400).length < 2 ^ (prefixWord ++ tailWord_4476400).sum := by decide
  have hdescent : baseEnd_4476400 < baseStart_4476400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476427 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 4]
def baseStart_4476427 : Nat := 118140960795 + 4476427 * 2 ^ 59
def prefixEnd_4476427 : Nat := 4983230072969 + 3 ^ 40 * 4476427 * 2
def baseEnd_4476427 : Nat := 2298558665764062692475793

theorem tailTrace_4476427 : CollatzResearch.WordTrace tailWord_4476427 prefixEnd_4476427 2298558665764062692475793 := by
  unfold tailWord_4476427
  simp only [CollatzResearch.WordTrace]
  refine ⟨163268705753676966710731535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108845803835784644473821023 163268705753676966710731535)
  ·
    refine ⟨244903058630515450066097303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163268705753676966710731535 244903058630515450066097303)
    ·
      refine ⟨367354587945773175099145955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244903058630515450066097303 367354587945773175099145955)
      ·
        refine ⟨551031881918659762648718933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367354587945773175099145955 551031881918659762648718933)
        ·
          refine ⟨6457404866234294093539675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 551031881918659762648718933 6457404866234294093539675)
          ·
            refine ⟨9686107299351441140309513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6457404866234294093539675 9686107299351441140309513)
            ·
              refine ⟨7264580474513580855232135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9686107299351441140309513 7264580474513580855232135)
              ·
                refine ⟨10896870711770371282848203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7264580474513580855232135 10896870711770371282848203)
                ·
                  refine ⟨16345306067655556924272305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10896870711770371282848203 16345306067655556924272305)
                  ·
                    refine ⟨12258979550741667693204229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16345306067655556924272305 12258979550741667693204229)
                    ·
                      refine ⟨2298558665764062692475793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12258979550741667693204229 2298558665764062692475793)
                      ·
                        rfl

theorem cell23_4476427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 4].length) (baseStart_4476427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476427 prefixEnd_4476427 := by exact prefixLift 4476427
  have htrace : WordTrace (prefixWord ++ tailWord_4476427) baseStart_4476427 baseEnd_4476427 := by
    simpa [prefixWord, tailWord_4476427, baseEnd_4476427] using wordTrace_append hprefix tailTrace_4476427
  have hstable : (prefixWord ++ tailWord_4476427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476427).length < 2 ^ (prefixWord ++ tailWord_4476427).sum := by decide
  have hdescent : baseEnd_4476427 < baseStart_4476427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476433 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 2, 7]
def baseStart_4476433 : Nat := 118140960795 + 4476433 * 2 ^ 59
def prefixEnd_4476433 : Nat := 4983230072969 + 3 ^ 40 * 4476433 * 2
def baseEnd_4476433 : Nat := 766187248882663223000255

theorem tailTrace_4476433 : CollatzResearch.WordTrace tailWord_4476433 prefixEnd_4476433 766187248882663223000255 := by
  unfold tailWord_4476433
  simp only [CollatzResearch.WordTrace]
  refine ⟨163268924591655229735449953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108845949727770153156966635 163268924591655229735449953)
  ·
    refine ⟨122451693443741422301587465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163268924591655229735449953 122451693443741422301587465)
    ·
      refine ⟨91838770082806066726190599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122451693443741422301587465 91838770082806066726190599)
      ·
        refine ⟨137758155124209100089285899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91838770082806066726190599 137758155124209100089285899)
        ·
          refine ⟨206637232686313650133928849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137758155124209100089285899 206637232686313650133928849)
          ·
            refine ⟨154977924514735237600446637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206637232686313650133928849 154977924514735237600446637)
            ·
              refine ⟨58116721693025714100167489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154977924514735237600446637 58116721693025714100167489)
              ·
                refine ⟨43587541269769285575125617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58116721693025714100167489 43587541269769285575125617)
                ·
                  refine ⟨32690655952326964181344213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43587541269769285575125617 32690655952326964181344213)
                  ·
                    refine ⟨766187248882663223000255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32690655952326964181344213 766187248882663223000255)
                    ·
                      rfl

theorem cell23_4476433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_4476433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476433 prefixEnd_4476433 := by exact prefixLift 4476433
  have htrace : WordTrace (prefixWord ++ tailWord_4476433) baseStart_4476433 baseEnd_4476433 := by
    simpa [prefixWord, tailWord_4476433, baseEnd_4476433] using wordTrace_append hprefix tailTrace_4476433
  have hstable : (prefixWord ++ tailWord_4476433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476433).length < 2 ^ (prefixWord ++ tailWord_4476433).sum := by decide
  have hdescent : baseEnd_4476433 < baseStart_4476433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476448 : List Nat := [2, 1, 1, 6, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4476448 : Nat := 118140960795 + 4476448 * 2 ^ 59
def prefixEnd_4476448 : Nat := 4983230072969 + 3 ^ 40 * 4476448 * 2
def baseEnd_4476448 : Nat := 2298569448857807110313197

theorem tailTrace_4476448 : CollatzResearch.WordTrace tailWord_4476448 prefixEnd_4476448 2298569448857807110313197 := by
  unfold tailWord_4476448
  simp only [CollatzResearch.WordTrace]
  refine ⟨81634735843300443648622999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108846314457733924864830665 81634735843300443648622999)
  ·
    refine ⟨122452103764950665472934499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81634735843300443648622999 122452103764950665472934499)
    ·
      refine ⟨183678155647425998209401749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122452103764950665472934499 183678155647425998209401749)
      ·
        refine ⟨8609913545973093666065707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 183678155647425998209401749 8609913545973093666065707)
        ·
          refine ⟨12914870318959640499098561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8609913545973093666065707 12914870318959640499098561)
          ·
            refine ⟨9686152739219730374323921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12914870318959640499098561 9686152739219730374323921)
            ·
              refine ⟨7264614554414797780742941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9686152739219730374323921 7264614554414797780742941)
              ·
                refine ⟨2724230457905549167778603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7264614554414797780742941 2724230457905549167778603)
                ·
                  refine ⟨4086345686858323751667905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724230457905549167778603 4086345686858323751667905)
                  ·
                    refine ⟨3064759265143742813750929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4086345686858323751667905 3064759265143742813750929)
                    ·
                      refine ⟨2298569448857807110313197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064759265143742813750929 2298569448857807110313197)
                      ·
                        rfl

theorem cell23_4476448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4476448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476448 prefixEnd_4476448 := by exact prefixLift 4476448
  have htrace : WordTrace (prefixWord ++ tailWord_4476448) baseStart_4476448 baseEnd_4476448 := by
    simpa [prefixWord, tailWord_4476448, baseEnd_4476448] using wordTrace_append hprefix tailTrace_4476448
  have hstable : (prefixWord ++ tailWord_4476448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476448).length < 2 ^ (prefixWord ++ tailWord_4476448).sum := by decide
  have hdescent : baseEnd_4476448 < baseStart_4476448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476451 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 1, 2, 3]
def baseStart_4476451 : Nat := 118140960795 + 4476451 * 2 ^ 59
def prefixEnd_4476451 : Nat := 4983230072969 + 3 ^ 40 * 4476451 * 2
def baseEnd_4476451 : Nat := 2298570989299770598575683

theorem tailTrace_4476451 : CollatzResearch.WordTrace tailWord_4476451 prefixEnd_4476451 2298570989299770598575683 := by
  unfold tailWord_4476451
  simp only [CollatzResearch.WordTrace]
  refine ⟨163269581105590018809605207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108846387403726679206403471 163269581105590018809605207)
  ·
    refine ⟨244904371658385028214407811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163269581105590018809605207 244904371658385028214407811)
    ·
      refine ⟨367356557487577542321611717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244904371658385028214407811 367356557487577542321611717)
      ·
        refine ⟨68879354528920789185302197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 367356557487577542321611717 68879354528920789185302197)
        ·
          refine ⟨6457439487086323986122081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68879354528920789185302197 6457439487086323986122081)
          ·
            refine ⟨4843079615314742989591561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6457439487086323986122081 4843079615314742989591561)
            ·
              refine ⟨3632309711486057242193671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4843079615314742989591561 3632309711486057242193671)
              ·
                refine ⟨5448464567229085863290507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632309711486057242193671 5448464567229085863290507)
                ·
                  refine ⟨8172696850843628794935761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448464567229085863290507 8172696850843628794935761)
                  ·
                    refine ⟨6129522638132721596201821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8172696850843628794935761 6129522638132721596201821)
                    ·
                      refine ⟨2298570989299770598575683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6129522638132721596201821 2298570989299770598575683)
                      ·
                        rfl

theorem cell23_4476451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_4476451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476451 prefixEnd_4476451 := by exact prefixLift 4476451
  have htrace : WordTrace (prefixWord ++ tailWord_4476451) baseStart_4476451 baseEnd_4476451 := by
    simpa [prefixWord, tailWord_4476451, baseEnd_4476451] using wordTrace_append hprefix tailTrace_4476451
  have hstable : (prefixWord ++ tailWord_4476451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476451).length < 2 ^ (prefixWord ++ tailWord_4476451).sum := by decide
  have hdescent : baseEnd_4476451 < baseStart_4476451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476481 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_4476481 : Nat := 118140960795 + 4476481 * 2 ^ 59
def prefixEnd_4476481 : Nat := 4983230072969 + 3 ^ 40 * 4476481 * 2
def baseEnd_4476481 : Nat := 2298586393719405481200545

theorem tailTrace_4476481 : CollatzResearch.WordTrace tailWord_4476481 prefixEnd_4476481 2298586393719405481200545 := by
  unfold tailWord_4476481
  simp only [CollatzResearch.WordTrace]
  refine ⟨163270675295481333933197297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108847116863654222622131531 163270675295481333933197297)
  ·
    refine ⟨122453006471611000449897973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163270675295481333933197297 122453006471611000449897973)
    ·
      refine ⟨11479969356713531292177935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122453006471611000449897973 11479969356713531292177935)
      ·
        refine ⟨17219954035070296938266903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11479969356713531292177935 17219954035070296938266903)
        ·
          refine ⟨25829931052605445407400355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17219954035070296938266903 25829931052605445407400355)
          ·
            refine ⟨38744896578908168111100533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25829931052605445407400355 38744896578908168111100533)
            ·
              refine ⟨3632334054272640760415675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38744896578908168111100533 3632334054272640760415675)
              ·
                refine ⟨5448501081408961140623513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632334054272640760415675 5448501081408961140623513)
                ·
                  refine ⟨4086375811056720855467635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5448501081408961140623513 4086375811056720855467635)
                  ·
                    refine ⟨6129563716585081283201453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4086375811056720855467635 6129563716585081283201453)
                    ·
                      refine ⟨2298586393719405481200545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6129563716585081283201453 2298586393719405481200545)
                      ·
                        rfl

theorem cell23_4476481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_4476481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476481 prefixEnd_4476481 := by exact prefixLift 4476481
  have htrace : WordTrace (prefixWord ++ tailWord_4476481) baseStart_4476481 baseEnd_4476481 := by
    simpa [prefixWord, tailWord_4476481, baseEnd_4476481] using wordTrace_append hprefix tailTrace_4476481
  have hstable : (prefixWord ++ tailWord_4476481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476481).length < 2 ^ (prefixWord ++ tailWord_4476481).sum := by decide
  have hdescent : baseEnd_4476481 < baseStart_4476481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476490 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_4476490 : Nat := 118140960795 + 4476490 * 2 ^ 59
def prefixEnd_4476490 : Nat := 4983230072969 + 3 ^ 40 * 4476490 * 2
def baseEnd_4476490 : Nat := 2298591015045295945988003

theorem tailTrace_4476490 : CollatzResearch.WordTrace tailWord_4476490 prefixEnd_4476490 2298591015045295945988003 := by
  unfold tailWord_4476490
  simp only [CollatzResearch.WordTrace]
  refine ⟨40817750888112182117568731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108847335701632485646849949 40817750888112182117568731)
  ·
    refine ⟨61226626332168273176353097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40817750888112182117568731 61226626332168273176353097)
    ·
      refine ⟨45919969749126204882264823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61226626332168273176353097 45919969749126204882264823)
      ·
        refine ⟨68879954623689307323397235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45919969749126204882264823 68879954623689307323397235)
        ·
          refine ⟨103319931935533960985095853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68879954623689307323397235 103319931935533960985095853)
          ·
            refine ⟨38744974475825235369410945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103319931935533960985095853 38744974475825235369410945)
            ·
              refine ⟨29058730856868926527058209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38744974475825235369410945 29058730856868926527058209)
              ·
                refine ⟨21794048142651694895293657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29058730856868926527058209 21794048142651694895293657)
                ·
                  refine ⟨16345536106988771171470243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21794048142651694895293657 16345536106988771171470243)
                  ·
                    refine ⟨24518304160483156757205365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16345536106988771171470243 24518304160483156757205365)
                    ·
                      refine ⟨2298591015045295945988003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24518304160483156757205365 2298591015045295945988003)
                      ·
                        rfl

theorem cell23_4476490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_4476490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476490 prefixEnd_4476490 := by exact prefixLift 4476490
  have htrace : WordTrace (prefixWord ++ tailWord_4476490) baseStart_4476490 baseEnd_4476490 := by
    simpa [prefixWord, tailWord_4476490, baseEnd_4476490] using wordTrace_append hprefix tailTrace_4476490
  have hstable : (prefixWord ++ tailWord_4476490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476490).length < 2 ^ (prefixWord ++ tailWord_4476490).sum := by decide
  have hdescent : baseEnd_4476490 < baseStart_4476490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476540 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_4476540 : Nat := 118140960795 + 4476540 * 2 ^ 59
def prefixEnd_4476540 : Nat := 4983230072969 + 3 ^ 40 * 4476540 * 2
def baseEnd_4476540 : Nat := 766205563026006916787591

theorem tailTrace_4476540 : CollatzResearch.WordTrace tailWord_4476540 prefixEnd_4476540 766205563026006916787591 := by
  unfold tailWord_4476540
  simp only [CollatzResearch.WordTrace]
  refine ⟨81636413601133793504797537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108848551468178391339730049 81636413601133793504797537)
  ·
    refine ⟨61227310200850345128598153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81636413601133793504797537 61227310200850345128598153)
    ·
      refine ⟨45920482650637758846448615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61227310200850345128598153 45920482650637758846448615)
      ·
        refine ⟨68880723975956638269672923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45920482650637758846448615 68880723975956638269672923)
        ·
          refine ⟨103321085963934957404509385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68880723975956638269672923 103321085963934957404509385)
          ·
            refine ⟨77490814472951218053382039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103321085963934957404509385 77490814472951218053382039)
            ·
              refine ⟨116236221709426827080073059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77490814472951218053382039 116236221709426827080073059)
              ·
                refine ⟨174354332564140240620109589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116236221709426827080073059 174354332564140240620109589)
                ·
                  refine ⟨8172859338944073779067637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 174354332564140240620109589 8172859338944073779067637)
                  ·
                    refine ⟨766205563026006916787591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8172859338944073779067637 766205563026006916787591)
                    ·
                      rfl

theorem cell23_4476540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_4476540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476540 prefixEnd_4476540 := by exact prefixLift 4476540
  have htrace : WordTrace (prefixWord ++ tailWord_4476540) baseStart_4476540 baseEnd_4476540 := by
    simpa [prefixWord, tailWord_4476540, baseEnd_4476540] using wordTrace_append hprefix tailTrace_4476540
  have hstable : (prefixWord ++ tailWord_4476540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476540).length < 2 ^ (prefixWord ++ tailWord_4476540).sum := by decide
  have hdescent : baseEnd_4476540 < baseStart_4476540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476560 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_4476560 : Nat := 118140960795 + 4476560 * 2 ^ 59
def prefixEnd_4476560 : Nat := 4983230072969 + 3 ^ 40 * 4476560 * 2
def baseEnd_4476560 : Nat := 2298626958691110672112681

theorem tailTrace_4476560 : CollatzResearch.WordTrace tailWord_4476560 prefixEnd_4476560 2298626958691110672112681 := by
  unfold tailWord_4476560
  simp only [CollatzResearch.WordTrace]
  refine ⟨81636778331097565212661567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108849037774796753616882089 81636778331097565212661567)
  ·
    refine ⟨122455167496646347818992351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81636778331097565212661567 122455167496646347818992351)
    ·
      refine ⟨183682751244969521728488527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122455167496646347818992351 183682751244969521728488527)
      ·
        refine ⟨275524126867454282592732791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183682751244969521728488527 275524126867454282592732791)
        ·
          refine ⟨413286190301181423889099187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275524126867454282592732791 413286190301181423889099187)
          ·
            refine ⟨619929285451772135833648781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413286190301181423889099187 619929285451772135833648781)
            ·
              refine ⟨232473482044414550937618293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 619929285451772135833648781 232473482044414550937618293)
              ·
                refine ⟨21794388941663864150401715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 232473482044414550937618293 21794388941663864150401715)
                ·
                  refine ⟨32691583412495796225602573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21794388941663864150401715 32691583412495796225602573)
                  ·
                    refine ⟨12259343779685923584600965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32691583412495796225602573 12259343779685923584600965)
                    ·
                      refine ⟨2298626958691110672112681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12259343779685923584600965 2298626958691110672112681)
                      ·
                        rfl

theorem cell23_4476560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_4476560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476560 prefixEnd_4476560 := by exact prefixLift 4476560
  have htrace : WordTrace (prefixWord ++ tailWord_4476560) baseStart_4476560 baseEnd_4476560 := by
    simpa [prefixWord, tailWord_4476560, baseEnd_4476560] using wordTrace_append hprefix tailTrace_4476560
  have hstable : (prefixWord ++ tailWord_4476560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476560).length < 2 ^ (prefixWord ++ tailWord_4476560).sum := by decide
  have hdescent : baseEnd_4476560 < baseStart_4476560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476574 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4476574 : Nat := 118140960795 + 4476574 * 2 ^ 59
def prefixEnd_4476574 : Nat := 4983230072969 + 3 ^ 40 * 4476574 * 2
def baseEnd_4476574 : Nat := 766211382473424539112539

theorem tailTrace_4476574 : CollatzResearch.WordTrace tailWord_4476574 prefixEnd_4476574 766211382473424539112539 := by
  unfold tailWord_4476574
  simp only [CollatzResearch.WordTrace]
  refine ⟨20409258410518051352041597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108849378189429607210888517 20409258410518051352041597)
  ·
    refine ⟨7653471903944269257015599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20409258410518051352041597 7653471903944269257015599)
    ·
      refine ⟨11480207855916403885523399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7653471903944269257015599 11480207855916403885523399)
      ·
        refine ⟨17220311783874605828285099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11480207855916403885523399 17220311783874605828285099)
        ·
          refine ⟨25830467675811908742427649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17220311783874605828285099 25830467675811908742427649)
          ·
            refine ⟨19372850756858931556820737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25830467675811908742427649 19372850756858931556820737)
            ·
              refine ⟨14529638067644198667615553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19372850756858931556820737 14529638067644198667615553)
              ·
                refine ⟨10897228550733149000711665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14529638067644198667615553 10897228550733149000711665)
                ·
                  refine ⟨8172921413049861750533749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10897228550733149000711665 8172921413049861750533749)
                  ·
                    refine ⟨766211382473424539112539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8172921413049861750533749 766211382473424539112539)
                    ·
                      rfl

theorem cell23_4476574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4476574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476574 prefixEnd_4476574 := by exact prefixLift 4476574
  have htrace : WordTrace (prefixWord ++ tailWord_4476574) baseStart_4476574 baseEnd_4476574 := by
    simpa [prefixWord, tailWord_4476574, baseEnd_4476574] using wordTrace_append hprefix tailTrace_4476574
  have hstable : (prefixWord ++ tailWord_4476574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476574).length < 2 ^ (prefixWord ++ tailWord_4476574).sum := by decide
  have hdescent : baseEnd_4476574 < baseStart_4476574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476604 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_4476604 : Nat := 118140960795 + 4476604 * 2 ^ 59
def prefixEnd_4476604 : Nat := 4983230072969 + 3 ^ 40 * 4476604 * 2
def baseEnd_4476604 : Nat := 766216517279969499987493

theorem tailTrace_4476604 : CollatzResearch.WordTrace tailWord_4476604 prefixEnd_4476604 766216517279969499987493 := by
  unfold tailWord_4476604
  simp only [CollatzResearch.WordTrace]
  refine ⟨81637580737017862969962433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108850107649357150626616577 81637580737017862969962433)
  ·
    refine ⟨61228185552763397227471825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81637580737017862969962433 61228185552763397227471825)
    ·
      refine ⟨45921139164572547920603869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61228185552763397227471825 45921139164572547920603869)
      ·
        refine ⟨17220427186714705470226451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45921139164572547920603869 17220427186714705470226451)
        ·
          refine ⟨25830640780072058205339677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17220427186714705470226451 25830640780072058205339677)
          ·
            refine ⟨9686490292527021827002379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25830640780072058205339677 9686490292527021827002379)
            ·
              refine ⟨14529735438790532740503569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9686490292527021827002379 14529735438790532740503569)
              ·
                refine ⟨10897301579092899555377677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14529735438790532740503569 10897301579092899555377677)
                ·
                  refine ⟨4086488092159837333266629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10897301579092899555377677 4086488092159837333266629)
                  ·
                    refine ⟨766216517279969499987493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4086488092159837333266629 766216517279969499987493)
                    ·
                      rfl

theorem cell23_4476604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_4476604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476604 prefixEnd_4476604 := by exact prefixLift 4476604
  have htrace : WordTrace (prefixWord ++ tailWord_4476604) baseStart_4476604 baseEnd_4476604 := by
    simpa [prefixWord, tailWord_4476604, baseEnd_4476604] using wordTrace_append hprefix tailTrace_4476604
  have hstable : (prefixWord ++ tailWord_4476604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476604).length < 2 ^ (prefixWord ++ tailWord_4476604).sum := by decide
  have hdescent : baseEnd_4476604 < baseStart_4476604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476634 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 6]
def baseStart_4476634 : Nat := 118140960795 + 4476634 * 2 ^ 59
def prefixEnd_4476634 : Nat := 4983230072969 + 3 ^ 40 * 4476634 * 2
def baseEnd_4476634 : Nat := 255407217362171486954149

theorem tailTrace_4476634 : CollatzResearch.WordTrace tailWord_4476634 prefixEnd_4476634 255407217362171486954149 := by
  unfold tailWord_4476634
  simp only [CollatzResearch.WordTrace]
  refine ⟨40819063915981760265879239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108850837109284694042344637 40819063915981760265879239)
  ·
    refine ⟨61228595873972640398818859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40819063915981760265879239 61228595873972640398818859)
    ·
      refine ⟨91842893810958960598228289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61228595873972640398818859 91842893810958960598228289)
      ·
        refine ⟨68882170358219220448671217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91842893810958960598228289 68882170358219220448671217)
        ·
          refine ⟨51661627768664415336503413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68882170358219220448671217 51661627768664415336503413)
          ·
            refine ⟨4843277603312288937797195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51661627768664415336503413 4843277603312288937797195)
            ·
              refine ⟨7264916404968433406695793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843277603312288937797195 7264916404968433406695793)
              ·
                refine ⟨5448687303726325055021845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7264916404968433406695793 5448687303726325055021845)
                ·
                  refine ⟨255407217362171486954149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5448687303726325055021845 255407217362171486954149)
                  ·
                    rfl

theorem cell23_4476634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_4476634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476634 prefixEnd_4476634 := by exact prefixLift 4476634
  have htrace : WordTrace (prefixWord ++ tailWord_4476634) baseStart_4476634 baseEnd_4476634 := by
    simpa [prefixWord, tailWord_4476634, baseEnd_4476634] using wordTrace_append hprefix tailTrace_4476634
  have hstable : (prefixWord ++ tailWord_4476634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476634).length < 2 ^ (prefixWord ++ tailWord_4476634).sum := by decide
  have hdescent : baseEnd_4476634 < baseStart_4476634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476654 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_4476654 : Nat := 118140960795 + 4476654 * 2 ^ 59
def prefixEnd_4476654 : Nat := 4983230072969 + 3 ^ 40 * 4476654 * 2
def baseEnd_4476654 : Nat := 2298675225872633304337249

theorem tailTrace_4476654 : CollatzResearch.WordTrace tailWord_4476654 prefixEnd_4476654 2298675225872633304337249 := by
  unfold tailWord_4476654
  simp only [CollatzResearch.WordTrace]
  refine ⟨20409623140481823059905627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108851323415903056319496677 20409623140481823059905627)
  ·
    refine ⟨30614434710722734589858441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20409623140481823059905627 30614434710722734589858441)
    ·
      refine ⟨22960826033042050942393831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30614434710722734589858441 22960826033042050942393831)
      ·
        refine ⟨34441239049563076413590747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22960826033042050942393831 34441239049563076413590747)
        ·
          refine ⟨51661858574344614620386121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34441239049563076413590747 51661858574344614620386121)
          ·
            refine ⟨38746393930758460965289591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51661858574344614620386121 38746393930758460965289591)
            ·
              refine ⟨58119590896137691447934387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38746393930758460965289591 58119590896137691447934387)
              ·
                refine ⟨87179386344206537171901581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58119590896137691447934387 87179386344206537171901581)
                ·
                  refine ⟨32692269879077451439463093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87179386344206537171901581 32692269879077451439463093)
                  ·
                    refine ⟨3064900301163511072449665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32692269879077451439463093 3064900301163511072449665)
                    ·
                      refine ⟨2298675225872633304337249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064900301163511072449665 2298675225872633304337249)
                      ·
                        rfl

theorem cell23_4476654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_4476654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476654 prefixEnd_4476654 := by exact prefixLift 4476654
  have htrace : WordTrace (prefixWord ++ tailWord_4476654) baseStart_4476654 baseEnd_4476654 := by
    simpa [prefixWord, tailWord_4476654, baseEnd_4476654] using wordTrace_append hprefix tailTrace_4476654
  have hstable : (prefixWord ++ tailWord_4476654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476654).length < 2 ^ (prefixWord ++ tailWord_4476654).sum := by decide
  have hdescent : baseEnd_4476654 < baseStart_4476654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476684 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_4476684 : Nat := 118140960795 + 4476684 * 2 ^ 59
def prefixEnd_4476684 : Nat := 4983230072969 + 3 ^ 40 * 4476684 * 2
def baseEnd_4476684 : Nat := 2298690630292268186962111

theorem tailTrace_4476684 : CollatzResearch.WordTrace tailWord_4476684 prefixEnd_4476684 2298690630292268186962111 := by
  unfold tailWord_4476684
  simp only [CollatzResearch.WordTrace]
  refine ⟨81639039656872949801418553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108852052875830599735224737 81639039656872949801418553)
  ·
    refine ⟨61229279742654712351063915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81639039656872949801418553 61229279742654712351063915)
    ·
      refine ⟨91843919613982068526595873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61229279742654712351063915 91843919613982068526595873)
      ·
        refine ⟨68882939710486551394946905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91843919613982068526595873 68882939710486551394946905)
        ·
          refine ⟨51662204782864913546210179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68882939710486551394946905 51662204782864913546210179)
          ·
            refine ⟨77493307174297370319315269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51662204782864913546210179 77493307174297370319315269)
            ·
              refine ⟨14529995095180756934871613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77493307174297370319315269 14529995095180756934871613)
              ·
                refine ⟨5448748160692783850576855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14529995095180756934871613 5448748160692783850576855)
                ·
                  refine ⟨8173122241039175775865283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448748160692783850576855 8173122241039175775865283)
                  ·
                    refine ⟨12259683361558763663797925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8173122241039175775865283 12259683361558763663797925)
                    ·
                      refine ⟨2298690630292268186962111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12259683361558763663797925 2298690630292268186962111)
                      ·
                        rfl

theorem cell23_4476684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_4476684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476684 prefixEnd_4476684 := by exact prefixLift 4476684
  have htrace : WordTrace (prefixWord ++ tailWord_4476684) baseStart_4476684 baseEnd_4476684 := by
    simpa [prefixWord, tailWord_4476684, baseEnd_4476684] using wordTrace_append hprefix tailTrace_4476684
  have hstable : (prefixWord ++ tailWord_4476684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476684).length < 2 ^ (prefixWord ++ tailWord_4476684).sum := by decide
  have hdescent : baseEnd_4476684 < baseStart_4476684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476695 : List Nat := [1, 1, 3, 4, 2, 2, 3, 2, 1, 1, 3]
def baseStart_4476695 : Nat := 118140960795 + 4476695 * 2 ^ 59
def prefixEnd_4476695 : Nat := 4983230072969 + 3 ^ 40 * 4476695 * 2
def baseEnd_4476695 : Nat := 2298696278579467643924561

theorem tailTrace_4476695 : CollatzResearch.WordTrace tailWord_4476695 prefixEnd_4476695 2298696278579467643924561 := by
  unfold tailWord_4476695
  simp only [CollatzResearch.WordTrace]
  refine ⟨163278480516706048481487539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108852320344470698987658359 163278480516706048481487539)
  ·
    refine ⟨244917720775059072722231309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163278480516706048481487539 244917720775059072722231309)
    ·
      refine ⟨91844145290647152270836741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244917720775059072722231309 91844145290647152270836741)
      ·
        refine ⟨17220777241996341050781889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91844145290647152270836741 17220777241996341050781889)
        ·
          refine ⟨12915582931497255788086417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17220777241996341050781889 12915582931497255788086417)
          ·
            refine ⟨9686687198622941841064813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12915582931497255788086417 9686687198622941841064813)
            ·
              refine ⟨3632507699483603190399305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9686687198622941841064813 3632507699483603190399305)
              ·
                refine ⟨2724380774612702392799479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632507699483603190399305 2724380774612702392799479)
                ·
                  refine ⟨4086571161919053589199219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724380774612702392799479 4086571161919053589199219)
                  ·
                    refine ⟨6129856742878580383798829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4086571161919053589199219 6129856742878580383798829)
                    ·
                      refine ⟨2298696278579467643924561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6129856742878580383798829 2298696278579467643924561)
                      ·
                        rfl

theorem cell23_4476695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_4476695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476695 prefixEnd_4476695 := by exact prefixLift 4476695
  have htrace : WordTrace (prefixWord ++ tailWord_4476695) baseStart_4476695 baseEnd_4476695 := by
    simpa [prefixWord, tailWord_4476695, baseEnd_4476695] using wordTrace_append hprefix tailTrace_4476695
  have hstable : (prefixWord ++ tailWord_4476695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476695).length < 2 ^ (prefixWord ++ tailWord_4476695).sum := by decide
  have hdescent : baseEnd_4476695 < baseStart_4476695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476702 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_4476702 : Nat := 118140960795 + 4476702 * 2 ^ 59
def prefixEnd_4476702 : Nat := 4983230072969 + 3 ^ 40 * 4476702 * 2
def baseEnd_4476702 : Nat := 255411096993783235170781

theorem tailTrace_4476702 : CollatzResearch.WordTrace tailWord_4476702 prefixEnd_4476702 255411096993783235170781 := by
  unfold tailWord_4476702
  simp only [CollatzResearch.WordTrace]
  refine ⟨20409841978460086084624045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108852490551787125784661573 20409841978460086084624045)
  ·
    refine ⟨7653690741922532281734017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20409841978460086084624045 7653690741922532281734017)
    ·
      refine ⟨5740268056441899211300513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7653690741922532281734017 5740268056441899211300513)
      ·
        refine ⟨4305201042331424408475385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5740268056441899211300513 4305201042331424408475385)
        ·
          refine ⟨3228900781748568306356539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4305201042331424408475385 3228900781748568306356539)
          ·
            refine ⟨4843351172622852459534809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228900781748568306356539 4843351172622852459534809)
            ·
              refine ⟨3632513379467139344651107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4843351172622852459534809 3632513379467139344651107)
              ·
                refine ⟨5448770069200709016976661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632513379467139344651107 5448770069200709016976661)
                ·
                  refine ⟨255411096993783235170781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5448770069200709016976661 255411096993783235170781)
                  ·
                    rfl

theorem cell23_4476702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_4476702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476702 prefixEnd_4476702 := by exact prefixLift 4476702
  have htrace : WordTrace (prefixWord ++ tailWord_4476702) baseStart_4476702 baseEnd_4476702 := by
    simpa [prefixWord, tailWord_4476702, baseEnd_4476702] using wordTrace_append hprefix tailTrace_4476702
  have hstable : (prefixWord ++ tailWord_4476702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476702).length < 2 ^ (prefixWord ++ tailWord_4476702).sum := by decide
  have hdescent : baseEnd_4476702 < baseStart_4476702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476704 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4476704 : Nat := 118140960795 + 4476704 * 2 ^ 59
def prefixEnd_4476704 : Nat := 4983230072969 + 3 ^ 40 * 4476704 * 2
def baseEnd_4476704 : Nat := 2298700899905358108712019

theorem tailTrace_4476704 : CollatzResearch.WordTrace tailWord_4476704 prefixEnd_4476704 2298700899905358108712019 := by
  unfold tailWord_4476704
  simp only [CollatzResearch.WordTrace]
  refine ⟨81639404386836721509282583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108852539182448962012376777 81639404386836721509282583)
  ·
    refine ⟨122459106580255082263923875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81639404386836721509282583 122459106580255082263923875)
    ·
      refine ⟨183688659870382623395885813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122459106580255082263923875 183688659870382623395885813)
      ·
        refine ⟨17220811862848370943364295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183688659870382623395885813 17220811862848370943364295)
        ·
          refine ⟨25831217794272556415046443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17220811862848370943364295 25831217794272556415046443)
          ·
            refine ⟨38746826691408834622569665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25831217794272556415046443 38746826691408834622569665)
            ·
              refine ⟨29060120018556625966927249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38746826691408834622569665 29060120018556625966927249)
              ·
                refine ⟨21795090013917469475195437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29060120018556625966927249 21795090013917469475195437)
                ·
                  refine ⟨8173158755219051053198289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21795090013917469475195437 8173158755219051053198289)
                  ·
                    refine ⟨6129869066414288289898717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8173158755219051053198289 6129869066414288289898717)
                    ·
                      refine ⟨2298700899905358108712019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6129869066414288289898717 2298700899905358108712019)
                      ·
                        rfl

theorem cell23_4476704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4476704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476704 prefixEnd_4476704 := by exact prefixLift 4476704
  have htrace : WordTrace (prefixWord ++ tailWord_4476704) baseStart_4476704 baseEnd_4476704 := by
    simpa [prefixWord, tailWord_4476704, baseEnd_4476704] using wordTrace_append hprefix tailTrace_4476704
  have hstable : (prefixWord ++ tailWord_4476704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476704).length < 2 ^ (prefixWord ++ tailWord_4476704).sum := by decide
  have hdescent : baseEnd_4476704 < baseStart_4476704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476721 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_4476721 : Nat := 118140960795 + 4476721 * 2 ^ 59
def prefixEnd_4476721 : Nat := 4983230072969 + 3 ^ 40 * 4476721 * 2
def baseEnd_4476721 : Nat := 2298709629076484542199441

theorem tailTrace_4476721 : CollatzResearch.WordTrace tailWord_4476721 prefixEnd_4476721 2298709629076484542199441 := by
  unfold tailWord_4476721
  simp only [CollatzResearch.WordTrace]
  refine ⟨163279428814611854921934017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108852952543074569947956011 163279428814611854921934017)
  ·
    refine ⟨122459571610958891191450513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163279428814611854921934017 122459571610958891191450513)
    ·
      refine ⟨91844678708219168393587885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122459571610958891191450513 91844678708219168393587885)
      ·
        refine ⟨34441754515582188147595457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91844678708219168393587885 34441754515582188147595457)
        ·
          refine ⟨25831315886686641110696593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34441754515582188147595457 25831315886686641110696593)
          ·
            refine ⟨19373486915014980833022445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25831315886686641110696593 19373486915014980833022445)
            ·
              refine ⟨7265057593130617812383417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19373486915014980833022445 7265057593130617812383417)
              ·
                refine ⟨5448793194847963359287563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7265057593130617812383417 5448793194847963359287563)
                ·
                  refine ⟨8173189792271945038931345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448793194847963359287563 8173189792271945038931345)
                  ·
                    refine ⟨6129892344203958779198509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8173189792271945038931345 6129892344203958779198509)
                    ·
                      refine ⟨2298709629076484542199441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6129892344203958779198509 2298709629076484542199441)
                      ·
                        rfl

theorem cell23_4476721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_4476721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476721 prefixEnd_4476721 := by exact prefixLift 4476721
  have htrace : WordTrace (prefixWord ++ tailWord_4476721) baseStart_4476721 baseEnd_4476721 := by
    simpa [prefixWord, tailWord_4476721, baseEnd_4476721] using wordTrace_append hprefix tailTrace_4476721
  have hstable : (prefixWord ++ tailWord_4476721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476721).length < 2 ^ (prefixWord ++ tailWord_4476721).sum := by decide
  have hdescent : baseEnd_4476721 < baseStart_4476721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476724 : List Nat := [2, 5, 1, 1, 2, 1, 2, 9]
def baseStart_4476724 : Nat := 118140960795 + 4476724 * 2 ^ 59
def prefixEnd_4476724 : Nat := 4983230072969 + 3 ^ 40 * 4476724 * 2
def baseEnd_4476724 : Nat := 85137450722905482609701

theorem tailTrace_4476724 : CollatzResearch.WordTrace tailWord_4476724 prefixEnd_4476724 85137450722905482609701 := by
  unfold tailWord_4476724
  simp only [CollatzResearch.WordTrace]
  refine ⟨81639769116800493217146613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108853025489067324289528817 81639769116800493217146613)
  ·
    refine ⟨7653728354700046239107495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81639769116800493217146613 7653728354700046239107495)
    ·
      refine ⟨11480592532050069358661243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7653728354700046239107495 11480592532050069358661243)
      ·
        refine ⟨17220888798075104037991865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11480592532050069358661243 17220888798075104037991865)
        ·
          refine ⟨12915666598556328028493899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17220888798075104037991865 12915666598556328028493899)
          ·
            refine ⟨19373499897834492042740849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12915666598556328028493899 19373499897834492042740849)
            ·
              refine ⟨14530124923375869032055637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19373499897834492042740849 14530124923375869032055637)
              ·
                refine ⟨85137450722905482609701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14530124923375869032055637 85137450722905482609701)
                ·
                  rfl

theorem cell23_4476724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 9].length) (baseStart_4476724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476724 prefixEnd_4476724 := by exact prefixLift 4476724
  have htrace : WordTrace (prefixWord ++ tailWord_4476724) baseStart_4476724 baseEnd_4476724 := by
    simpa [prefixWord, tailWord_4476724, baseEnd_4476724] using wordTrace_append hprefix tailTrace_4476724
  have hstable : (prefixWord ++ tailWord_4476724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476724).length < 2 ^ (prefixWord ++ tailWord_4476724).sum := by decide
  have hdescent : baseEnd_4476724 < baseStart_4476724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476767 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 1, 8]
def baseStart_4476767 : Nat := 118140960795 + 4476767 * 2 ^ 59
def prefixEnd_4476767 : Nat := 4983230072969 + 3 ^ 40 * 4476767 * 2
def baseEnd_4476767 : Nat := 766244416395530454074743

theorem tailTrace_4476767 : CollatzResearch.WordTrace tailWord_4476767 prefixEnd_4476767 766244416395530454074743 := by
  unfold tailWord_4476767
  simp only [CollatzResearch.WordTrace]
  refine ⟨163281106572445204778108555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108854071048296803185405703 163281106572445204778108555)
  ·
    refine ⟨244921659858667807167162833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163281106572445204778108555 244921659858667807167162833)
    ·
      refine ⟨183691244894000855375372125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244921659858667807167162833 183691244894000855375372125)
      ·
        refine ⟨68884216835250320765764547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183691244894000855375372125 68884216835250320765764547)
        ·
          refine ⟨103326325252875481148646821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68884216835250320765764547 103326325252875481148646821)
          ·
            refine ⟨19373685984914152715371279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103326325252875481148646821 19373685984914152715371279)
            ·
              refine ⟨29060528977371229073056919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19373685984914152715371279 29060528977371229073056919)
              ·
                refine ⟨43590793466056843609585379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29060528977371229073056919 43590793466056843609585379)
                ·
                  refine ⟨65386190199085265414378069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43590793466056843609585379 65386190199085265414378069)
                  ·
                    refine ⟨766244416395530454074743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65386190199085265414378069 766244416395530454074743)
                    ·
                      rfl

theorem cell23_4476767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_4476767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476767 prefixEnd_4476767 := by exact prefixLift 4476767
  have htrace : WordTrace (prefixWord ++ tailWord_4476767) baseStart_4476767 baseEnd_4476767 := by
    simpa [prefixWord, tailWord_4476767, baseEnd_4476767] using wordTrace_append hprefix tailTrace_4476767
  have hstable : (prefixWord ++ tailWord_4476767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476767).length < 2 ^ (prefixWord ++ tailWord_4476767).sum := by decide
  have hdescent : baseEnd_4476767 < baseStart_4476767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476777 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_4476777 : Nat := 118140960795 + 4476777 * 2 ^ 59
def prefixEnd_4476777 : Nat := 4983230072969 + 3 ^ 40 * 4476777 * 2
def baseEnd_4476777 : Nat := 2298738383993136323099183

theorem tailTrace_4476777 : CollatzResearch.WordTrace tailWord_4476777 prefixEnd_4476777 2298738383993136323099183 := by
  unfold tailWord_4476777
  simp only [CollatzResearch.WordTrace]
  refine ⟨163281471302408976485972585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108854314201605984323981723 163281471302408976485972585)
  ·
    refine ⟨122461103476806732364479439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163281471302408976485972585 122461103476806732364479439)
    ·
      refine ⟨183691655215210098546719159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122461103476806732364479439 183691655215210098546719159)
      ·
        refine ⟨275537482822815147820078739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183691655215210098546719159 275537482822815147820078739)
        ·
          refine ⟨413306224234222721730118109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275537482822815147820078739 413306224234222721730118109)
          ·
            refine ⟨154989834087833520648794291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 413306224234222721730118109 154989834087833520648794291)
            ·
              refine ⟨232484751131750280973191437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154989834087833520648794291 232484751131750280973191437)
              ·
                refine ⟨87181781674406355364946789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232484751131750280973191437 87181781674406355364946789)
                ·
                  refine ⟨16346584063951191630927523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87181781674406355364946789 16346584063951191630927523)
                  ·
                    refine ⟨24519876095926787446391285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16346584063951191630927523 24519876095926787446391285)
                    ·
                      refine ⟨2298738383993136323099183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24519876095926787446391285 2298738383993136323099183)
                      ·
                        rfl

theorem cell23_4476777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_4476777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476777 prefixEnd_4476777 := by exact prefixLift 4476777
  have htrace : WordTrace (prefixWord ++ tailWord_4476777) baseStart_4476777 baseEnd_4476777 := by
    simpa [prefixWord, tailWord_4476777, baseEnd_4476777] using wordTrace_append hprefix tailTrace_4476777
  have hstable : (prefixWord ++ tailWord_4476777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476777).length < 2 ^ (prefixWord ++ tailWord_4476777).sum := by decide
  have hdescent : baseEnd_4476777 < baseStart_4476777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476787 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 4]
def baseStart_4476787 : Nat := 118140960795 + 4476787 * 2 ^ 59
def prefixEnd_4476787 : Nat := 4983230072969 + 3 ^ 40 * 4476787 * 2
def baseEnd_4476787 : Nat := 2298743518799681283974137

theorem tailTrace_4476787 : CollatzResearch.WordTrace tailWord_4476787 prefixEnd_4476787 2298743518799681283974137 := by
  unfold tailWord_4476787
  simp only [CollatzResearch.WordTrace]
  refine ⟨163281836032372748193836615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108854557354915165462557743 163281836032372748193836615)
  ·
    refine ⟨244922754048559122290754923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163281836032372748193836615 244922754048559122290754923)
    ·
      refine ⟨367384131072838683436132385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244922754048559122290754923 367384131072838683436132385)
      ·
        refine ⟨275538098304629012577099289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367384131072838683436132385 275538098304629012577099289)
        ·
          refine ⟨206653573728471759432824467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275538098304629012577099289 206653573728471759432824467)
          ·
            refine ⟨309980360592707639149236701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206653573728471759432824467 309980360592707639149236701)
            ·
              refine ⟨116242635222265364680963763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309980360592707639149236701 116242635222265364680963763)
              ·
                refine ⟨174363952833398047021445645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116242635222265364680963763 174363952833398047021445645)
                ·
                  refine ⟨65386482312524267633042117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174363952833398047021445645 65386482312524267633042117)
                  ·
                    refine ⟨12259965433598300181195397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65386482312524267633042117 12259965433598300181195397)
                    ·
                      refine ⟨2298743518799681283974137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12259965433598300181195397 2298743518799681283974137)
                      ·
                        rfl

theorem cell23_4476787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_4476787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476787 prefixEnd_4476787 := by exact prefixLift 4476787
  have htrace : WordTrace (prefixWord ++ tailWord_4476787) baseStart_4476787 baseEnd_4476787 := by
    simpa [prefixWord, tailWord_4476787, baseEnd_4476787] using wordTrace_append hprefix tailTrace_4476787
  have hstable : (prefixWord ++ tailWord_4476787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476787).length < 2 ^ (prefixWord ++ tailWord_4476787).sum := by decide
  have hdescent : baseEnd_4476787 < baseStart_4476787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476797 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 11]
def baseStart_4476797 : Nat := 118140960795 + 4476797 * 2 ^ 59
def prefixEnd_4476797 : Nat := 4983230072969 + 3 ^ 40 * 4476797 * 2
def baseEnd_4476797 : Nat := 255416517067358471649899

theorem tailTrace_4476797 : CollatzResearch.WordTrace tailWord_4476797 prefixEnd_4476797 255416517067358471649899 := by
  unfold tailWord_4476797
  simp only [CollatzResearch.WordTrace]
  refine ⟨163282200762336519901700645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108854800508224346601133763 163282200762336519901700645)
  ·
    refine ⟨30615412642938097481568871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163282200762336519901700645 30615412642938097481568871)
    ·
      refine ⟨45923118964407146222353307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30615412642938097481568871 45923118964407146222353307)
      ·
        refine ⟨68884678446610719333529961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45923118964407146222353307 68884678446610719333529961)
        ·
          refine ⟨51663508834958039500147471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68884678446610719333529961 51663508834958039500147471)
          ·
            refine ⟨77495263252437059250221207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51663508834958039500147471 77495263252437059250221207)
            ·
              refine ⟨116242894878655588875331811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77495263252437059250221207 116242894878655588875331811)
              ·
                refine ⟨174364342317983383312997717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116242894878655588875331811 174364342317983383312997717)
                ·
                  refine ⟨255416517067358471649899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 174364342317983383312997717 255416517067358471649899)
                  ·
                    rfl

theorem cell23_4476797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_4476797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476797 prefixEnd_4476797 := by exact prefixLift 4476797
  have htrace : WordTrace (prefixWord ++ tailWord_4476797) baseStart_4476797 baseEnd_4476797 := by
    simpa [prefixWord, tailWord_4476797, baseEnd_4476797] using wordTrace_append hprefix tailTrace_4476797
  have hstable : (prefixWord ++ tailWord_4476797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476797).length < 2 ^ (prefixWord ++ tailWord_4476797).sum := by decide
  have hdescent : baseEnd_4476797 < baseStart_4476797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476804 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_4476804 : Nat := 118140960795 + 4476804 * 2 ^ 59
def prefixEnd_4476804 : Nat := 4983230072969 + 3 ^ 40 * 4476804 * 2
def baseEnd_4476804 : Nat := 2298752247970807717461559

theorem tailTrace_4476804 : CollatzResearch.WordTrace tailWord_4476804 prefixEnd_4476804 2298752247970807717461559 := by
  unfold tailWord_4476804
  simp only [CollatzResearch.WordTrace]
  refine ⟨81641228036655580048602733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108854970715540773398136977 81641228036655580048602733)
  ·
    refine ⟨30615460513745842518226025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81641228036655580048602733 30615460513745842518226025)
    ·
      refine ⟨22961595385309381888669519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30615460513745842518226025 22961595385309381888669519)
      ·
        refine ⟨34442393077964072833004279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22961595385309381888669519 34442393077964072833004279)
        ·
          refine ⟨51663589616946109249506419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34442393077964072833004279 51663589616946109249506419)
          ·
            refine ⟨77495384425419163874259629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51663589616946109249506419 77495384425419163874259629)
            ·
              refine ⟨29060769159532186452847361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77495384425419163874259629 29060769159532186452847361)
              ·
                refine ⟨21795576869649139839635521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29060769159532186452847361 21795576869649139839635521)
                ·
                  refine ⟨16346682652236854879726641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21795576869649139839635521 16346682652236854879726641)
                  ·
                    refine ⟨12260011989177641159794981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16346682652236854879726641 12260011989177641159794981)
                    ·
                      refine ⟨2298752247970807717461559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12260011989177641159794981 2298752247970807717461559)
                      ·
                        rfl

theorem cell23_4476804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_4476804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476804 prefixEnd_4476804 := by exact prefixLift 4476804
  have htrace : WordTrace (prefixWord ++ tailWord_4476804) baseStart_4476804 baseEnd_4476804 := by
    simpa [prefixWord, tailWord_4476804, baseEnd_4476804] using wordTrace_append hprefix tailTrace_4476804
  have hstable : (prefixWord ++ tailWord_4476804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476804).length < 2 ^ (prefixWord ++ tailWord_4476804).sum := by decide
  have hdescent : baseEnd_4476804 < baseStart_4476804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476861 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_4476861 : Nat := 118140960795 + 4476861 * 2 ^ 59
def prefixEnd_4476861 : Nat := 4983230072969 + 3 ^ 40 * 4476861 * 2
def baseEnd_4476861 : Nat := 766260505456037998149599

theorem tailTrace_4476861 : CollatzResearch.WordTrace tailWord_4476861 prefixEnd_4476861 766260505456037998149599 := by
  unfold tailWord_4476861
  simp only [CollatzResearch.WordTrace]
  refine ⟨163284535034104658832030437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108856356689403105888020291 163284535034104658832030437)
  ·
    refine ⟨30615850318894623531005707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163284535034104658832030437 30615850318894623531005707)
    ·
      refine ⟨45923775478341935296508561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30615850318894623531005707 45923775478341935296508561)
      ·
        refine ⟨34442831608756451472381421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45923775478341935296508561 34442831608756451472381421)
        ·
          refine ⟨12916061853283669302143033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34442831608756451472381421 12916061853283669302143033)
          ·
            refine ⟨9687046389962751976607275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12916061853283669302143033 9687046389962751976607275)
            ·
              refine ⟨14530569584944127964910913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9687046389962751976607275 14530569584944127964910913)
              ·
                refine ⟨10897927188708095973683185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14530569584944127964910913 10897927188708095973683185)
                ·
                  refine ⟨8173445391531071980262389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10897927188708095973683185 8173445391531071980262389)
                  ·
                    refine ⟨766260505456037998149599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8173445391531071980262389 766260505456037998149599)
                    ·
                      rfl

theorem cell23_4476861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_4476861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476861 prefixEnd_4476861 := by exact prefixLift 4476861
  have htrace : WordTrace (prefixWord ++ tailWord_4476861) baseStart_4476861 baseEnd_4476861 := by
    simpa [prefixWord, tailWord_4476861, baseEnd_4476861] using wordTrace_append hprefix tailTrace_4476861
  have hstable : (prefixWord ++ tailWord_4476861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476861).length < 2 ^ (prefixWord ++ tailWord_4476861).sum := by decide
  have hdescent : baseEnd_4476861 < baseStart_4476861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476921 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 6]
def baseStart_4476921 : Nat := 118140960795 + 4476921 * 2 ^ 59
def prefixEnd_4476921 : Nat := 4983230072969 + 3 ^ 40 * 4476921 * 2
def baseEnd_4476921 : Nat := 255423591689709306633169

theorem tailTrace_4476921 : CollatzResearch.WordTrace tailWord_4476921 prefixEnd_4476921 255423591689709306633169 := by
  unfold tailWord_4476921
  simp only [CollatzResearch.WordTrace]
  refine ⟨163286723413887289079214617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108857815609258192719476411 163286723413887289079214617)
  ·
    refine ⟨122465042560415466809410963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163286723413887289079214617 122465042560415466809410963)
    ·
      refine ⟨183697563840623200214116445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122465042560415466809410963 183697563840623200214116445)
      ·
        refine ⟨68886586440233700080293667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183697563840623200214116445 68886586440233700080293667)
        ·
          refine ⟨103329879660350550120440501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68886586440233700080293667 103329879660350550120440501)
          ·
            refine ⟨9687176218157864073791297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103329879660350550120440501 9687176218157864073791297)
            ·
              refine ⟨7265382163618398055343473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9687176218157864073791297 7265382163618398055343473)
              ·
                refine ⟨5449036622713798541507605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7265382163618398055343473 5449036622713798541507605)
                ·
                  refine ⟨255423591689709306633169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5449036622713798541507605 255423591689709306633169)
                  ·
                    rfl

theorem cell23_4476921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 6].length) (baseStart_4476921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476921 prefixEnd_4476921 := by exact prefixLift 4476921
  have htrace : WordTrace (prefixWord ++ tailWord_4476921) baseStart_4476921 baseEnd_4476921 := by
    simpa [prefixWord, tailWord_4476921, baseEnd_4476921] using wordTrace_append hprefix tailTrace_4476921
  have hstable : (prefixWord ++ tailWord_4476921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476921).length < 2 ^ (prefixWord ++ tailWord_4476921).sum := by decide
  have hdescent : baseEnd_4476921 < baseStart_4476921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476924 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_4476924 : Nat := 118140960795 + 4476924 * 2 ^ 59
def prefixEnd_4476924 : Nat := 4983230072969 + 3 ^ 40 * 4476924 * 2
def baseEnd_4476924 : Nat := 2298813865649347247961007

theorem tailTrace_4476924 : CollatzResearch.WordTrace tailWord_4476924 prefixEnd_4476924 2298813865649347247961007 := by
  unfold tailWord_4476924
  simp only [CollatzResearch.WordTrace]
  refine ⟨81643416416438210295786913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108857888555250947061049217 81643416416438210295786913)
  ·
    refine ⟨61232562312328657721840185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81643416416438210295786913 61232562312328657721840185)
    ·
      refine ⟨45924421734246493291380139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61232562312328657721840185 45924421734246493291380139)
      ·
        refine ⟨68886632601369739937070209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45924421734246493291380139 68886632601369739937070209)
        ·
          refine ⟨51664974451027304952802657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68886632601369739937070209 51664974451027304952802657)
          ·
            refine ⟨38748730838270478714601993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51664974451027304952802657 38748730838270478714601993)
            ·
              refine ⟨29061548128702859035951495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38748730838270478714601993 29061548128702859035951495)
              ·
                refine ⟨43592322193054288553927243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29061548128702859035951495 43592322193054288553927243)
                ·
                  refine ⟨65388483289581432830890865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43592322193054288553927243 65388483289581432830890865)
                  ·
                    refine ⟨49041362467186074623168149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65388483289581432830890865 49041362467186074623168149)
                    ·
                      refine ⟨2298813865649347247961007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49041362467186074623168149 2298813865649347247961007)
                      ·
                        rfl

theorem cell23_4476924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_4476924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476924 prefixEnd_4476924 := by exact prefixLift 4476924
  have htrace : WordTrace (prefixWord ++ tailWord_4476924) baseStart_4476924 baseEnd_4476924 := by
    simpa [prefixWord, tailWord_4476924, baseEnd_4476924] using wordTrace_append hprefix tailTrace_4476924
  have hstable : (prefixWord ++ tailWord_4476924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476924).length < 2 ^ (prefixWord ++ tailWord_4476924).sum := by decide
  have hdescent : baseEnd_4476924 < baseStart_4476924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476925 : List Nat := [1, 4, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_4476925 : Nat := 118140960795 + 4476925 * 2 ^ 59
def prefixEnd_4476925 : Nat := 4983230072969 + 3 ^ 40 * 4476925 * 2
def baseEnd_4476925 : Nat := 766271459710000581349501

theorem tailTrace_4476925 : CollatzResearch.WordTrace tailWord_4476925 prefixEnd_4476925 766271459710000581349501 := by
  unfold tailWord_4476925
  simp only [CollatzResearch.WordTrace]
  refine ⟨163286869305872797762360229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108857912870581865174906819 163286869305872797762360229)
  ·
    refine ⟨30616287994851149580442543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163286869305872797762360229 30616287994851149580442543)
    ·
      refine ⟨45924431992276724370663815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30616287994851149580442543 45924431992276724370663815)
      ·
        refine ⟨68886647988415086555995723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45924431992276724370663815 68886647988415086555995723)
        ·
          refine ⟨103329971982622629833993585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68886647988415086555995723 103329971982622629833993585)
          ·
            refine ⟨77497478986966972375495189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103329971982622629833993585 77497478986966972375495189)
            ·
              refine ⟨3632694327514076830101337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77497478986966972375495189 3632694327514076830101337)
              ·
                refine ⟨2724520745635557622576003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632694327514076830101337 2724520745635557622576003)
                ·
                  refine ⟨4086781118453336433864005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724520745635557622576003 4086781118453336433864005)
                  ·
                    refine ⟨766271459710000581349501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4086781118453336433864005 766271459710000581349501)
                    ·
                      rfl

theorem cell23_4476925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_4476925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476925 prefixEnd_4476925 := by exact prefixLift 4476925
  have htrace : WordTrace (prefixWord ++ tailWord_4476925) baseStart_4476925 baseEnd_4476925 := by
    simpa [prefixWord, tailWord_4476925, baseEnd_4476925] using wordTrace_append hprefix tailTrace_4476925
  have hstable : (prefixWord ++ tailWord_4476925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476925).length < 2 ^ (prefixWord ++ tailWord_4476925).sum := by decide
  have hdescent : baseEnd_4476925 < baseStart_4476925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476931 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 3]
def baseStart_4476931 : Nat := 118140960795 + 4476931 * 2 ^ 59
def prefixEnd_4476931 : Nat := 4983230072969 + 3 ^ 40 * 4476931 * 2
def baseEnd_4476931 : Nat := 2298817460013928720573475

theorem tailTrace_4476931 : CollatzResearch.WordTrace tailWord_4476931 prefixEnd_4476931 2298817460013928720573475 := by
  unfold tailWord_4476931
  simp only [CollatzResearch.WordTrace]
  refine ⟨163287088143851060787078647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108858058762567373858052431 163287088143851060787078647)
  ·
    refine ⟨244930632215776591180617971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163287088143851060787078647 244930632215776591180617971)
    ·
      refine ⟨367395948323664886770926957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244930632215776591180617971 367395948323664886770926957)
      ·
        refine ⟨137773480621374332539097609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367395948323664886770926957 137773480621374332539097609)
        ·
          refine ⟨103330110466030749404323207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137773480621374332539097609 103330110466030749404323207)
          ·
            refine ⟨154995165699046124106484811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103330110466030749404323207 154995165699046124106484811)
            ·
              refine ⟨232492748548569186159727217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154995165699046124106484811 232492748548569186159727217)
              ·
                refine ⟨174369561411426889619795413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232492748548569186159727217 174369561411426889619795413)
                ·
                  refine ⟨4086786595580317725463955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 174369561411426889619795413 4086786595580317725463955)
                  ·
                    refine ⟨6130179893370476588195933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4086786595580317725463955 6130179893370476588195933)
                    ·
                      refine ⟨2298817460013928720573475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6130179893370476588195933 2298817460013928720573475)
                      ·
                        rfl

theorem cell23_4476931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_4476931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476931 prefixEnd_4476931 := by exact prefixLift 4476931
  have htrace : WordTrace (prefixWord ++ tailWord_4476931) baseStart_4476931 baseEnd_4476931 := by
    simpa [prefixWord, tailWord_4476931, baseEnd_4476931] using wordTrace_append hprefix tailTrace_4476931
  have hstable : (prefixWord ++ tailWord_4476931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476931).length < 2 ^ (prefixWord ++ tailWord_4476931).sum := by decide
  have hdescent : baseEnd_4476931 < baseStart_4476931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476965 : List Nat := [1, 3, 1, 2, 2, 3, 1, 5, 1, 1, 3]
def baseStart_4476965 : Nat := 118140960795 + 4476965 * 2 ^ 59
def prefixEnd_4476965 : Nat := 4983230072969 + 3 ^ 40 * 4476965 * 2
def baseEnd_4476965 : Nat := 2298834918356181587548319

theorem tailTrace_4476965 : CollatzResearch.WordTrace tailWord_4476965 prefixEnd_4476965 2298834918356181587548319 := by
  unfold tailWord_4476965
  simp only [CollatzResearch.WordTrace]
  refine ⟨163288328225727884593816349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108858885483818589729210899 163288328225727884593816349)
  ·
    refine ⟨61233123084647956722681131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163288328225727884593816349 61233123084647956722681131)
    ·
      refine ⟨91849684626971935084021697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61233123084647956722681131 91849684626971935084021697)
      ·
        refine ⟨68887263470228951313016273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91849684626971935084021697 68887263470228951313016273)
        ·
          refine ⟨51665447602671713484762205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68887263470228951313016273 51665447602671713484762205)
          ·
            refine ⟨19374542851001892556785827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51665447602671713484762205 19374542851001892556785827)
            ·
              refine ⟨29061814276502838835178741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19374542851001892556785827 29061814276502838835178741)
              ·
                refine ⟨2724545088422141140798007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29061814276502838835178741 2724545088422141140798007)
                ·
                  refine ⟨4086817632633211711197011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724545088422141140798007 4086817632633211711197011)
                  ·
                    refine ⟨6130226448949817566795517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4086817632633211711197011 6130226448949817566795517)
                    ·
                      refine ⟨2298834918356181587548319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6130226448949817566795517 2298834918356181587548319)
                      ·
                        rfl

theorem cell23_4476965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_4476965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476965 prefixEnd_4476965 := by exact prefixLift 4476965
  have htrace : WordTrace (prefixWord ++ tailWord_4476965) baseStart_4476965 baseEnd_4476965 := by
    simpa [prefixWord, tailWord_4476965, baseEnd_4476965] using wordTrace_append hprefix tailTrace_4476965
  have hstable : (prefixWord ++ tailWord_4476965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476965).length < 2 ^ (prefixWord ++ tailWord_4476965).sum := by decide
  have hdescent : baseEnd_4476965 < baseStart_4476965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476982 : List Nat := [5, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_4476982 : Nat := 118140960795 + 4476982 * 2 ^ 59
def prefixEnd_4476982 : Nat := 4983230072969 + 3 ^ 40 * 4476982 * 2
def baseEnd_4476982 : Nat := 2298843647527308021035741

theorem tailTrace_4476982 : CollatzResearch.WordTrace tailWord_4476982 prefixEnd_4476982 2298843647527308021035741 := by
  unfold tailWord_4476982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10205559266666643531074075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108859298844444197664790133 10205559266666643531074075)
  ·
    refine ⟨15308338899999965296611113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10205559266666643531074075 15308338899999965296611113)
    ·
      refine ⟨11481254174999973972458335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15308338899999965296611113 11481254174999973972458335)
      ·
        refine ⟨17221881262499960958687503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11481254174999973972458335 17221881262499960958687503)
        ·
          refine ⟨25832821893749941438031255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17221881262499960958687503 25832821893749941438031255)
          ·
            refine ⟨38749232840624912157046883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25832821893749941438031255 38749232840624912157046883)
            ·
              refine ⟨58123849260937368235570325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38749232840624912157046883 58123849260937368235570325)
              ·
                refine ⟨2724555434106439136042359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58123849260937368235570325 2724555434106439136042359)
                ·
                  refine ⟨4086833151159658704063539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724555434106439136042359 4086833151159658704063539)
                  ·
                    refine ⟨6130249726739488056095309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4086833151159658704063539 6130249726739488056095309)
                    ·
                      refine ⟨2298843647527308021035741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6130249726739488056095309 2298843647527308021035741)
                      ·
                        rfl

theorem cell23_4476982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_4476982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476982 prefixEnd_4476982 := by exact prefixLift 4476982
  have htrace : WordTrace (prefixWord ++ tailWord_4476982) baseStart_4476982 baseEnd_4476982 := by
    simpa [prefixWord, tailWord_4476982, baseEnd_4476982] using wordTrace_append hprefix tailTrace_4476982
  have hstable : (prefixWord ++ tailWord_4476982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476982).length < 2 ^ (prefixWord ++ tailWord_4476982).sum := by decide
  have hdescent : baseEnd_4476982 < baseStart_4476982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476991 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 3]
def baseStart_4476991 : Nat := 118140960795 + 4476991 * 2 ^ 59
def prefixEnd_4476991 : Nat := 4983230072969 + 3 ^ 40 * 4476991 * 2
def baseEnd_4476991 : Nat := 2298848268853198485823199

theorem tailTrace_4476991 : CollatzResearch.WordTrace tailWord_4476991 prefixEnd_4476991 2298848268853198485823199 := by
  unfold tailWord_4476991
  simp only [CollatzResearch.WordTrace]
  refine ⟨163289276523633691034262827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108859517682422460689508551 163289276523633691034262827)
  ·
    refine ⟨244933914785450536551394241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163289276523633691034262827 244933914785450536551394241)
    ·
      refine ⟨183700436089087902413545681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244933914785450536551394241 183700436089087902413545681)
      ·
        refine ⟨137775327066815926810159261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183700436089087902413545681 137775327066815926810159261)
        ·
          refine ⟨51665747650055972553809723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137775327066815926810159261 51665747650055972553809723)
          ·
            refine ⟨77498621475083958830714585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51665747650055972553809723 77498621475083958830714585)
            ·
              refine ⟨58123966106312969123035939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77498621475083958830714585 58123966106312969123035939)
              ·
                refine ⟨87185949159469453684553909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58123966106312969123035939 87185949159469453684553909)
                ·
                  refine ⟨8173682733700261282926929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87185949159469453684553909 8173682733700261282926929)
                  ·
                    refine ⟨6130262050275195962195197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8173682733700261282926929 6130262050275195962195197)
                    ·
                      refine ⟨2298848268853198485823199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6130262050275195962195197 2298848268853198485823199)
                      ·
                        rfl

theorem cell23_4476991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_4476991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476991 prefixEnd_4476991 := by exact prefixLift 4476991
  have htrace : WordTrace (prefixWord ++ tailWord_4476991) baseStart_4476991 baseEnd_4476991 := by
    simpa [prefixWord, tailWord_4476991, baseEnd_4476991] using wordTrace_append hprefix tailTrace_4476991
  have hstable : (prefixWord ++ tailWord_4476991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476991).length < 2 ^ (prefixWord ++ tailWord_4476991).sum := by decide
  have hdescent : baseEnd_4476991 < baseStart_4476991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477005 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_4477005 : Nat := 118140960795 + 4477005 * 2 ^ 59
def prefixEnd_4477005 : Nat := 4983230072969 + 3 ^ 40 * 4477005 * 2
def baseEnd_4477005 : Nat := 2298855457582361431048135

theorem tailTrace_4477005 : CollatzResearch.WordTrace tailWord_4477005 prefixEnd_4477005 2298855457582361431048135 := by
  unfold tailWord_4477005
  simp only [CollatzResearch.WordTrace]
  refine ⟨163289787145582971425272469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108859858097055314283514979 163289787145582971425272469)
  ·
    refine ⟨7654208772449201785559647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163289787145582971425272469 7654208772449201785559647)
    ·
      refine ⟨11481313158673802678339471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7654208772449201785559647 11481313158673802678339471)
      ·
        refine ⟨17221969738010704017509207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11481313158673802678339471 17221969738010704017509207)
        ·
          refine ⟨25832954607016056026263811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17221969738010704017509207 25832954607016056026263811)
          ·
            refine ⟨38749431910524084039395717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25832954607016056026263811 38749431910524084039395717)
            ·
              refine ⟨7265518483223265757386697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38749431910524084039395717 7265518483223265757386697)
              ·
                refine ⟨5449138862417449318040023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7265518483223265757386697 5449138862417449318040023)
                ·
                  refine ⟨8173708293626173977060035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5449138862417449318040023 8173708293626173977060035)
                  ·
                    refine ⟨12260562440439260965590053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8173708293626173977060035 12260562440439260965590053)
                    ·
                      refine ⟨2298855457582361431048135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12260562440439260965590053 2298855457582361431048135)
                      ·
                        rfl

theorem cell23_4477005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_4477005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477005 prefixEnd_4477005 := by exact prefixLift 4477005
  have htrace : WordTrace (prefixWord ++ tailWord_4477005) baseStart_4477005 baseEnd_4477005 := by
    simpa [prefixWord, tailWord_4477005, baseEnd_4477005] using wordTrace_append hprefix tailTrace_4477005
  have hstable : (prefixWord ++ tailWord_4477005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477005).length < 2 ^ (prefixWord ++ tailWord_4477005).sum := by decide
  have hdescent : baseEnd_4477005 < baseStart_4477005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477039 : List Nat := [1, 1, 2, 1, 3, 5, 3, 2, 1, 2, 2]
def baseStart_4477039 : Nat := 118140960795 + 4477039 * 2 ^ 59
def prefixEnd_4477039 : Nat := 4983230072969 + 3 ^ 40 * 4477039 * 2
def baseEnd_4477039 : Nat := 2298872915924614298022979

theorem tailTrace_4477039 : CollatzResearch.WordTrace tailWord_4477039 prefixEnd_4477039 2298872915924614298022979 := by
  unfold tailWord_4477039
  simp only [CollatzResearch.WordTrace]
  refine ⟨163291027227459795232010171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108860684818306530154673447 163291027227459795232010171)
  ·
    refine ⟨244936540841189692848015257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163291027227459795232010171 244936540841189692848015257)
    ·
      refine ⟨183702405630892269636011443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244936540841189692848015257 183702405630892269636011443)
      ·
        refine ⟨275553608446338404454017165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183702405630892269636011443 275553608446338404454017165)
        ·
          refine ⟨103332603167376901670256437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275553608446338404454017165 103332603167376901670256437)
          ·
            refine ⟨9687431546941584531586541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103332603167376901670256437 9687431546941584531586541)
            ·
              refine ⟨3632786830103094199344953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9687431546941584531586541 3632786830103094199344953)
              ·
                refine ⟨2724590122577320649508715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632786830103094199344953 2724590122577320649508715)
                ·
                  refine ⟨4086885183865980974263073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724590122577320649508715 4086885183865980974263073)
                  ·
                    refine ⟨3065163887899485730697305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4086885183865980974263073 3065163887899485730697305)
                    ·
                      refine ⟨2298872915924614298022979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3065163887899485730697305 2298872915924614298022979)
                      ·
                        rfl

theorem cell23_4477039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 1, 2, 2].length) (baseStart_4477039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477039 prefixEnd_4477039 := by exact prefixLift 4477039
  have htrace : WordTrace (prefixWord ++ tailWord_4477039) baseStart_4477039 baseEnd_4477039 := by
    simpa [prefixWord, tailWord_4477039, baseEnd_4477039] using wordTrace_append hprefix tailTrace_4477039
  have hstable : (prefixWord ++ tailWord_4477039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477039).length < 2 ^ (prefixWord ++ tailWord_4477039).sum := by decide
  have hdescent : baseEnd_4477039 < baseStart_4477039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477048 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 3, 3, 2]
def baseStart_4477048 : Nat := 118140960795 + 4477048 * 2 ^ 59
def prefixEnd_4477048 : Nat := 4983230072969 + 3 ^ 40 * 4477048 * 2
def baseEnd_4477048 : Nat := 2298877537250504762810437

theorem tailTrace_4477048 : CollatzResearch.WordTrace tailWord_4477048 prefixEnd_4477048 2298877537250504762810437 := by
  unfold tailWord_4477048
  simp only [CollatzResearch.WordTrace]
  refine ⟨81645677742213594884543899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108860903656284793179391865 81645677742213594884543899)
  ·
    refine ⟨122468516613320392326815849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81645677742213594884543899 122468516613320392326815849)
    ·
      refine ⟨91851387459990294245111887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122468516613320392326815849 91851387459990294245111887)
      ·
        refine ⟨137777081189985441367667831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91851387459990294245111887 137777081189985441367667831)
        ·
          refine ⟨206665621784978162051501747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137777081189985441367667831 206665621784978162051501747)
          ·
            refine ⟨309998432677467243077252621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206665621784978162051501747 309998432677467243077252621)
            ·
              refine ⟨116249412254050216153969733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309998432677467243077252621 116249412254050216153969733)
              ·
                refine ⟨21796764797634415528869325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116249412254050216153969733 21796764797634415528869325)
                ·
                  refine ⟨8173786799112905823325997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21796764797634415528869325 8173786799112905823325997)
                  ·
                    refine ⟨3065170049667339683747249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8173786799112905823325997 3065170049667339683747249)
                    ·
                      refine ⟨2298877537250504762810437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3065170049667339683747249 2298877537250504762810437)
                      ·
                        rfl

theorem cell23_4477048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_4477048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477048 prefixEnd_4477048 := by exact prefixLift 4477048
  have htrace : WordTrace (prefixWord ++ tailWord_4477048) baseStart_4477048 baseEnd_4477048 := by
    simpa [prefixWord, tailWord_4477048, baseEnd_4477048] using wordTrace_append hprefix tailTrace_4477048
  have hstable : (prefixWord ++ tailWord_4477048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477048).length < 2 ^ (prefixWord ++ tailWord_4477048).sum := by decide
  have hdescent : baseEnd_4477048 < baseStart_4477048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477081 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 3]
def baseStart_4477081 : Nat := 118140960795 + 4477081 * 2 ^ 59
def prefixEnd_4477081 : Nat := 4983230072969 + 3 ^ 40 * 4477081 * 2
def baseEnd_4477081 : Nat := 2298894482112103133697785

theorem tailTrace_4477081 : CollatzResearch.WordTrace tailWord_4477081 prefixEnd_4477081 2298894482112103133697785 := by
  unfold tailWord_4477081
  simp only [CollatzResearch.WordTrace]
  refine ⟨163292559093307636405039097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108861706062205090936692731 163292559093307636405039097)
  ·
    refine ⟨122469419319980727303779323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163292559093307636405039097 122469419319980727303779323)
    ·
      refine ⟨183704128979971090955668985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122469419319980727303779323 183704128979971090955668985)
      ·
        refine ⟨137778096734978318216751739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183704128979971090955668985 137778096734978318216751739)
        ·
          refine ⟨206667145102467477325127609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137778096734978318216751739 206667145102467477325127609)
          ·
            refine ⟨155000358826850607993845707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206667145102467477325127609 155000358826850607993845707)
            ·
              refine ⟨232500538240275911990768561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155000358826850607993845707 232500538240275911990768561)
              ·
                refine ⟨174375403680206933993076421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232500538240275911990768561 174375403680206933993076421)
                ·
                  refine ⟨32695388190038800123701829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174375403680206933993076421 32695388190038800123701829)
                  ·
                    refine ⟨6130385285632275023194093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32695388190038800123701829 6130385285632275023194093)
                    ·
                      refine ⟨2298894482112103133697785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6130385285632275023194093 2298894482112103133697785)
                      ·
                        rfl

theorem cell23_4477081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_4477081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477081 prefixEnd_4477081 := by exact prefixLift 4477081
  have htrace : WordTrace (prefixWord ++ tailWord_4477081) baseStart_4477081 baseEnd_4477081 := by
    simpa [prefixWord, tailWord_4477081, baseEnd_4477081] using wordTrace_append hprefix tailTrace_4477081
  have hstable : (prefixWord ++ tailWord_4477081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477081).length < 2 ^ (prefixWord ++ tailWord_4477081).sum := by decide
  have hdescent : baseEnd_4477081 < baseStart_4477081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477131 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 1, 7]
def baseStart_4477131 : Nat := 118140960795 + 4477131 * 2 ^ 59
def prefixEnd_4477131 : Nat := 4983230072969 + 3 ^ 40 * 4477131 * 2
def baseEnd_4477131 : Nat := 766306718714942646024185

theorem tailTrace_4477131 : CollatzResearch.WordTrace tailWord_4477131 prefixEnd_4477131 766306718714942646024185 := by
  unfold tailWord_4477131
  simp only [CollatzResearch.WordTrace]
  refine ⟨163294382743126494944359247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108862921828750996629572831 163294382743126494944359247)
  ·
    refine ⟨244941574114689742416538871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163294382743126494944359247 244941574114689742416538871)
    ·
      refine ⟨367412361172034613624808307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244941574114689742416538871 367412361172034613624808307)
      ·
        refine ⟨551118541758051920437212461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367412361172034613624808307 551118541758051920437212461)
        ·
          refine ⟨206669453159269470163954673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 551118541758051920437212461 206669453159269470163954673)
          ·
            refine ⟨155002089869452102622966005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206669453159269470163954673 155002089869452102622966005)
            ·
              refine ⟨14531445925261134620903063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155002089869452102622966005 14531445925261134620903063)
              ·
                refine ⟨21797168887891701931354595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14531445925261134620903063 21797168887891701931354595)
                ·
                  refine ⟨32695753331837552897031893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21797168887891701931354595 32695753331837552897031893)
                  ·
                    refine ⟨766306718714942646024185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32695753331837552897031893 766306718714942646024185)
                    ·
                      rfl

theorem cell23_4477131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 7].length) (baseStart_4477131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477131 prefixEnd_4477131 := by exact prefixLift 4477131
  have htrace : WordTrace (prefixWord ++ tailWord_4477131) baseStart_4477131 baseEnd_4477131 := by
    simpa [prefixWord, tailWord_4477131, baseEnd_4477131] using wordTrace_append hprefix tailTrace_4477131
  have hstable : (prefixWord ++ tailWord_4477131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477131).length < 2 ^ (prefixWord ++ tailWord_4477131).sum := by decide
  have hdescent : baseEnd_4477131 < baseStart_4477131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477208 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 6]
def baseStart_4477208 : Nat := 118140960795 + 4477208 * 2 ^ 59
def prefixEnd_4477208 : Nat := 4983230072969 + 3 ^ 40 * 4477208 * 2
def baseEnd_4477208 : Nat := 255439966017247126312189

theorem tailTrace_4477208 : CollatzResearch.WordTrace tailWord_4477208 prefixEnd_4477208 255439966017247126312189 := by
  unfold tailWord_4477208
  simp only [CollatzResearch.WordTrace]
  refine ⟨81648595581923768547456139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108864794109231691396608185 81648595581923768547456139)
  ·
    refine ⟨122472893372885652821184209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81648595581923768547456139 122472893372885652821184209)
    ·
      refine ⟨91854670029664239615888157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122472893372885652821184209 91854670029664239615888157)
      ·
        refine ⟨34445501261124089855958059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91854670029664239615888157 34445501261124089855958059)
        ·
          refine ⟨51668251891686134783937089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34445501261124089855958059 51668251891686134783937089)
          ·
            refine ⟨38751188918764601087952817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51668251891686134783937089 38751188918764601087952817)
            ·
              refine ⟨29063391689073450815964613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38751188918764601087952817 29063391689073450815964613)
              ·
                refine ⟨5449385941701272027993365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29063391689073450815964613 5449385941701272027993365)
                ·
                  refine ⟨255439966017247126312189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5449385941701272027993365 255439966017247126312189)
                  ·
                    rfl

theorem cell23_4477208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 6].length) (baseStart_4477208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477208 prefixEnd_4477208 := by exact prefixLift 4477208
  have htrace : WordTrace (prefixWord ++ tailWord_4477208) baseStart_4477208 baseEnd_4477208 := by
    simpa [prefixWord, tailWord_4477208, baseEnd_4477208] using wordTrace_append hprefix tailTrace_4477208
  have hstable : (prefixWord ++ tailWord_4477208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477208).length < 2 ^ (prefixWord ++ tailWord_4477208).sum := by decide
  have hdescent : baseEnd_4477208 < baseStart_4477208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477211 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 8]
def baseStart_4477211 : Nat := 118140960795 + 4477211 * 2 ^ 59
def prefixEnd_4477211 : Nat := 4983230072969 + 3 ^ 40 * 4477211 * 2
def baseEnd_4477211 : Nat := 2298961234597187625072187

theorem tailTrace_4477211 : CollatzResearch.WordTrace tailWord_4477211 prefixEnd_4477211 2298961234597187625072187 := by
  unfold tailWord_4477211
  simp only [CollatzResearch.WordTrace]
  refine ⟨163297300582836668607271487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108864867055224445738180991 163297300582836668607271487)
  ·
    refine ⟨244945950874255002910907231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163297300582836668607271487 244945950874255002910907231)
    ·
      refine ⟨367418926311382504366360847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244945950874255002910907231 367418926311382504366360847)
      ·
        refine ⟨551128389467073756549541271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367418926311382504366360847 551128389467073756549541271)
        ·
          refine ⟨826692584200610634824311907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551128389467073756549541271 826692584200610634824311907)
          ·
            refine ⟨1240038876300915952236467861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826692584200610634824311907 1240038876300915952236467861)
            ·
              refine ⟨58126822326605435261084431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1240038876300915952236467861 58126822326605435261084431)
              ·
                refine ⟨87190233489908152891626647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58126822326605435261084431 87190233489908152891626647)
                ·
                  refine ⟨130785350234862229337439971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87190233489908152891626647 130785350234862229337439971)
                  ·
                    refine ⟨196178025352293344006159957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130785350234862229337439971 196178025352293344006159957)
                    ·
                      refine ⟨2298961234597187625072187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 196178025352293344006159957 2298961234597187625072187)
                      ·
                        rfl

theorem cell23_4477211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_4477211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477211 prefixEnd_4477211 := by exact prefixLift 4477211
  have htrace : WordTrace (prefixWord ++ tailWord_4477211) baseStart_4477211 baseEnd_4477211 := by
    simpa [prefixWord, tailWord_4477211, baseEnd_4477211] using wordTrace_append hprefix tailTrace_4477211
  have hstable : (prefixWord ++ tailWord_4477211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477211).length < 2 ^ (prefixWord ++ tailWord_4477211).sum := by decide
  have hdescent : baseEnd_4477211 < baseStart_4477211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477235 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 3]
def baseStart_4477235 : Nat := 118140960795 + 4477235 * 2 ^ 59
def prefixEnd_4477235 : Nat := 4983230072969 + 3 ^ 40 * 4477235 * 2
def baseEnd_4477235 : Nat := 2298973558132895531172077

theorem tailTrace_4477235 : CollatzResearch.WordTrace tailWord_4477235 prefixEnd_4477235 2298973558132895531172077 := by
  unfold tailWord_4477235
  simp only [CollatzResearch.WordTrace]
  refine ⟨163298175934749720706145159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108865450623166480470763439 163298175934749720706145159)
  ·
    refine ⟨244947263902124581059217739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163298175934749720706145159 244947263902124581059217739)
    ·
      refine ⟨367420895853186871588826609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244947263902124581059217739 367420895853186871588826609)
      ·
        refine ⟨275565671889890153691619957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367420895853186871588826609 275565671889890153691619957)
        ·
          refine ⟨25834281739677201908589371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 275565671889890153691619957 25834281739677201908589371)
          ·
            refine ⟨38751422609515802862884057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25834281739677201908589371 38751422609515802862884057)
            ·
              refine ⟨29063566957136852147163043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38751422609515802862884057 29063566957136852147163043)
              ·
                refine ⟨43595350435705278220744565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29063566957136852147163043 43595350435705278220744565)
                ·
                  refine ⟨4087064103347369833194803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43595350435705278220744565 4087064103347369833194803)
                  ·
                    refine ⟨6130596155021054749792205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4087064103347369833194803 6130596155021054749792205)
                    ·
                      refine ⟨2298973558132895531172077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6130596155021054749792205 2298973558132895531172077)
                      ·
                        rfl

theorem cell23_4477235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 3].length) (baseStart_4477235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477235 prefixEnd_4477235 := by exact prefixLift 4477235
  have htrace : WordTrace (prefixWord ++ tailWord_4477235) baseStart_4477235 baseEnd_4477235 := by
    simpa [prefixWord, tailWord_4477235, baseEnd_4477235] using wordTrace_append hprefix tailTrace_4477235
  have hstable : (prefixWord ++ tailWord_4477235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477235).length < 2 ^ (prefixWord ++ tailWord_4477235).sum := by decide
  have hdescent : baseEnd_4477235 < baseStart_4477235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477285 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_4477285 : Nat := 118140960795 + 4477285 * 2 ^ 59
def prefixEnd_4477285 : Nat := 4983230072969 + 3 ^ 40 * 4477285 * 2
def baseEnd_4477285 : Nat := 766333077388540111848949

theorem tailTrace_4477285 : CollatzResearch.WordTrace tailWord_4477285 prefixEnd_4477285 766333077388540111848949 := by
  unfold tailWord_4477285
  simp only [CollatzResearch.WordTrace]
  refine ⟨163299999584568579245465309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108866666389712386163643539 163299999584568579245465309)
  ·
    refine ⟨61237499844213217217049491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163299999584568579245465309 61237499844213217217049491)
    ·
      refine ⟨91856249766319825825574237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61237499844213217217049491 91856249766319825825574237)
      ·
        refine ⟨34446093662369934684590339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91856249766319825825574237 34446093662369934684590339)
        ·
          refine ⟨51669140493554902026885509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34446093662369934684590339 51669140493554902026885509)
          ·
            refine ⟨9687963842541544130041033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51669140493554902026885509 9687963842541544130041033)
            ·
              refine ⟨7265972881906158097530775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9687963842541544130041033 7265972881906158097530775)
              ·
                refine ⟨10898959322859237146296163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7265972881906158097530775 10898959322859237146296163)
                ·
                  refine ⟨16348438984288855719444245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10898959322859237146296163 16348438984288855719444245)
                  ·
                    refine ⟨766333077388540111848949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16348438984288855719444245 766333077388540111848949)
                    ·
                      rfl

theorem cell23_4477285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_4477285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477285 prefixEnd_4477285 := by exact prefixLift 4477285
  have htrace : WordTrace (prefixWord ++ tailWord_4477285) baseStart_4477285 baseEnd_4477285 := by
    simpa [prefixWord, tailWord_4477285, baseEnd_4477285] using wordTrace_append hprefix tailTrace_4477285
  have hstable : (prefixWord ++ tailWord_4477285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477285).length < 2 ^ (prefixWord ++ tailWord_4477285).sum := by decide
  have hdescent : baseEnd_4477285 < baseStart_4477285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477309 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_4477309 : Nat := 118140960795 + 4477309 * 2 ^ 59
def prefixEnd_4477309 : Nat := 4983230072969 + 3 ^ 40 * 4477309 * 2
def baseEnd_4477309 : Nat := 2299011555701328241646737

theorem tailTrace_4477309 : CollatzResearch.WordTrace tailWord_4477309 prefixEnd_4477309 2299011555701328241646737 := by
  unfold tailWord_4477309
  simp only [CollatzResearch.WordTrace]
  refine ⟨163300874936481631344338981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108867249957654420896225987 163300874936481631344338981)
  ·
    refine ⟨30618914050590305877063559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163300874936481631344338981 30618914050590305877063559)
    ·
      refine ⟨45928371075885458815595339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30618914050590305877063559 45928371075885458815595339)
      ·
        refine ⟨68892556613828188223393009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45928371075885458815595339 68892556613828188223393009)
        ·
          refine ⟨51669417460371141167544757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68892556613828188223393009 51669417460371141167544757)
          ·
            refine ⟨4844007886909794484457321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51669417460371141167544757 4844007886909794484457321)
            ·
              refine ⟨3633005915182345863342991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4844007886909794484457321 3633005915182345863342991)
              ·
                refine ⟨5449508872773518795014487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3633005915182345863342991 5449508872773518795014487)
                ·
                  refine ⟨8174263309160278192521731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5449508872773518795014487 8174263309160278192521731)
                  ·
                    refine ⟨12261394963740417288782597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8174263309160278192521731 12261394963740417288782597)
                    ·
                      refine ⟨2299011555701328241646737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12261394963740417288782597 2299011555701328241646737)
                      ·
                        rfl

theorem cell23_4477309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_4477309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477309 prefixEnd_4477309 := by exact prefixLift 4477309
  have htrace : WordTrace (prefixWord ++ tailWord_4477309) baseStart_4477309 baseEnd_4477309 := by
    simpa [prefixWord, tailWord_4477309, baseEnd_4477309] using wordTrace_append hprefix tailTrace_4477309
  have hstable : (prefixWord ++ tailWord_4477309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477309).length < 2 ^ (prefixWord ++ tailWord_4477309).sum := by decide
  have hdescent : baseEnd_4477309 < baseStart_4477309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477326 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4477326 : Nat := 118140960795 + 4477326 * 2 ^ 59
def prefixEnd_4477326 : Nat := 4983230072969 + 3 ^ 40 * 4477326 * 2
def baseEnd_4477326 : Nat := 2299020284872454675134159

theorem tailTrace_4477326 : CollatzResearch.WordTrace tailWord_4477326 prefixEnd_4477326 2299020284872454675134159 := by
  unfold tailWord_4477326
  simp only [CollatzResearch.WordTrace]
  refine ⟨20412686872177505405963479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108867663318280028831805221 20412686872177505405963479)
  ·
    refine ⟨30619030308266258108945219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20412686872177505405963479 30619030308266258108945219)
    ·
      refine ⟨45928545462399387163417829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30619030308266258108945219 45928545462399387163417829)
      ·
        refine ⟨8611602274199885093140843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45928545462399387163417829 8611602274199885093140843)
        ·
          refine ⟨12917403411299827639711265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8611602274199885093140843 12917403411299827639711265)
          ·
            refine ⟨9688052558474870729783449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12917403411299827639711265 9688052558474870729783449)
            ·
              refine ⟨7266039418856153047337587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9688052558474870729783449 7266039418856153047337587)
              ·
                refine ⟨10899059128284229571006381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7266039418856153047337587 10899059128284229571006381)
                ·
                  refine ⟨4087147173106586089127393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10899059128284229571006381 4087147173106586089127393)
                  ·
                    refine ⟨3065360379829939566845545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4087147173106586089127393 3065360379829939566845545)
                    ·
                      refine ⟨2299020284872454675134159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3065360379829939566845545 2299020284872454675134159)
                      ·
                        rfl

theorem cell23_4477326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4477326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477326 prefixEnd_4477326 := by exact prefixLift 4477326
  have htrace : WordTrace (prefixWord ++ tailWord_4477326) baseStart_4477326 baseEnd_4477326 := by
    simpa [prefixWord, tailWord_4477326, baseEnd_4477326] using wordTrace_append hprefix tailTrace_4477326
  have hstable : (prefixWord ++ tailWord_4477326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477326).length < 2 ^ (prefixWord ++ tailWord_4477326).sum := by decide
  have hdescent : baseEnd_4477326 < baseStart_4477326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477369 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 1, 3, 2]
def baseStart_4477369 : Nat := 118140960795 + 4477369 * 2 ^ 59
def prefixEnd_4477369 : Nat := 4983230072969 + 3 ^ 40 * 4477369 * 2
def baseEnd_4477369 : Nat := 2299042364540598006896461

theorem tailTrace_4477369 : CollatzResearch.WordTrace tailWord_4477369 prefixEnd_4477369 2299042364540598006896461 := by
  unfold tailWord_4477369
  simp only [CollatzResearch.WordTrace]
  refine ⟨163303063316264261591523161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108868708877509507727682107 163303063316264261591523161)
  ·
    refine ⟨122477297487198196193642371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163303063316264261591523161 122477297487198196193642371)
    ·
      refine ⟨183715946230797294290463557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122477297487198196193642371 183715946230797294290463557)
      ·
        refine ⟨34446739918274492679461917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183715946230797294290463557 34446739918274492679461917)
        ·
          refine ⟨12917527469352934754798219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34446739918274492679461917 12917527469352934754798219)
          ·
            refine ⟨19376291204029402132197329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12917527469352934754798219 19376291204029402132197329)
            ·
              refine ⟨14532218403022051599147997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19376291204029402132197329 14532218403022051599147997)
              ·
                refine ⟨5449581901133269349680499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14532218403022051599147997 5449581901133269349680499)
                ·
                  refine ⟨8174372851699904024520749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5449581901133269349680499 8174372851699904024520749)
                  ·
                    refine ⟨3065389819387464009195281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8174372851699904024520749 3065389819387464009195281)
                    ·
                      refine ⟨2299042364540598006896461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3065389819387464009195281 2299042364540598006896461)
                      ·
                        rfl

theorem cell23_4477369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_4477369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477369 prefixEnd_4477369 := by exact prefixLift 4477369
  have htrace : WordTrace (prefixWord ++ tailWord_4477369) baseStart_4477369 baseEnd_4477369 := by
    simpa [prefixWord, tailWord_4477369, baseEnd_4477369] using wordTrace_append hprefix tailTrace_4477369
  have hstable : (prefixWord ++ tailWord_4477369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477369).length < 2 ^ (prefixWord ++ tailWord_4477369).sum := by decide
  have hdescent : baseEnd_4477369 < baseStart_4477369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477377 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4477377 : Nat := 118140960795 + 4477377 * 2 ^ 59
def prefixEnd_4477377 : Nat := 4983230072969 + 3 ^ 40 * 4477377 * 2
def baseEnd_4477377 : Nat := 2299046472385833975596425

theorem tailTrace_4477377 : CollatzResearch.WordTrace tailWord_4477377 prefixEnd_4477377 2299046472385833975596425 := by
  unfold tailWord_4477377
  simp only [CollatzResearch.WordTrace]
  refine ⟨163303355100235278957814385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108868903400156852638542923 163303355100235278957814385)
  ·
    refine ⟨122477516325176459218360789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163303355100235278957814385 122477516325176459218360789)
    ·
      refine ⟨2870566788871323262930331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 122477516325176459218360789 2870566788871323262930331)
      ·
        refine ⟨4305850183306984894395497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2870566788871323262930331 4305850183306984894395497)
        ·
          refine ⟨3229387637480238670796623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4305850183306984894395497 3229387637480238670796623)
          ·
            refine ⟨4844081456220358006194935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229387637480238670796623 4844081456220358006194935)
            ·
              refine ⟨7266122184330537009292403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4844081456220358006194935 7266122184330537009292403)
              ·
                refine ⟨10899183276495805513938605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7266122184330537009292403 10899183276495805513938605)
                ·
                  refine ⟨4087193728685927067726977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10899183276495805513938605 4087193728685927067726977)
                  ·
                    refine ⟨3065395296514445300795233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4087193728685927067726977 3065395296514445300795233)
                    ·
                      refine ⟨2299046472385833975596425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3065395296514445300795233 2299046472385833975596425)
                      ·
                        rfl

theorem cell23_4477377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4477377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477377 prefixEnd_4477377 := by exact prefixLift 4477377
  have htrace : WordTrace (prefixWord ++ tailWord_4477377) baseStart_4477377 baseEnd_4477377 := by
    simpa [prefixWord, tailWord_4477377, baseEnd_4477377] using wordTrace_append hprefix tailTrace_4477377
  have hstable : (prefixWord ++ tailWord_4477377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477377).length < 2 ^ (prefixWord ++ tailWord_4477377).sum := by decide
  have hdescent : baseEnd_4477377 < baseStart_4477377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477405 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 9]
def baseStart_4477405 : Nat := 118140960795 + 4477405 * 2 ^ 59
def prefixEnd_4477405 : Nat := 4983230072969 + 3 ^ 40 * 4477405 * 2
def baseEnd_4477405 : Nat := 255451205538239985116255

theorem tailTrace_4477405 : CollatzResearch.WordTrace tailWord_4477405 prefixEnd_4477405 255451205538239985116255 := by
  unfold tailWord_4477405
  simp only [CollatzResearch.WordTrace]
  refine ⟨163304376344133839739833669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108869584229422559826555779 163304376344133839739833669)
  ·
    refine ⟨30619570564525094951218813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163304376344133839739833669 30619570564525094951218813)
    ·
      refine ⟨11482338961696910606707055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30619570564525094951218813 11482338961696910606707055)
      ·
        refine ⟨17223508442545365910060583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11482338961696910606707055 17223508442545365910060583)
        ·
          refine ⟨25835262663818048865090875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17223508442545365910060583 25835262663818048865090875)
          ·
            refine ⟨38752893995727073297636313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25835262663818048865090875 38752893995727073297636313)
            ·
              refine ⟨29064670496795304973227235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38752893995727073297636313 29064670496795304973227235)
              ·
                refine ⟨43597005745192957459840853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29064670496795304973227235 43597005745192957459840853)
                ·
                  refine ⟨255451205538239985116255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43597005745192957459840853 255451205538239985116255)
                  ·
                    rfl

theorem cell23_4477405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_4477405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477405 prefixEnd_4477405 := by exact prefixLift 4477405
  have htrace : WordTrace (prefixWord ++ tailWord_4477405) baseStart_4477405 baseEnd_4477405 := by
    simpa [prefixWord, tailWord_4477405, baseEnd_4477405] using wordTrace_append hprefix tailTrace_4477405
  have hstable : (prefixWord ++ tailWord_4477405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477405).length < 2 ^ (prefixWord ++ tailWord_4477405).sum := by decide
  have hdescent : baseEnd_4477405 < baseStart_4477405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477445 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_4477445 : Nat := 118140960795 + 4477445 * 2 ^ 59
def prefixEnd_4477445 : Nat := 4983230072969 + 3 ^ 40 * 4477445 * 2
def baseEnd_4477445 : Nat := 2299081389070339709546111

theorem tailTrace_4477445 : CollatzResearch.WordTrace tailWord_4477445 prefixEnd_4477445 2299081389070339709546111 := by
  unfold tailWord_4477445
  simp only [CollatzResearch.WordTrace]
  refine ⟨163305835263988926571289789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108870556842659284380859859 163305835263988926571289789)
  ·
    refine ⟨61239688223995847464233671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163305835263988926571289789 61239688223995847464233671)
    ·
      refine ⟨91859532335993771196350507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61239688223995847464233671 91859532335993771196350507)
      ·
        refine ⟨137789298503990656794525761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91859532335993771196350507 137789298503990656794525761)
        ·
          refine ⟨103341973877992992595894321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137789298503990656794525761 103341973877992992595894321)
          ·
            refine ⟨77506480408494744446920741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103341973877992992595894321 77506480408494744446920741)
            ·
              refine ⟨14532465076592764583797639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77506480408494744446920741 14532465076592764583797639)
              ·
                refine ⟨21798697614889146875696459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14532465076592764583797639 21798697614889146875696459)
                ·
                  refine ⟨32698046422333720313544689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21798697614889146875696459 32698046422333720313544689)
                  ·
                    refine ⟨24523534816750290235158517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32698046422333720313544689 24523534816750290235158517)
                    ·
                      refine ⟨2299081389070339709546111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24523534816750290235158517 2299081389070339709546111)
                      ·
                        rfl

theorem cell23_4477445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_4477445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477445 prefixEnd_4477445 := by exact prefixLift 4477445
  have htrace : WordTrace (prefixWord ++ tailWord_4477445) baseStart_4477445 baseEnd_4477445 := by
    simpa [prefixWord, tailWord_4477445, baseEnd_4477445] using wordTrace_append hprefix tailTrace_4477445
  have hstable : (prefixWord ++ tailWord_4477445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477445).length < 2 ^ (prefixWord ++ tailWord_4477445).sum := by decide
  have hdescent : baseEnd_4477445 < baseStart_4477445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477446 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4477446 : Nat := 118140960795 + 4477446 * 2 ^ 59
def prefixEnd_4477446 : Nat := 4983230072969 + 3 ^ 40 * 4477446 * 2
def baseEnd_4477446 : Nat := 2299081902550994205633607

theorem tailTrace_4477446 : CollatzResearch.WordTrace tailWord_4477446 prefixEnd_4477446 2299081902550994205633607 := by
  unfold tailWord_4477446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5103308491780790741939881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108870581157990202494717461 5103308491780790741939881)
  ·
    refine ⟨3827481368835593056454911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5103308491780790741939881 3827481368835593056454911)
    ·
      refine ⟨5741222053253389584682367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3827481368835593056454911 5741222053253389584682367)
      ·
        refine ⟨8611833079880084377023551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5741222053253389584682367 8611833079880084377023551)
        ·
          refine ⟨12917749619820126565535327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8611833079880084377023551 12917749619820126565535327)
          ·
            refine ⟨19376624429730189848302991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12917749619820126565535327 19376624429730189848302991)
            ·
              refine ⟨29064936644595284772454487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19376624429730189848302991 29064936644595284772454487)
              ·
                refine ⟨43597404966892927158681731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29064936644595284772454487 43597404966892927158681731)
                ·
                  refine ⟨65396107450339390738022597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43597404966892927158681731 65396107450339390738022597)
                  ·
                    refine ⟨12261770146938635763379237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65396107450339390738022597 12261770146938635763379237)
                    ·
                      refine ⟨2299081902550994205633607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12261770146938635763379237 2299081902550994205633607)
                      ·
                        rfl

theorem cell23_4477446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4477446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477446 prefixEnd_4477446 := by exact prefixLift 4477446
  have htrace : WordTrace (prefixWord ++ tailWord_4477446) baseStart_4477446 baseEnd_4477446 := by
    simpa [prefixWord, tailWord_4477446, baseEnd_4477446] using wordTrace_append hprefix tailTrace_4477446
  have hstable : (prefixWord ++ tailWord_4477446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477446).length < 2 ^ (prefixWord ++ tailWord_4477446).sum := by decide
  have hdescent : baseEnd_4477446 < baseStart_4477446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477455 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_4477455 : Nat := 118140960795 + 4477455 * 2 ^ 59
def prefixEnd_4477455 : Nat := 4983230072969 + 3 ^ 40 * 4477455 * 2
def baseEnd_4477455 : Nat := 2299086523876884670421065

theorem tailTrace_4477455 : CollatzResearch.WordTrace tailWord_4477455 prefixEnd_4477455 2299086523876884670421065 := by
  unfold tailWord_4477455
  simp only [CollatzResearch.WordTrace]
  refine ⟨163306199993952698279153819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108870799995968465519435879 163306199993952698279153819)
  ·
    refine ⟨244959299990929047418730729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163306199993952698279153819 244959299990929047418730729)
    ·
      refine ⟨183719474993196785564048047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244959299990929047418730729 183719474993196785564048047)
      ·
        refine ⟨275579212489795178346072071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183719474993196785564048047 275579212489795178346072071)
        ·
          refine ⟨413368818734692767519108107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275579212489795178346072071 413368818734692767519108107)
          ·
            refine ⟨620053228102039151278662161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413368818734692767519108107 620053228102039151278662161)
            ·
              refine ⟨465039921076529363458996621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620053228102039151278662161 465039921076529363458996621)
              ·
                refine ⟨174389970403698511297123733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 465039921076529363458996621 174389970403698511297123733)
                ·
                  refine ⟨8174529862673367717052675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 174389970403698511297123733 8174529862673367717052675)
                  ·
                    refine ⟨12261794794010051575579013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8174529862673367717052675 12261794794010051575579013)
                    ·
                      refine ⟨2299086523876884670421065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12261794794010051575579013 2299086523876884670421065)
                      ·
                        rfl

theorem cell23_4477455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_4477455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477455 prefixEnd_4477455 := by exact prefixLift 4477455
  have htrace : WordTrace (prefixWord ++ tailWord_4477455) baseStart_4477455 baseEnd_4477455 := by
    simpa [prefixWord, tailWord_4477455, baseEnd_4477455] using wordTrace_append hprefix tailTrace_4477455
  have hstable : (prefixWord ++ tailWord_4477455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477455).length < 2 ^ (prefixWord ++ tailWord_4477455).sum := by decide
  have hdescent : baseEnd_4477455 < baseStart_4477455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477469 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_4477469 : Nat := 118140960795 + 4477469 * 2 ^ 59
def prefixEnd_4477469 : Nat := 4983230072969 + 3 ^ 40 * 4477469 * 2
def baseEnd_4477469 : Nat := 766364570868682538548667

theorem tailTrace_4477469 : CollatzResearch.WordTrace tailWord_4477469 prefixEnd_4477469 766364570868682538548667 := by
  unfold tailWord_4477469
  simp only [CollatzResearch.WordTrace]
  refine ⟨163306710615901978670163461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108871140410601319113442307 163306710615901978670163461)
  ·
    refine ⟨30620008240481621000655649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163306710615901978670163461 30620008240481621000655649)
    ·
      refine ⟨22965006180361215750491737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30620008240481621000655649 22965006180361215750491737)
      ·
        refine ⟨17223754635270911812868803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22965006180361215750491737 17223754635270911812868803)
        ·
          refine ⟨25835631952906367719303205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17223754635270911812868803 25835631952906367719303205)
          ·
            refine ⟨4844180991169943947369351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25835631952906367719303205 4844180991169943947369351)
            ·
              refine ⟨7266271486754915921054027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4844180991169943947369351 7266271486754915921054027)
              ·
                refine ⟨10899407230132373881581041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7266271486754915921054027 10899407230132373881581041)
                ·
                  refine ⟨8174555422599280411185781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10899407230132373881581041 8174555422599280411185781)
                  ·
                    refine ⟨766364570868682538548667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8174555422599280411185781 766364570868682538548667)
                    ·
                      rfl

theorem cell23_4477469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_4477469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477469 prefixEnd_4477469 := by exact prefixLift 4477469
  have htrace : WordTrace (prefixWord ++ tailWord_4477469) baseStart_4477469 baseEnd_4477469 := by
    simpa [prefixWord, tailWord_4477469, baseEnd_4477469] using wordTrace_append hprefix tailTrace_4477469
  have hstable : (prefixWord ++ tailWord_4477469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477469).length < 2 ^ (prefixWord ++ tailWord_4477469).sum := by decide
  have hdescent : baseEnd_4477469 < baseStart_4477469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477495 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 8]
def baseStart_4477495 : Nat := 118140960795 + 4477495 * 2 ^ 59
def prefixEnd_4477495 : Nat := 4983230072969 + 3 ^ 40 * 4477495 * 2
def baseEnd_4477495 : Nat := 255456340344784945991209

theorem tailTrace_4477495 : CollatzResearch.WordTrace tailWord_4477495 prefixEnd_4477495 255456340344784945991209 := by
  unfold tailWord_4477495
  simp only [CollatzResearch.WordTrace]
  refine ⟨163307658913807785110609939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108871772609205190073739959 163307658913807785110609939)
  ·
    refine ⟨244961488370711677665914909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163307658913807785110609939 244961488370711677665914909)
    ·
      refine ⟨91860558139016879124718091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244961488370711677665914909 91860558139016879124718091)
      ·
        refine ⟨137790837208525318687077137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91860558139016879124718091 137790837208525318687077137)
        ·
          refine ⟨103343127906393989015307853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137790837208525318687077137 103343127906393989015307853)
          ·
            refine ⟨38753672964897745880740445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103343127906393989015307853 38753672964897745880740445)
            ·
              refine ⟨14532627361836654705277667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38753672964897745880740445 14532627361836654705277667)
              ·
                refine ⟨21798941042754982057916501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14532627361836654705277667 21798941042754982057916501)
                ·
                  refine ⟨255456340344784945991209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21798941042754982057916501 255456340344784945991209)
                  ·
                    rfl

theorem cell23_4477495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 8].length) (baseStart_4477495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477495 prefixEnd_4477495 := by exact prefixLift 4477495
  have htrace : WordTrace (prefixWord ++ tailWord_4477495) baseStart_4477495 baseEnd_4477495 := by
    simpa [prefixWord, tailWord_4477495, baseEnd_4477495] using wordTrace_append hprefix tailTrace_4477495
  have hstable : (prefixWord ++ tailWord_4477495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477495).length < 2 ^ (prefixWord ++ tailWord_4477495).sum := by decide
  have hdescent : baseEnd_4477495 < baseStart_4477495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477522 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_4477522 : Nat := 118140960795 + 4477522 * 2 ^ 59
def prefixEnd_4477522 : Nat := 4983230072969 + 3 ^ 40 * 4477522 * 2
def baseEnd_4477522 : Nat := 2299120927080735908283257

theorem tailTrace_4477522 : CollatzResearch.WordTrace tailWord_4477522 prefixEnd_4477522 2299120927080735908283257 := by
  unfold tailWord_4477522
  simp only [CollatzResearch.WordTrace]
  refine ⟨40827160921177492180460705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108872429123139979147895213 40827160921177492180460705)
  ·
    refine ⟨30620370690883119135345529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40827160921177492180460705 30620370690883119135345529)
    ·
      refine ⟨22965278018162339351509147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30620370690883119135345529 22965278018162339351509147)
      ·
        refine ⟨34447917027243509027263721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22965278018162339351509147 34447917027243509027263721)
        ·
          refine ⟨25835937770432631770447791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34447917027243509027263721 25835937770432631770447791)
          ·
            refine ⟨38753906655648947655671687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25835937770432631770447791 38753906655648947655671687)
            ·
              refine ⟨58130859983473421483507531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38753906655648947655671687 58130859983473421483507531)
              ·
                refine ⟨87196289975210132225261297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58130859983473421483507531 87196289975210132225261297)
                ·
                  refine ⟨65397217481407599168945973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87196289975210132225261297 65397217481407599168945973)
                  ·
                    refine ⟨6130989138881962422088685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65397217481407599168945973 6130989138881962422088685)
                    ·
                      refine ⟨2299120927080735908283257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6130989138881962422088685 2299120927080735908283257)
                      ·
                        rfl

theorem cell23_4477522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_4477522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477522 prefixEnd_4477522 := by exact prefixLift 4477522
  have htrace : WordTrace (prefixWord ++ tailWord_4477522) baseStart_4477522 baseEnd_4477522 := by
    simpa [prefixWord, tailWord_4477522, baseEnd_4477522] using wordTrace_append hprefix tailTrace_4477522
  have hstable : (prefixWord ++ tailWord_4477522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477522).length < 2 ^ (prefixWord ++ tailWord_4477522).sum := by decide
  have hdescent : baseEnd_4477522 < baseStart_4477522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477555 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 5, 6]
def baseStart_4477555 : Nat := 118140960795 + 4477555 * 2 ^ 59
def prefixEnd_4477555 : Nat := 4983230072969 + 3 ^ 40 * 4477555 * 2
def baseEnd_4477555 : Nat := 766379290647444759723535

theorem tailTrace_4477555 : CollatzResearch.WordTrace tailWord_4477555 prefixEnd_4477555 766379290647444759723535 := by
  unfold tailWord_4477555
  simp only [CollatzResearch.WordTrace]
  refine ⟨163309847293590415357794119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108873231529060276905196079 163309847293590415357794119)
  ·
    refine ⟨244964770940385623036691179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163309847293590415357794119 244964770940385623036691179)
    ·
      refine ⟨367447156410578434555036769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244964770940385623036691179 367447156410578434555036769)
      ·
        refine ⟨275585367307933825916277577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367447156410578434555036769 275585367307933825916277577)
        ·
          refine ⟨206689025480950369437208183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275585367307933825916277577 206689025480950369437208183)
          ·
            refine ⟨310033538221425554155812275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206689025480950369437208183 310033538221425554155812275)
            ·
              refine ⟨465050307332138331233718413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310033538221425554155812275 465050307332138331233718413)
              ·
                refine ⟨174393865249551874212644405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 465050307332138331233718413 174393865249551874212644405)
                ·
                  refine ⟨16349424867145488207435413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174393865249551874212644405 16349424867145488207435413)
                  ·
                    refine ⟨766379290647444759723535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16349424867145488207435413 766379290647444759723535)
                    ·
                      rfl

theorem cell23_4477555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 6].length) (baseStart_4477555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477555 prefixEnd_4477555 := by exact prefixLift 4477555
  have htrace : WordTrace (prefixWord ++ tailWord_4477555) baseStart_4477555 baseEnd_4477555 := by
    simpa [prefixWord, tailWord_4477555, baseEnd_4477555] using wordTrace_append hprefix tailTrace_4477555
  have hstable : (prefixWord ++ tailWord_4477555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477555).length < 2 ^ (prefixWord ++ tailWord_4477555).sum := by decide
  have hdescent : baseEnd_4477555 < baseStart_4477555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477595 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 7]
def baseStart_4477595 : Nat := 118140960795 + 4477595 * 2 ^ 59
def prefixEnd_4477595 : Nat := 4983230072969 + 3 ^ 40 * 4477595 * 2
def baseEnd_4477595 : Nat := 2299158411168514122670421

theorem tailTrace_4477595 : CollatzResearch.WordTrace tailWord_4477595 prefixEnd_4477595 2299158411168514122670421 := by
  unfold tailWord_4477595
  simp only [CollatzResearch.WordTrace]
  refine ⟨163311306213445502189250239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108874204142297001459500159 163311306213445502189250239)
  ·
    refine ⟨244966959320168253283875359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163311306213445502189250239 244966959320168253283875359)
    ·
      refine ⟨367450438980252379925813039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244966959320168253283875359 367450438980252379925813039)
      ·
        refine ⟨551175658470378569888719559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367450438980252379925813039 551175658470378569888719559)
        ·
          refine ⟨826763487705567854833079339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551175658470378569888719559 826763487705567854833079339)
          ·
            refine ⟨1240145231558351782249619009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826763487705567854833079339 1240145231558351782249619009)
            ·
              refine ⟨930108923668763836687214257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240145231558351782249619009 930108923668763836687214257)
              ·
                refine ⟨697581692751572877515410693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930108923668763836687214257 697581692751572877515410693)
                ·
                  refine ⟨130796567390919914534139505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697581692751572877515410693 130796567390919914534139505)
                  ·
                    refine ⟨98097425543189935900604629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130796567390919914534139505 98097425543189935900604629)
                    ·
                      refine ⟨2299158411168514122670421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98097425543189935900604629 2299158411168514122670421)
                      ·
                        rfl

theorem cell23_4477595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_4477595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477595 prefixEnd_4477595 := by exact prefixLift 4477595
  have htrace : WordTrace (prefixWord ++ tailWord_4477595) baseStart_4477595 baseEnd_4477595 := by
    simpa [prefixWord, tailWord_4477595, baseEnd_4477595] using wordTrace_append hprefix tailTrace_4477595
  have hstable : (prefixWord ++ tailWord_4477595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477595).length < 2 ^ (prefixWord ++ tailWord_4477595).sum := by decide
  have hdescent : baseEnd_4477595 < baseStart_4477595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477629 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_4477629 : Nat := 118140960795 + 4477629 * 2 ^ 59
def prefixEnd_4477629 : Nat := 4983230072969 + 3 ^ 40 * 4477629 * 2
def baseEnd_4477629 : Nat := 2299175869510766989645265

theorem tailTrace_4477629 : CollatzResearch.WordTrace tailWord_4477629 prefixEnd_4477629 2299175869510766989645265 := by
  unfold tailWord_4477629
  simp only [CollatzResearch.WordTrace]
  refine ⟨163312546295322325995987941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108875030863548217330658627 163312546295322325995987941)
  ·
    refine ⟨30621102430372936124247739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163312546295322325995987941 30621102430372936124247739)
    ·
      refine ⟨45931653645559404186371609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30621102430372936124247739 45931653645559404186371609)
      ·
        refine ⟨34448740234169553139778707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45931653645559404186371609 34448740234169553139778707)
        ·
          refine ⟨51673110351254329709668061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34448740234169553139778707 51673110351254329709668061)
          ·
            refine ⟨19377416381720373641125523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51673110351254329709668061 19377416381720373641125523)
            ·
              refine ⟨29066124572580560461688285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19377416381720373641125523 29066124572580560461688285)
              ·
                refine ⟨10899796714717710173133107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29066124572580560461688285 10899796714717710173133107)
                ·
                  refine ⟨16349695072076565259699661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10899796714717710173133107 16349695072076565259699661)
                  ·
                    refine ⟨6131135652028711972387373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16349695072076565259699661 6131135652028711972387373)
                    ·
                      refine ⟨2299175869510766989645265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6131135652028711972387373 2299175869510766989645265)
                      ·
                        rfl

theorem cell23_4477629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_4477629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477629 prefixEnd_4477629 := by exact prefixLift 4477629
  have htrace : WordTrace (prefixWord ++ tailWord_4477629) baseStart_4477629 baseEnd_4477629 := by
    simpa [prefixWord, tailWord_4477629, baseEnd_4477629] using wordTrace_append hprefix tailTrace_4477629
  have hstable : (prefixWord ++ tailWord_4477629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477629).length < 2 ^ (prefixWord ++ tailWord_4477629).sum := by decide
  have hdescent : baseEnd_4477629 < baseStart_4477629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477650 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_4477650 : Nat := 118140960795 + 4477650 * 2 ^ 59
def prefixEnd_4477650 : Nat := 4983230072969 + 3 ^ 40 * 4477650 * 2
def baseEnd_4477650 : Nat := 2299186652604511407482669

theorem tailTrace_4477650 : CollatzResearch.WordTrace tailWord_4477650 prefixEnd_4477650 2299186652604511407482669 := by
  unfold tailWord_4477650
  simp only [CollatzResearch.WordTrace]
  refine ⟨40828328057061561645625601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108875541485497497721668269 40828328057061561645625601)
  ·
    refine ⟨30621246042796171234219201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40828328057061561645625601 30621246042796171234219201)
    ·
      refine ⟨22965934532097128425664401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30621246042796171234219201 22965934532097128425664401)
      ·
        refine ⟨17224450899072846319248301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22965934532097128425664401 17224450899072846319248301)
        ·
          refine ⟨6459169087152317369718113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17224450899072846319248301 6459169087152317369718113)
          ·
            refine ⟨4844376815364238027288585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6459169087152317369718113 4844376815364238027288585)
            ·
              refine ⟨3633282611523178520466439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4844376815364238027288585 3633282611523178520466439)
              ·
                refine ⟨5449923917284767780699659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3633282611523178520466439 5449923917284767780699659)
                ·
                  refine ⟨8174885875927151671049489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5449923917284767780699659 8174885875927151671049489)
                  ·
                    refine ⟨6131164406945363753287117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8174885875927151671049489 6131164406945363753287117)
                    ·
                      refine ⟨2299186652604511407482669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6131164406945363753287117 2299186652604511407482669)
                      ·
                        rfl

theorem cell23_4477650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_4477650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477650 prefixEnd_4477650 := by exact prefixLift 4477650
  have htrace : WordTrace (prefixWord ++ tailWord_4477650) baseStart_4477650 baseEnd_4477650 := by
    simpa [prefixWord, tailWord_4477650, baseEnd_4477650] using wordTrace_append hprefix tailTrace_4477650
  have hstable : (prefixWord ++ tailWord_4477650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477650).length < 2 ^ (prefixWord ++ tailWord_4477650).sum := by decide
  have hdescent : baseEnd_4477650 < baseStart_4477650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477663 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 3]
def baseStart_4477663 : Nat := 118140960795 + 4477663 * 2 ^ 59
def prefixEnd_4477663 : Nat := 4983230072969 + 3 ^ 40 * 4477663 * 2
def baseEnd_4477663 : Nat := 2299193327853019856620109

theorem tailTrace_4477663 : CollatzResearch.WordTrace tailWord_4477663 prefixEnd_4477663 2299193327853019856620109 := by
  unfold tailWord_4477663
  simp only [CollatzResearch.WordTrace]
  refine ⟨163313786377199149802725643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108875857584799433201817095 163313786377199149802725643)
  ·
    refine ⟨244970679565798724704088465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163313786377199149802725643 244970679565798724704088465)
    ·
      refine ⟨183728009674349043528066349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244970679565798724704088465 183728009674349043528066349)
      ·
        refine ⟨68898003627880891323024881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183728009674349043528066349 68898003627880891323024881)
        ·
          refine ⟨51673502720910668492268661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68898003627880891323024881 51673502720910668492268661)
          ·
            refine ⟨4844390880085375171150187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51673502720910668492268661 4844390880085375171150187)
            ·
              refine ⟨7266586320128062756725281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4844390880085375171150187 7266586320128062756725281)
              ·
                refine ⟨5449939740096047067543961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7266586320128062756725281 5449939740096047067543961)
                ·
                  refine ⟨4087454805072035300657971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5449939740096047067543961 4087454805072035300657971)
                  ·
                    refine ⟨6131182207608052950986957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4087454805072035300657971 6131182207608052950986957)
                    ·
                      refine ⟨2299193327853019856620109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6131182207608052950986957 2299193327853019856620109)
                      ·
                        rfl

theorem cell23_4477663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_4477663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477663 prefixEnd_4477663 := by exact prefixLift 4477663
  have htrace : WordTrace (prefixWord ++ tailWord_4477663) baseStart_4477663 baseEnd_4477663 := by
    simpa [prefixWord, tailWord_4477663, baseEnd_4477663] using wordTrace_append hprefix tailTrace_4477663
  have hstable : (prefixWord ++ tailWord_4477663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477663).length < 2 ^ (prefixWord ++ tailWord_4477663).sum := by decide
  have hdescent : baseEnd_4477663 < baseStart_4477663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477703 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4477703 : Nat := 118140960795 + 4477703 * 2 ^ 59
def prefixEnd_4477703 : Nat := 4983230072969 + 3 ^ 40 * 4477703 * 2
def baseEnd_4477703 : Nat := 2299213867079199700119925

theorem tailTrace_4477703 : CollatzResearch.WordTrace tailWord_4477703 prefixEnd_4477703 2299213867079199700119925 := by
  unfold tailWord_4477703
  simp only [CollatzResearch.WordTrace]
  refine ⟨163315245297054236634181763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108876830198036157756121175 163315245297054236634181763)
  ·
    refine ⟨244972867945581354951272645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163315245297054236634181763 244972867945581354951272645)
    ·
      refine ⟨45932412739796504053363621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244972867945581354951272645 45932412739796504053363621)
      ·
        refine ⟨8612327388711844510005679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45932412739796504053363621 8612327388711844510005679)
        ·
          refine ⟨12918491083067766765008519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8612327388711844510005679 12918491083067766765008519)
          ·
            refine ⟨19377736624601650147512779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12918491083067766765008519 19377736624601650147512779)
            ·
              refine ⟨29066604936902475221269169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19377736624601650147512779 29066604936902475221269169)
              ·
                refine ⟨21799953702676856415951877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29066604936902475221269169 21799953702676856415951877)
                ·
                  refine ⟨4087491319251910577990977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21799953702676856415951877 4087491319251910577990977)
                  ·
                    refine ⟨3065618489438932933493233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4087491319251910577990977 3065618489438932933493233)
                    ·
                      refine ⟨2299213867079199700119925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3065618489438932933493233 2299213867079199700119925)
                      ·
                        rfl

theorem cell23_4477703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4477703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477703 prefixEnd_4477703 := by exact prefixLift 4477703
  have htrace : WordTrace (prefixWord ++ tailWord_4477703) baseStart_4477703 baseEnd_4477703 := by
    simpa [prefixWord, tailWord_4477703, baseEnd_4477703] using wordTrace_append hprefix tailTrace_4477703
  have hstable : (prefixWord ++ tailWord_4477703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477703).length < 2 ^ (prefixWord ++ tailWord_4477703).sum := by decide
  have hdescent : baseEnd_4477703 < baseStart_4477703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477813 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4477813 : Nat := 118140960795 + 4477813 * 2 ^ 59
def prefixEnd_4477813 : Nat := 4983230072969 + 3 ^ 40 * 4477813 * 2
def baseEnd_4477813 : Nat := 2299270349951194269744419

theorem tailTrace_4477813 : CollatzResearch.WordTrace tailWord_4477813 prefixEnd_4477813 2299270349951194269744419 := by
  unfold tailWord_4477813
  simp only [CollatzResearch.WordTrace]
  refine ⟨163319257326655725420686093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108879504884437150280457395 163319257326655725420686093)
  ·
    refine ⟨61244721497495897032757285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163319257326655725420686093 61244721497495897032757285)
    ·
      refine ⟨11483385280780480693641991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61244721497495897032757285 11483385280780480693641991)
      ·
        refine ⟨17225077921170721040462987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11483385280780480693641991 17225077921170721040462987)
        ·
          refine ⟨25837616881756081560694481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17225077921170721040462987 25837616881756081560694481)
          ·
            refine ⟨19378212661317061170520861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25837616881756081560694481 19378212661317061170520861)
            ·
              refine ⟨7266829747993897938945323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19378212661317061170520861 7266829747993897938945323)
              ·
                refine ⟨10900244621990846908417985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7266829747993897938945323 10900244621990846908417985)
                ·
                  refine ⟨8175183466493135181313489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10900244621990846908417985 8175183466493135181313489)
                  ·
                    refine ⟨6131387599869851385985117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8175183466493135181313489 6131387599869851385985117)
                    ·
                      refine ⟨2299270349951194269744419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6131387599869851385985117 2299270349951194269744419)
                      ·
                        rfl

theorem cell23_4477813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4477813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477813 prefixEnd_4477813 := by exact prefixLift 4477813
  have htrace : WordTrace (prefixWord ++ tailWord_4477813) baseStart_4477813 baseEnd_4477813 := by
    simpa [prefixWord, tailWord_4477813, baseEnd_4477813] using wordTrace_append hprefix tailTrace_4477813
  have hstable : (prefixWord ++ tailWord_4477813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477813).length < 2 ^ (prefixWord ++ tailWord_4477813).sum := by decide
  have hdescent : baseEnd_4477813 < baseStart_4477813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477901 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 6]
def baseStart_4477901 : Nat := 118140960795 + 4477901 * 2 ^ 59
def prefixEnd_4477901 : Nat := 4983230072969 + 3 ^ 40 * 4477901 * 2
def baseEnd_4477901 : Nat := 255479504027643325049335

theorem tailTrace_4477901 : CollatzResearch.WordTrace tailWord_4477901 prefixEnd_4477901 255479504027643325049335 := by
  unfold tailWord_4477901
  simp only [CollatzResearch.WordTrace]
  refine ⟨163322466950336916449889557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108881644633557944299926371 163322466950336916449889557)
  ·
    refine ⟨7655740638297042958588573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163322466950336916449889557 7655740638297042958588573)
    ·
      refine ⟨2870902739361391109470715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7655740638297042958588573 2870902739361391109470715)
      ·
        refine ⟨4306354109042086664206073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2870902739361391109470715 4306354109042086664206073)
        ·
          refine ⟨3229765581781564998154555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4306354109042086664206073 3229765581781564998154555)
          ·
            refine ⟨4844648372672347497231833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229765581781564998154555 4844648372672347497231833)
            ·
              refine ⟨3633486279504260622923875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4844648372672347497231833 3633486279504260622923875)
              ·
                refine ⟨5450229419256390934385813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3633486279504260622923875 5450229419256390934385813)
                ·
                  refine ⟨255479504027643325049335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5450229419256390934385813 255479504027643325049335)
                  ·
                    rfl

theorem cell23_4477901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_4477901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477901 prefixEnd_4477901 := by exact prefixLift 4477901
  have htrace : WordTrace (prefixWord ++ tailWord_4477901) baseStart_4477901 baseEnd_4477901 := by
    simpa [prefixWord, tailWord_4477901, baseEnd_4477901] using wordTrace_append hprefix tailTrace_4477901
  have hstable : (prefixWord ++ tailWord_4477901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477901).length < 2 ^ (prefixWord ++ tailWord_4477901).sum := by decide
  have hdescent : baseEnd_4477901 < baseStart_4477901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477906 : List Nat := [3, 2, 2, 3, 1, 1, 1, 10]
def baseStart_4477906 : Nat := 118140960795 + 4477906 * 2 ^ 59
def prefixEnd_4477906 : Nat := 4983230072969 + 3 ^ 40 * 4477906 * 2
def baseEnd_4477906 : Nat := 85159929764891200217833

theorem tailTrace_4477906 : CollatzResearch.WordTrace tailWord_4477906 prefixEnd_4477906 85159929764891200217833 := by
  unfold tailWord_4477906
  simp only [CollatzResearch.WordTrace]
  refine ⟨40830662328829700575955393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108881766210212534869214381 40830662328829700575955393)
  ·
    refine ⟨30622996746622275431966545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40830662328829700575955393 30622996746622275431966545)
    ·
      refine ⟨22967247559966706573974909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30622996746622275431966545 22967247559966706573974909)
      ·
        refine ⟨8612717834987514965240591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22967247559966706573974909 8612717834987514965240591)
        ·
          refine ⟨12919076752481272447860887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8612717834987514965240591 12919076752481272447860887)
          ·
            refine ⟨19378615128721908671791331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12919076752481272447860887 19378615128721908671791331)
            ·
              refine ⟨29067922693082863007686997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19378615128721908671791331 29067922693082863007686997)
              ·
                refine ⟨85159929764891200217833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29067922693082863007686997 85159929764891200217833)
                ·
                  rfl

theorem cell23_4477906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 10].length) (baseStart_4477906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477906 prefixEnd_4477906 := by exact prefixLift 4477906
  have htrace : WordTrace (prefixWord ++ tailWord_4477906) baseStart_4477906 baseEnd_4477906 := by
    simpa [prefixWord, tailWord_4477906, baseEnd_4477906] using wordTrace_append hprefix tailTrace_4477906
  have hstable : (prefixWord ++ tailWord_4477906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477906).length < 2 ^ (prefixWord ++ tailWord_4477906).sum := by decide
  have hdescent : baseEnd_4477906 < baseStart_4477906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477940 : List Nat := [2, 6, 2, 1, 12]
def baseStart_4477940 : Nat := 118140960795 + 4477940 * 2 ^ 59
def prefixEnd_4477940 : Nat := 4983230072969 + 3 ^ 40 * 4477940 * 2
def baseEnd_4477940 : Nat := 3154095421117030552615

theorem tailTrace_4477940 : CollatzResearch.WordTrace tailWord_4477940 prefixEnd_4477940 3154095421117030552615 := by
  unfold tailWord_4477940
  simp only [CollatzResearch.WordTrace]
  refine ⟨81661944698597813055279637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108882592931463750740372849 81661944698597813055279637)
  ·
    refine ⟨3827903657746772486966233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81661944698597813055279637 3827903657746772486966233)
    ·
      refine ⟨2870927743310079365224675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3827903657746772486966233 2870927743310079365224675)
      ·
        refine ⟨4306391614965119047837013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2870927743310079365224675 4306391614965119047837013)
        ·
          refine ⟨3154095421117030552615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4306391614965119047837013 3154095421117030552615)
          ·
            rfl

theorem cell23_4477940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 12].length) (baseStart_4477940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477940 prefixEnd_4477940 := by exact prefixLift 4477940
  have htrace : WordTrace (prefixWord ++ tailWord_4477940) baseStart_4477940 baseEnd_4477940 := by
    simpa [prefixWord, tailWord_4477940, baseEnd_4477940] using wordTrace_append hprefix tailTrace_4477940
  have hstable : (prefixWord ++ tailWord_4477940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477940).length < 2 ^ (prefixWord ++ tailWord_4477940).sum := by decide
  have hdescent : baseEnd_4477940 < baseStart_4477940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4477966 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_4477966 : Nat := 118140960795 + 4477966 * 2 ^ 59
def prefixEnd_4477966 : Nat := 4983230072969 + 3 ^ 40 * 4477966 * 2
def baseEnd_4477966 : Nat := 766449637497110723710405

theorem tailTrace_4477966 : CollatzResearch.WordTrace tailWord_4477966 prefixEnd_4477966 766449637497110723710405 := by
  unfold tailWord_4477966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20415604711887679068875719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108883225130067621700670501 20415604711887679068875719)
  ·
    refine ⟨30623407067831518603313579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20415604711887679068875719 30623407067831518603313579)
    ·
      refine ⟨45935110601747277904970369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30623407067831518603313579 45935110601747277904970369)
      ·
        refine ⟨34451332951310458428727777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45935110601747277904970369 34451332951310458428727777)
        ·
          refine ⟨25838499713482843821545833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34451332951310458428727777 25838499713482843821545833)
          ·
            refine ⟨19378874785112132866159375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25838499713482843821545833 19378874785112132866159375)
            ·
              refine ⟨29068312177668199299239063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19378874785112132866159375 29068312177668199299239063)
              ·
                refine ⟨43602468266502298948858595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29068312177668199299239063 43602468266502298948858595)
                ·
                  refine ⟨65403702399753448423287893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43602468266502298948858595 65403702399753448423287893)
                  ·
                    refine ⟨766449637497110723710405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65403702399753448423287893 766449637497110723710405)
                    ·
                      rfl

theorem cell23_4477966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_4477966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4477966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4477966 prefixEnd_4477966 := by exact prefixLift 4477966
  have htrace : WordTrace (prefixWord ++ tailWord_4477966) baseStart_4477966 baseEnd_4477966 := by
    simpa [prefixWord, tailWord_4477966, baseEnd_4477966] using wordTrace_append hprefix tailTrace_4477966
  have hstable : (prefixWord ++ tailWord_4477966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4477966).length < 2 ^ (prefixWord ++ tailWord_4477966).sum := by decide
  have hdescent : baseEnd_4477966 < baseStart_4477966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4477966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478013 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 7]
def baseStart_4478013 : Nat := 118140960795 + 4478013 * 2 ^ 59
def prefixEnd_4478013 : Nat := 4983230072969 + 3 ^ 40 * 4478013 * 2
def baseEnd_4478013 : Nat := 255485894009121498582611

theorem tailTrace_4478013 : CollatzResearch.WordTrace tailWord_4478013 prefixEnd_4478013 255485894009121498582611 := by
  unfold tailWord_4478013
  simp only [CollatzResearch.WordTrace]
  refine ⟨163326551925931159577966693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108884367950620773051977795 163326551925931159577966693)
  ·
    refine ⟨30623728486112092420868755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163326551925931159577966693 30623728486112092420868755)
    ·
      refine ⟨45935592729168138631303133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30623728486112092420868755 45935592729168138631303133)
      ·
        refine ⟨17225847273438051986738675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45935592729168138631303133 17225847273438051986738675)
        ·
          refine ⟨25838770910157077980108013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17225847273438051986738675 25838770910157077980108013)
          ·
            refine ⟨9689539091308904242540505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25838770910157077980108013 9689539091308904242540505)
            ·
              refine ⟨7267154318481678181905379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9689539091308904242540505 7267154318481678181905379)
              ·
                refine ⟨10900731477722517272858069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7267154318481678181905379 10900731477722517272858069)
                ·
                  refine ⟨255485894009121498582611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10900731477722517272858069 255485894009121498582611)
                  ·
                    rfl

theorem cell23_4478013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_4478013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478013 prefixEnd_4478013 := by exact prefixLift 4478013
  have htrace : WordTrace (prefixWord ++ tailWord_4478013) baseStart_4478013 baseEnd_4478013 := by
    simpa [prefixWord, tailWord_4478013, baseEnd_4478013] using wordTrace_append hprefix tailTrace_4478013
  have hstable : (prefixWord ++ tailWord_4478013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478013).length < 2 ^ (prefixWord ++ tailWord_4478013).sum := by decide
  have hdescent : baseEnd_4478013 < baseStart_4478013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478023 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_4478023 : Nat := 118140960795 + 4478023 * 2 ^ 59
def prefixEnd_4478023 : Nat := 4983230072969 + 3 ^ 40 * 4478023 * 2
def baseEnd_4478023 : Nat := 2299378180888638448118453

theorem tailTrace_4478023 : CollatzResearch.WordTrace tailWord_4478023 prefixEnd_4478023 2299378180888638448118453 := by
  unfold tailWord_4478023
  simp only [CollatzResearch.WordTrace]
  refine ⟨163326916655894931285830723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108884611103929954190553815 163326916655894931285830723)
  ·
    refine ⟨244990374983842396928746085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163326916655894931285830723 244990374983842396928746085)
    ·
      refine ⟨45935695309470449424139891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244990374983842396928746085 45935695309470449424139891)
      ·
        refine ⟨68903542964205674136209837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45935695309470449424139891 68903542964205674136209837)
        ·
          refine ⟨25838828611577127801078689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68903542964205674136209837 25838828611577127801078689)
          ·
            refine ⟨19379121458682845850809017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25838828611577127801078689 19379121458682845850809017)
            ·
              refine ⟨14534341094012134388106763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19379121458682845850809017 14534341094012134388106763)
              ·
                refine ⟨21801511641018201582160145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14534341094012134388106763 21801511641018201582160145)
                ·
                  refine ⟨16351133730763651186620109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21801511641018201582160145 16351133730763651186620109)
                  ·
                    refine ⟨6131675149036369194982541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16351133730763651186620109 6131675149036369194982541)
                    ·
                      refine ⟨2299378180888638448118453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6131675149036369194982541 2299378180888638448118453)
                      ·
                        rfl

theorem cell23_4478023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_4478023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478023 prefixEnd_4478023 := by exact prefixLift 4478023
  have htrace : WordTrace (prefixWord ++ tailWord_4478023) baseStart_4478023 baseEnd_4478023 := by
    simpa [prefixWord, tailWord_4478023, baseEnd_4478023] using wordTrace_append hprefix tailTrace_4478023
  have hstable : (prefixWord ++ tailWord_4478023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478023).length < 2 ^ (prefixWord ++ tailWord_4478023).sum := by decide
  have hdescent : baseEnd_4478023 < baseStart_4478023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478026 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_4478026 : Nat := 118140960795 + 4478026 * 2 ^ 59
def prefixEnd_4478026 : Nat := 4983230072969 + 3 ^ 40 * 4478026 * 2
def baseEnd_4478026 : Nat := 766459907110200645460313

theorem tailTrace_4478026 : CollatzResearch.WordTrace tailWord_4478026 prefixEnd_4478026 766459907110200645460313 := by
  unfold tailWord_4478026
  simp only [CollatzResearch.WordTrace]
  refine ⟨40831756518721015699547483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108884684049922708532126621 40831756518721015699547483)
  ·
    refine ⟨61247634778081523549321225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40831756518721015699547483 61247634778081523549321225)
    ·
      refine ⟨45935726083561142661990919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61247634778081523549321225 45935726083561142661990919)
      ·
        refine ⟨68903589125341713992986379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45935726083561142661990919 68903589125341713992986379)
        ·
          refine ⟨103355383688012570989479569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68903589125341713992986379 103355383688012570989479569)
          ·
            refine ⟨77516537766009428242109677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103355383688012570989479569 77516537766009428242109677)
            ·
              refine ⟨29068701662253535590791129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77516537766009428242109677 29068701662253535590791129)
              ·
                refine ⟨21801526246690151693093347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29068701662253535590791129 21801526246690151693093347)
                ·
                  refine ⟨32702289370035227539640021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21801526246690151693093347 32702289370035227539640021)
                  ·
                    refine ⟨766459907110200645460313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32702289370035227539640021 766459907110200645460313)
                    ·
                      rfl

theorem cell23_4478026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_4478026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478026 prefixEnd_4478026 := by exact prefixLift 4478026
  have htrace : WordTrace (prefixWord ++ tailWord_4478026) baseStart_4478026 baseEnd_4478026 := by
    simpa [prefixWord, tailWord_4478026, baseEnd_4478026] using wordTrace_append hprefix tailTrace_4478026
  have hstable : (prefixWord ++ tailWord_4478026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478026).length < 2 ^ (prefixWord ++ tailWord_4478026).sum := by decide
  have hdescent : baseEnd_4478026 < baseStart_4478026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478033 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 2, 5, 2]
def baseStart_4478033 : Nat := 118140960795 + 4478033 * 2 ^ 59
def prefixEnd_4478033 : Nat := 4983230072969 + 3 ^ 40 * 4478033 * 2
def baseEnd_4478033 : Nat := 2299383315695183408993407

theorem tailTrace_4478033 : CollatzResearch.WordTrace tailWord_4478033 prefixEnd_4478033 2299383315695183408993407 := by
  unfold tailWord_4478033
  simp only [CollatzResearch.WordTrace]
  refine ⟨163327281385858702993694753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108884854257239135329129835 163327281385858702993694753)
  ·
    refine ⟨122495461039394027245271065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163327281385858702993694753 122495461039394027245271065)
    ·
      refine ⟨91871595779545520433953299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122495461039394027245271065 91871595779545520433953299)
      ·
        refine ⟨137807393669318280650929949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91871595779545520433953299 137807393669318280650929949)
        ·
          refine ⟨51677772625994355244098731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137807393669318280650929949 51677772625994355244098731)
          ·
            refine ⟨77516658938991532866148097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51677772625994355244098731 77516658938991532866148097)
            ·
              refine ⟨58137494204243649649611073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77516658938991532866148097 58137494204243649649611073)
              ·
                refine ⟨43603120653182737237208305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58137494204243649649611073 43603120653182737237208305)
                ·
                  refine ⟨32702340489887052927906229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43603120653182737237208305 32702340489887052927906229)
                  ·
                    refine ⟨3065844420926911211991209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32702340489887052927906229 3065844420926911211991209)
                    ·
                      refine ⟨2299383315695183408993407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3065844420926911211991209 2299383315695183408993407)
                      ·
                        rfl

theorem cell23_4478033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_4478033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478033 prefixEnd_4478033 := by exact prefixLift 4478033
  have htrace : WordTrace (prefixWord ++ tailWord_4478033) baseStart_4478033 baseEnd_4478033 := by
    simpa [prefixWord, tailWord_4478033, baseEnd_4478033] using wordTrace_append hprefix tailTrace_4478033
  have hstable : (prefixWord ++ tailWord_4478033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478033).length < 2 ^ (prefixWord ++ tailWord_4478033).sum := by decide
  have hdescent : baseEnd_4478033 < baseStart_4478033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478063 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_4478063 : Nat := 118140960795 + 4478063 * 2 ^ 59
def prefixEnd_4478063 : Nat := 4983230072969 + 3 ^ 40 * 4478063 * 2
def baseEnd_4478063 : Nat := 2299398720114818291618269

theorem tailTrace_4478063 : CollatzResearch.WordTrace tailWord_4478063 prefixEnd_4478063 2299398720114818291618269 := by
  unfold tailWord_4478063
  simp only [CollatzResearch.WordTrace]
  refine ⟨163328375575750018117286843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108885583717166678744857895 163328375575750018117286843)
  ·
    refine ⟨244992563363625027175930265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163328375575750018117286843 244992563363625027175930265)
    ·
      refine ⟨183744422522718770381947699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244992563363625027175930265 183744422522718770381947699)
      ·
        refine ⟨275616633784078155572921549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183744422522718770381947699 275616633784078155572921549)
        ·
          refine ⟨103356237669029308339845581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275616633784078155572921549 103356237669029308339845581)
          ·
            refine ⟨38758589125885990627442093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103356237669029308339845581 38758589125885990627442093)
            ·
              refine ⟨14534470922207246485290785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38758589125885990627442093 14534470922207246485290785)
              ·
                refine ⟨10900853191655434863968089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14534470922207246485290785 10900853191655434863968089)
                ·
                  refine ⟨8175639893741576147976067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10900853191655434863968089 8175639893741576147976067)
                  ·
                    refine ⟨12263459840612364221964101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8175639893741576147976067 12263459840612364221964101)
                    ·
                      refine ⟨2299398720114818291618269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12263459840612364221964101 2299398720114818291618269)
                      ·
                        rfl

theorem cell23_4478063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_4478063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478063 prefixEnd_4478063 := by exact prefixLift 4478063
  have htrace : WordTrace (prefixWord ++ tailWord_4478063) baseStart_4478063 baseEnd_4478063 := by
    simpa [prefixWord, tailWord_4478063, baseEnd_4478063] using wordTrace_append hprefix tailTrace_4478063
  have hstable : (prefixWord ++ tailWord_4478063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478063).length < 2 ^ (prefixWord ++ tailWord_4478063).sum := by decide
  have hdescent : baseEnd_4478063 < baseStart_4478063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478083 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 3]
def baseStart_4478083 : Nat := 118140960795 + 4478083 * 2 ^ 59
def prefixEnd_4478083 : Nat := 4983230072969 + 3 ^ 40 * 4478083 * 2
def baseEnd_4478083 : Nat := 2299408989727908213368177

theorem tailTrace_4478083 : CollatzResearch.WordTrace tailWord_4478083 prefixEnd_4478083 2299408989727908213368177 := by
  unfold tailWord_4478083
  simp only [CollatzResearch.WordTrace]
  refine ⟨163329105035677561533014903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108886070023785041022009935 163329105035677561533014903)
  ·
    refine ⟨244993657553516342299522355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163329105035677561533014903 244993657553516342299522355)
    ·
      refine ⟨367490486330274513449283533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244993657553516342299522355 367490486330274513449283533)
      ·
        refine ⟨137808932373852942543481325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367490486330274513449283533 137808932373852942543481325)
        ·
          refine ⟨51678349640194853453805497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137808932373852942543481325 51678349640194853453805497)
          ·
            refine ⟨38758762230146140090354123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51678349640194853453805497 38758762230146140090354123)
            ·
              refine ⟨58138143345219210135531185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38758762230146140090354123 58138143345219210135531185)
              ·
                refine ⟨43603607508914407601648389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58138143345219210135531185 43603607508914407601648389)
                ·
                  refine ⟨8175676407921451425309073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43603607508914407601648389 8175676407921451425309073)
                  ·
                    refine ⟨6131757305941088568981805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8175676407921451425309073 6131757305941088568981805)
                    ·
                      refine ⟨2299408989727908213368177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6131757305941088568981805 2299408989727908213368177)
                      ·
                        rfl

theorem cell23_4478083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_4478083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478083 prefixEnd_4478083 := by exact prefixLift 4478083
  have htrace : WordTrace (prefixWord ++ tailWord_4478083) baseStart_4478083 baseEnd_4478083 := by
    simpa [prefixWord, tailWord_4478083, baseEnd_4478083] using wordTrace_append hprefix tailTrace_4478083
  have hstable : (prefixWord ++ tailWord_4478083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478083).length < 2 ^ (prefixWord ++ tailWord_4478083).sum := by decide
  have hdescent : baseEnd_4478083 < baseStart_4478083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478163 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 6, 4]
def baseStart_4478163 : Nat := 118140960795 + 4478163 * 2 ^ 59
def prefixEnd_4478163 : Nat := 4983230072969 + 3 ^ 40 * 4478163 * 2
def baseEnd_4478163 : Nat := 766483356060089300122603

theorem tailTrace_4478163 : CollatzResearch.WordTrace tailWord_4478163 prefixEnd_4478163 766483356060089300122603 := by
  unfold tailWord_4478163
  simp only [CollatzResearch.WordTrace]
  refine ⟨163332022875387735195927143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108888015250258490130618095 163332022875387735195927143)
  ·
    refine ⟨244998034313081602793890715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163332022875387735195927143 244998034313081602793890715)
    ·
      refine ⟨367497051469622404190836073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244998034313081602793890715 367497051469622404190836073)
      ·
        refine ⟨275622788602216803143127055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367497051469622404190836073 275622788602216803143127055)
        ·
          refine ⟨413434182903325204714690583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275622788602216803143127055 413434182903325204714690583)
          ·
            refine ⟨620151274354987807072035875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413434182903325204714690583 620151274354987807072035875)
            ·
              refine ⟨930226911532481710608053813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620151274354987807072035875 930226911532481710608053813)
              ·
                refine ⟨87208772956170160369505045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 930226911532481710608053813 87208772956170160369505045)
                ·
                  refine ⟨4087911232320476267320549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87208772956170160369505045 4087911232320476267320549)
                  ·
                    refine ⟨766483356060089300122603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4087911232320476267320549 766483356060089300122603)
                    ·
                      rfl

theorem cell23_4478163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 4].length) (baseStart_4478163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478163 prefixEnd_4478163 := by exact prefixLift 4478163
  have htrace : WordTrace (prefixWord ++ tailWord_4478163) baseStart_4478163 baseEnd_4478163 := by
    simpa [prefixWord, tailWord_4478163, baseEnd_4478163] using wordTrace_append hprefix tailTrace_4478163
  have hstable : (prefixWord ++ tailWord_4478163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478163).length < 2 ^ (prefixWord ++ tailWord_4478163).sum := by decide
  have hdescent : baseEnd_4478163 < baseStart_4478163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478187 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 3, 2, 2]
def baseStart_4478187 : Nat := 118140960795 + 4478187 * 2 ^ 59
def prefixEnd_4478187 : Nat := 4983230072969 + 3 ^ 40 * 4478187 * 2
def baseEnd_4478187 : Nat := 2299462391715975806467699

theorem tailTrace_4478187 : CollatzResearch.WordTrace tailWord_4478187 prefixEnd_4478187 2299462391715975806467699 := by
  unfold tailWord_4478187
  simp only [CollatzResearch.WordTrace]
  refine ⟨163332898227300787294800815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108888598818200524863200543 163332898227300787294800815)
  ·
    refine ⟨244999347340951180942201223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163332898227300787294800815 244999347340951180942201223)
    ·
      refine ⟨367499021011426771413301835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244999347340951180942201223 367499021011426771413301835)
      ·
        refine ⟨551248531517140157119952753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367499021011426771413301835 551248531517140157119952753)
        ·
          refine ⟨413436398637855117839964565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551248531517140157119952753 413436398637855117839964565)
          ·
            refine ⟨19379831186149458648748339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 413436398637855117839964565 19379831186149458648748339)
            ·
              refine ⟨29069746779224187973122509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19379831186149458648748339 29069746779224187973122509)
              ·
                refine ⟨10901155042209070489920941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29069746779224187973122509 10901155042209070489920941)
                ·
                  refine ⟨4087933140828401433720353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10901155042209070489920941 4087933140828401433720353)
                  ·
                    refine ⟨3065949855621301075290265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4087933140828401433720353 3065949855621301075290265)
                    ·
                      refine ⟨2299462391715975806467699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3065949855621301075290265 2299462391715975806467699)
                      ·
                        rfl

theorem cell23_4478187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 2, 2].length) (baseStart_4478187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478187 prefixEnd_4478187 := by exact prefixLift 4478187
  have htrace : WordTrace (prefixWord ++ tailWord_4478187) baseStart_4478187 baseEnd_4478187 := by
    simpa [prefixWord, tailWord_4478187, baseEnd_4478187] using wordTrace_append hprefix tailTrace_4478187
  have hstable : (prefixWord ++ tailWord_4478187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478187).length < 2 ^ (prefixWord ++ tailWord_4478187).sum := by decide
  have hdescent : baseEnd_4478187 < baseStart_4478187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478190 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_4478190 : Nat := 118140960795 + 4478190 * 2 ^ 59
def prefixEnd_4478190 : Nat := 4983230072969 + 3 ^ 40 * 4478190 * 2
def baseEnd_4478190 : Nat := 2299463932157939294730185

theorem tailTrace_4478190 : CollatzResearch.WordTrace tailWord_4478190 prefixEnd_4478190 2299463932157939294730185 := by
  unfold tailWord_4478190
  simp only [CollatzResearch.WordTrace]
  refine ⟨20416625955786239850895003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108888671764193279204773349 20416625955786239850895003)
  ·
    refine ⟨30624938933679359776342505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20416625955786239850895003 30624938933679359776342505)
    ·
      refine ⟨22968704200259519832256879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30624938933679359776342505 22968704200259519832256879)
      ·
        refine ⟨34453056300389279748385319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22968704200259519832256879 34453056300389279748385319)
        ·
          refine ⟨51679584450583919622577979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34453056300389279748385319 51679584450583919622577979)
          ·
            refine ⟨77519376675875879433866969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51679584450583919622577979 77519376675875879433866969)
            ·
              refine ⟨58139532506906909575400227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77519376675875879433866969 58139532506906909575400227)
              ·
                refine ⟨87209298760360364363100341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58139532506906909575400227 87209298760360364363100341)
                ·
                  refine ⟨8175871758783784159040657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87209298760360364363100341 8175871758783784159040657)
                  ·
                    refine ⟨6131903819087838119280493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8175871758783784159040657 6131903819087838119280493)
                    ·
                      refine ⟨2299463932157939294730185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6131903819087838119280493 2299463932157939294730185)
                      ·
                        rfl

theorem cell23_4478190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_4478190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478190 prefixEnd_4478190 := by exact prefixLift 4478190
  have htrace : WordTrace (prefixWord ++ tailWord_4478190) baseStart_4478190 baseEnd_4478190 := by
    simpa [prefixWord, tailWord_4478190, baseEnd_4478190] using wordTrace_append hprefix tailTrace_4478190
  have hstable : (prefixWord ++ tailWord_4478190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478190).length < 2 ^ (prefixWord ++ tailWord_4478190).sum := by decide
  have hdescent : baseEnd_4478190 < baseStart_4478190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478207 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 3]
def baseStart_4478207 : Nat := 118140960795 + 4478207 * 2 ^ 59
def prefixEnd_4478207 : Nat := 4983230072969 + 3 ^ 40 * 4478207 * 2
def baseEnd_4478207 : Nat := 2299472661329065728217607

theorem tailTrace_4478207 : CollatzResearch.WordTrace tailWord_4478207 prefixEnd_4478207 2299472661329065728217607 := by
  unfold tailWord_4478207
  simp only [CollatzResearch.WordTrace]
  refine ⟨163333627687228330710528875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108889085124818887140352583 163333627687228330710528875)
  ·
    refine ⟨245000441530842496065793313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163333627687228330710528875 245000441530842496065793313)
    ·
      refine ⟨183750331148131872049344985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245000441530842496065793313 183750331148131872049344985)
      ·
        refine ⟨137812748361098904037008739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183750331148131872049344985 137812748361098904037008739)
        ·
          refine ⟨206719122541648356055513109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137812748361098904037008739 206719122541648356055513109)
          ·
            refine ⟨9689958869139766690102177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206719122541648356055513109 9689958869139766690102177)
            ·
              refine ⟨7267469151854825017576633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9689958869139766690102177 7267469151854825017576633)
              ·
                refine ⟨5450601863891118763182475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7267469151854825017576633 5450601863891118763182475)
                ·
                  refine ⟨8175902795836678144773713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5450601863891118763182475 8175902795836678144773713)
                  ·
                    refine ⟨6131927096877508608580285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8175902795836678144773713 6131927096877508608580285)
                    ·
                      refine ⟨2299472661329065728217607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6131927096877508608580285 2299472661329065728217607)
                      ·
                        rfl

theorem cell23_4478207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_4478207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478207 prefixEnd_4478207 := by exact prefixLift 4478207
  have htrace : WordTrace (prefixWord ++ tailWord_4478207) baseStart_4478207 baseEnd_4478207 := by
    simpa [prefixWord, tailWord_4478207, baseEnd_4478207] using wordTrace_append hprefix tailTrace_4478207
  have hstable : (prefixWord ++ tailWord_4478207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478207).length < 2 ^ (prefixWord ++ tailWord_4478207).sum := by decide
  have hdescent : baseEnd_4478207 < baseStart_4478207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478277 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 6, 2, 2]
def baseStart_4478277 : Nat := 118140960795 + 4478277 * 2 ^ 59
def prefixEnd_4478277 : Nat := 4983230072969 + 3 ^ 40 * 4478277 * 2
def baseEnd_4478277 : Nat := 2299508604974880454342285

theorem tailTrace_4478277 : CollatzResearch.WordTrace tailWord_4478277 prefixEnd_4478277 2299508604974880454342285 := by
  unfold tailWord_4478277
  simp only [CollatzResearch.WordTrace]
  refine ⟨163336180796974732665577085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108890787197983155110384723 163336180796974732665577085)
  ·
    refine ⟨61251067798865524749591407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163336180796974732665577085 61251067798865524749591407)
    ·
      refine ⟨91876601698298287124387111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61251067798865524749591407 91876601698298287124387111)
      ·
        refine ⟨137814902547447430686580667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91876601698298287124387111 137814902547447430686580667)
        ·
          refine ⟨206722353821171146029871001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137814902547447430686580667 206722353821171146029871001)
          ·
            refine ⟨155041765365878359522403251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206722353821171146029871001 155041765365878359522403251)
            ·
              refine ⟨232562648048817539283604877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155041765365878359522403251 232562648048817539283604877)
              ·
                refine ⟨87210993018306577231351829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232562648048817539283604877 87210993018306577231351829)
                ·
                  refine ⟨4088015297733120807719617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87210993018306577231351829 4088015297733120807719617)
                  ·
                    refine ⟨3066011473299840605789713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4088015297733120807719617 3066011473299840605789713)
                    ·
                      refine ⟨2299508604974880454342285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066011473299840605789713 2299508604974880454342285)
                      ·
                        rfl

theorem cell23_4478277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_4478277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478277 prefixEnd_4478277 := by exact prefixLift 4478277
  have htrace : WordTrace (prefixWord ++ tailWord_4478277) baseStart_4478277 baseEnd_4478277 := by
    simpa [prefixWord, tailWord_4478277, baseEnd_4478277] using wordTrace_append hprefix tailTrace_4478277
  have hstable : (prefixWord ++ tailWord_4478277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478277).length < 2 ^ (prefixWord ++ tailWord_4478277).sum := by decide
  have hdescent : baseEnd_4478277 < baseStart_4478277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478290 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_4478290 : Nat := 118140960795 + 4478290 * 2 ^ 59
def prefixEnd_4478290 : Nat := 4983230072969 + 3 ^ 40 * 4478290 * 2
def baseEnd_4478290 : Nat := 2299515280223388903479725

theorem tailTrace_4478290 : CollatzResearch.WordTrace tailWord_4478290 prefixEnd_4478290 2299515280223388903479725 := by
  unfold tailWord_4478290
  simp only [CollatzResearch.WordTrace]
  refine ⟨40834163736481908971450081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108891103297285090590533549 40834163736481908971450081)
  ·
    refine ⟨30625622802361431728587561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40834163736481908971450081 30625622802361431728587561)
    ·
      refine ⟨22969217101771073796440671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30625622802361431728587561 22969217101771073796440671)
      ·
        refine ⟨34453825652656610694661007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22969217101771073796440671 34453825652656610694661007)
        ·
          refine ⟨51680738478984916041991511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34453825652656610694661007 51680738478984916041991511)
          ·
            refine ⟨77521107718477374062987267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51680738478984916041991511 77521107718477374062987267)
            ·
              refine ⟨116281661577716061094480901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77521107718477374062987267 116281661577716061094480901)
              ·
                refine ⟨21802811545821761455215169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116281661577716061094480901 21802811545821761455215169)
                ·
                  refine ⟨16352108659366321091411377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21802811545821761455215169 16352108659366321091411377)
                  ·
                    refine ⟨12264081494524740818558533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16352108659366321091411377 12264081494524740818558533)
                    ·
                      refine ⟨2299515280223388903479725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12264081494524740818558533 2299515280223388903479725)
                      ·
                        rfl

theorem cell23_4478290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_4478290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478290 prefixEnd_4478290 := by exact prefixLift 4478290
  have htrace : WordTrace (prefixWord ++ tailWord_4478290) baseStart_4478290 baseEnd_4478290 := by
    simpa [prefixWord, tailWord_4478290, baseEnd_4478290] using wordTrace_append hprefix tailTrace_4478290
  have hstable : (prefixWord ++ tailWord_4478290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478290).length < 2 ^ (prefixWord ++ tailWord_4478290).sum := by decide
  have hdescent : baseEnd_4478290 < baseStart_4478290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478303 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_4478303 : Nat := 118140960795 + 4478303 * 2 ^ 59
def prefixEnd_4478303 : Nat := 4983230072969 + 3 ^ 40 * 4478303 * 2
def baseEnd_4478303 : Nat := 2299521955471897352617165

theorem tailTrace_4478303 : CollatzResearch.WordTrace tailWord_4478303 prefixEnd_4478303 2299521955471897352617165 := by
  unfold tailWord_4478303
  simp only [CollatzResearch.WordTrace]
  refine ⟨163337129094880539106023563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108891419396587026070682375 163337129094880539106023563)
  ·
    refine ⟨245005693642320808659035345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163337129094880539106023563 245005693642320808659035345)
    ·
      refine ⟨183754270231740606494276509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245005693642320808659035345 183754270231740606494276509)
      ·
        refine ⟨68907851336902727435353691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183754270231740606494276509 68907851336902727435353691)
        ·
          refine ⟨103361777005354091153030537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68907851336902727435353691 103361777005354091153030537)
          ·
            refine ⟨77521332754015568364772903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103361777005354091153030537 77521332754015568364772903)
            ·
              refine ⟨116281999131023352547159355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77521332754015568364772903 116281999131023352547159355)
              ·
                refine ⟨174422998696535028820739033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116281999131023352547159355 174422998696535028820739033)
                ·
                  refine ⟨130817249022401271615554275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174422998696535028820739033 130817249022401271615554275)
                  ·
                    refine ⟨196225873533601907423331413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 130817249022401271615554275 196225873533601907423331413)
                    ·
                      refine ⟨2299521955471897352617165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 196225873533601907423331413 2299521955471897352617165)
                      ·
                        rfl

theorem cell23_4478303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_4478303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478303 prefixEnd_4478303 := by exact prefixLift 4478303
  have htrace : WordTrace (prefixWord ++ tailWord_4478303) baseStart_4478303 baseEnd_4478303 := by
    simpa [prefixWord, tailWord_4478303, baseEnd_4478303] using wordTrace_append hprefix tailTrace_4478303
  have hstable : (prefixWord ++ tailWord_4478303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478303).length < 2 ^ (prefixWord ++ tailWord_4478303).sum := by decide
  have hdescent : baseEnd_4478303 < baseStart_4478303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478402 : List Nat := [3, 5, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4478402 : Nat := 118140960795 + 4478402 * 2 ^ 59
def prefixEnd_4478402 : Nat := 4983230072969 + 3 ^ 40 * 4478402 * 2
def baseEnd_4478402 : Nat := 255508087784076940586579

theorem tailTrace_4478402 : CollatzResearch.WordTrace tailWord_4478402 prefixEnd_4478402 255508087784076940586579 := by
  unfold tailWord_4478402
  simp only [CollatzResearch.WordTrace]
  refine ⟨40835184980380469753469365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108893826614347919342584973 40835184980380469753469365)
  ·
    refine ⟨3828298591910669039387753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40835184980380469753469365 3828298591910669039387753)
    ·
      refine ⟨2871223943933001779540815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3828298591910669039387753 2871223943933001779540815)
      ·
        refine ⟨4306835915899502669311223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871223943933001779540815 4306835915899502669311223)
        ·
          refine ⟨6460253873849254003966835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306835915899502669311223 6460253873849254003966835)
          ·
            refine ⟨9690380810773881005950253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460253873849254003966835 9690380810773881005950253)
            ·
              refine ⟨3633892804040205377231345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9690380810773881005950253 3633892804040205377231345)
              ·
                refine ⟨2725419603030154032923509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633892804040205377231345 2725419603030154032923509)
                ·
                  refine ⟨255508087784076940586579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2725419603030154032923509 255508087784076940586579)
                  ·
                    rfl

theorem cell23_4478402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4478402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478402 prefixEnd_4478402 := by exact prefixLift 4478402
  have htrace : WordTrace (prefixWord ++ tailWord_4478402) baseStart_4478402 baseEnd_4478402 := by
    simpa [prefixWord, tailWord_4478402, baseEnd_4478402] using wordTrace_append hprefix tailTrace_4478402
  have hstable : (prefixWord ++ tailWord_4478402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478402).length < 2 ^ (prefixWord ++ tailWord_4478402).sum := by decide
  have hdescent : baseEnd_4478402 < baseStart_4478402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478404 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4478404 : Nat := 118140960795 + 4478404 * 2 ^ 59
def prefixEnd_4478404 : Nat := 4983230072969 + 3 ^ 40 * 4478404 * 2
def baseEnd_4478404 : Nat := 2299573817018001457454201

theorem tailTrace_4478404 : CollatzResearch.WordTrace tailWord_4478404 prefixEnd_4478404 2299573817018001457454201 := by
  unfold tailWord_4478404
  simp only [CollatzResearch.WordTrace]
  refine ⟨81670406433757316677725133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108893875245009755570300177 81670406433757316677725133)
  ·
    refine ⟨30626402412658993754146925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81670406433757316677725133 30626402412658993754146925)
    ·
      refine ⟨11484900904747122657805097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30626402412658993754146925 11484900904747122657805097)
      ·
        refine ⟨8613675678560341993353823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11484900904747122657805097 8613675678560341993353823)
        ·
          refine ⟨12920513517840512990030735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8613675678560341993353823 12920513517840512990030735)
          ·
            refine ⟨19380770276760769485046103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12920513517840512990030735 19380770276760769485046103)
            ·
              refine ⟨29071155415141154227569155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19380770276760769485046103 29071155415141154227569155)
              ·
                refine ⟨43606733122711731341353733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29071155415141154227569155 43606733122711731341353733)
                ·
                  refine ⟨8176262460508449626503825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43606733122711731341353733 8176262460508449626503825)
                  ·
                    refine ⟨6132196845381337219877869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8176262460508449626503825 6132196845381337219877869)
                    ·
                      refine ⟨2299573817018001457454201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6132196845381337219877869 2299573817018001457454201)
                      ·
                        rfl

theorem cell23_4478404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4478404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478404 prefixEnd_4478404 := by exact prefixLift 4478404
  have htrace : WordTrace (prefixWord ++ tailWord_4478404) baseStart_4478404 baseEnd_4478404 := by
    simpa [prefixWord, tailWord_4478404, baseEnd_4478404] using wordTrace_append hprefix tailTrace_4478404
  have hstable : (prefixWord ++ tailWord_4478404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478404).length < 2 ^ (prefixWord ++ tailWord_4478404).sum := by decide
  have hdescent : baseEnd_4478404 < baseStart_4478404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478462 : List Nat := [4, 2, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_4478462 : Nat := 118140960795 + 4478462 * 2 ^ 59
def prefixEnd_4478462 : Nat := 4983230072969 + 3 ^ 40 * 4478462 * 2
def baseEnd_4478462 : Nat := 766534532965320743509645

theorem tailTrace_4478462 : CollatzResearch.WordTrace tailWord_4478462 prefixEnd_4478462 766534532965320743509645 := by
  unfold tailWord_4478462
  simp only [CollatzResearch.WordTrace]
  refine ⟨20417866037663063657632705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108895285534203006174041093 20417866037663063657632705)
  ·
    refine ⟨15313399528247297743224529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20417866037663063657632705 15313399528247297743224529)
    ·
      refine ⟨11485049646185473307418397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15313399528247297743224529 11485049646185473307418397)
      ·
        refine ⟨4306893617319552490281899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11485049646185473307418397 4306893617319552490281899)
        ·
          refine ⟨6460340425979328735422849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4306893617319552490281899 6460340425979328735422849)
          ·
            refine ⟨4845255319484496551567137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6460340425979328735422849 4845255319484496551567137)
            ·
              refine ⟨3633941489613372413675353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845255319484496551567137 3633941489613372413675353)
              ·
                refine ⟨2725456117210029310256515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633941489613372413675353 2725456117210029310256515)
                ·
                  refine ⟨4088184175815043965384773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725456117210029310256515 4088184175815043965384773)
                  ·
                    refine ⟨766534532965320743509645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4088184175815043965384773 766534532965320743509645)
                    ·
                      rfl

theorem cell23_4478462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_4478462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478462 prefixEnd_4478462 := by exact prefixLift 4478462
  have htrace : WordTrace (prefixWord ++ tailWord_4478462) baseStart_4478462 baseEnd_4478462 := by
    simpa [prefixWord, tailWord_4478462, baseEnd_4478462] using wordTrace_append hprefix tailTrace_4478462
  have hstable : (prefixWord ++ tailWord_4478462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478462).length < 2 ^ (prefixWord ++ tailWord_4478462).sum := by decide
  have hdescent : baseEnd_4478462 < baseStart_4478462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478551 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 1, 3, 2]
def baseStart_4478551 : Nat := 118140960795 + 4478551 * 2 ^ 59
def prefixEnd_4478551 : Nat := 4983230072969 + 3 ^ 40 * 4478551 * 2
def baseEnd_4478551 : Nat := 2299649298674212382316025

theorem tailTrace_4478551 : CollatzResearch.WordTrace tailWord_4478551 prefixEnd_4478551 2299649298674212382316025 := by
  unfold tailWord_4478551
  simp only [CollatzResearch.WordTrace]
  refine ⟨163346174397982077461051507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108897449598654718307367671 163346174397982077461051507)
  ·
    refine ⟨245019261596973116191577261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163346174397982077461051507 245019261596973116191577261)
    ·
      refine ⟨91882223098864918571841473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245019261596973116191577261 91882223098864918571841473)
      ·
        refine ⟨68911667324148688928881105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91882223098864918571841473 68911667324148688928881105)
        ·
          refine ⟨51683750493111516696660829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68911667324148688928881105 51683750493111516696660829)
          ·
            refine ⟨19381406434916818761247811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51683750493111516696660829 19381406434916818761247811)
            ·
              refine ⟨29072109652375228141871717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19381406434916818761247811 29072109652375228141871717)
              ·
                refine ⟨5451020559820355276600947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29072109652375228141871717 5451020559820355276600947)
                ·
                  refine ⟨8176530839730532914901421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5451020559820355276600947 8176530839730532914901421)
                  ·
                    refine ⟨3066199064898949843088033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8176530839730532914901421 3066199064898949843088033)
                    ·
                      refine ⟨2299649298674212382316025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066199064898949843088033 2299649298674212382316025)
                      ·
                        rfl

theorem cell23_4478551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_4478551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478551 prefixEnd_4478551 := by exact prefixLift 4478551
  have htrace : WordTrace (prefixWord ++ tailWord_4478551) baseStart_4478551 baseEnd_4478551 := by
    simpa [prefixWord, tailWord_4478551, baseEnd_4478551] using wordTrace_append hprefix tailTrace_4478551
  have hstable : (prefixWord ++ tailWord_4478551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478551).length < 2 ^ (prefixWord ++ tailWord_4478551).sum := by decide
  have hdescent : baseEnd_4478551 < baseStart_4478551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478567 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_4478567 : Nat := 118140960795 + 4478567 * 2 ^ 59
def prefixEnd_4478567 : Nat := 4983230072969 + 3 ^ 40 * 4478567 * 2
def baseEnd_4478567 : Nat := 2299657514364684319715951

theorem tailTrace_4478567 : CollatzResearch.WordTrace tailWord_4478567 prefixEnd_4478567 2299657514364684319715951 := by
  unfold tailWord_4478567
  simp only [CollatzResearch.WordTrace]
  refine ⟨163346757965924112193633955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108897838643949408129089303 163346757965924112193633955)
  ·
    refine ⟨245020136948886168290450933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163346757965924112193633955 245020136948886168290450933)
    ·
      refine ⟨22970637838958078277229775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245020136948886168290450933 22970637838958078277229775)
      ·
        refine ⟨34455956758437117415844663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22970637838958078277229775 34455956758437117415844663)
        ·
          refine ⟨51683935137655676123766995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34455956758437117415844663 51683935137655676123766995)
          ·
            refine ⟨77525902706483514185650493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51683935137655676123766995 77525902706483514185650493)
            ·
              refine ⟨29072213514931317819618935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77525902706483514185650493 29072213514931317819618935)
              ·
                refine ⟨43608320272396976729428403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29072213514931317819618935 43608320272396976729428403)
                ·
                  refine ⟨65412480408595465094142605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43608320272396976729428403 65412480408595465094142605)
                  ·
                    refine ⟨24529680153223299410303477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65412480408595465094142605 24529680153223299410303477)
                    ·
                      refine ⟨2299657514364684319715951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24529680153223299410303477 2299657514364684319715951)
                      ·
                        rfl

theorem cell23_4478567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_4478567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478567 prefixEnd_4478567 := by exact prefixLift 4478567
  have htrace : WordTrace (prefixWord ++ tailWord_4478567) baseStart_4478567 baseEnd_4478567 := by
    simpa [prefixWord, tailWord_4478567, baseEnd_4478567] using wordTrace_append hprefix tailTrace_4478567
  have hstable : (prefixWord ++ tailWord_4478567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478567).length < 2 ^ (prefixWord ++ tailWord_4478567).sum := by decide
  have hdescent : baseEnd_4478567 < baseStart_4478567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478568 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_4478568 : Nat := 118140960795 + 4478568 * 2 ^ 59
def prefixEnd_4478568 : Nat := 4983230072969 + 3 ^ 40 * 4478568 * 2
def baseEnd_4478568 : Nat := 2299658027845338815803447

theorem tailTrace_4478568 : CollatzResearch.WordTrace tailWord_4478568 prefixEnd_4478568 2299658027845338815803447 := by
  unfold tailWord_4478568
  simp only [CollatzResearch.WordTrace]
  refine ⟨81673397219460244682210179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108897862959280326242946905 81673397219460244682210179)
  ·
    refine ⟨122510095829190367023315269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81673397219460244682210179 122510095829190367023315269)
    ·
      refine ⟨22970642967973193816871613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122510095829190367023315269 22970642967973193816871613)
      ·
        refine ⟨8613991112989947681326855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22970642967973193816871613 8613991112989947681326855)
        ·
          refine ⟨12920986669484921521990283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8613991112989947681326855 12920986669484921521990283)
          ·
            refine ⟨19381480004227382282985425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12920986669484921521990283 19381480004227382282985425)
            ·
              refine ⟨14536110003170536712239069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19381480004227382282985425 14536110003170536712239069)
              ·
                refine ⟨5451041251188951267089651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14536110003170536712239069 5451041251188951267089651)
                ·
                  refine ⟨8176561876783426900634477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5451041251188951267089651 8176561876783426900634477)
                  ·
                    refine ⟨3066210703793785087737929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8176561876783426900634477 3066210703793785087737929)
                    ·
                      refine ⟨2299658027845338815803447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066210703793785087737929 2299658027845338815803447)
                      ·
                        rfl

theorem cell23_4478568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_4478568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478568 prefixEnd_4478568 := by exact prefixLift 4478568
  have htrace : WordTrace (prefixWord ++ tailWord_4478568) baseStart_4478568 baseEnd_4478568 := by
    simpa [prefixWord, tailWord_4478568, baseEnd_4478568] using wordTrace_append hprefix tailTrace_4478568
  have hstable : (prefixWord ++ tailWord_4478568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478568).length < 2 ^ (prefixWord ++ tailWord_4478568).sum := by decide
  have hdescent : baseEnd_4478568 < baseStart_4478568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478577 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_4478577 : Nat := 118140960795 + 4478577 * 2 ^ 59
def prefixEnd_4478577 : Nat := 4983230072969 + 3 ^ 40 * 4478577 * 2
def baseEnd_4478577 : Nat := 2299662649171229280590905

theorem tailTrace_4478577 : CollatzResearch.WordTrace tailWord_4478577 prefixEnd_4478577 2299662649171229280590905 := by
  unfold tailWord_4478577
  simp only [CollatzResearch.WordTrace]
  refine ⟨163347122695887883901497985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108898081797258589267665323 163347122695887883901497985)
  ·
    refine ⟨122510342021915912926123489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163347122695887883901497985 122510342021915912926123489)
    ·
      refine ⟨91882756516436934694592617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122510342021915912926123489 91882756516436934694592617)
      ·
        refine ⟨68912067387327701020944463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91882756516436934694592617 68912067387327701020944463)
        ·
          refine ⟨103368101080991551531416695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68912067387327701020944463 103368101080991551531416695)
          ·
            refine ⟨155052151621487327297125043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103368101080991551531416695 155052151621487327297125043)
            ·
              refine ⟨232578227432230990945687565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155052151621487327297125043 232578227432230990945687565)
              ·
                refine ⟨87216835287086621604632837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232578227432230990945687565 87216835287086621604632837)
                ·
                  refine ⟨16353156616328741550868657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87216835287086621604632837 16353156616328741550868657)
                  ·
                    refine ⟨12264867462246556163151493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16353156616328741550868657 12264867462246556163151493)
                    ·
                      refine ⟨2299662649171229280590905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12264867462246556163151493 2299662649171229280590905)
                      ·
                        rfl

theorem cell23_4478577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_4478577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478577 prefixEnd_4478577 := by exact prefixLift 4478577
  have htrace : WordTrace (prefixWord ++ tailWord_4478577) baseStart_4478577 baseEnd_4478577 := by
    simpa [prefixWord, tailWord_4478577, baseEnd_4478577] using wordTrace_append hprefix tailTrace_4478577
  have hstable : (prefixWord ++ tailWord_4478577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478577).length < 2 ^ (prefixWord ++ tailWord_4478577).sum := by decide
  have hdescent : baseEnd_4478577 < baseStart_4478577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478627 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 5]
def baseStart_4478627 : Nat := 118140960795 + 4478627 * 2 ^ 59
def prefixEnd_4478627 : Nat := 4983230072969 + 3 ^ 40 * 4478627 * 2
def baseEnd_4478627 : Nat := 2299688323203954084965675

theorem tailTrace_4478627 : CollatzResearch.WordTrace tailWord_4478627 prefixEnd_4478627 2299688323203954084965675 := by
  unfold tailWord_4478627
  simp only [CollatzResearch.WordTrace]
  refine ⟨163348946345706742440818135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108899297563804494960545423 163348946345706742440818135)
  ·
    refine ⟨245023419518560113661227203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163348946345706742440818135 245023419518560113661227203)
    ·
      refine ⟨367535129277840170491840805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245023419518560113661227203 367535129277840170491840805)
      ·
        refine ⟨68912836739595031967220151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 367535129277840170491840805 68912836739595031967220151)
        ·
          refine ⟨103369255109392547950830227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68912836739595031967220151 103369255109392547950830227)
          ·
            refine ⟨155053882664088821926245341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103369255109392547950830227 155053882664088821926245341)
            ·
              refine ⟨58145205999033308222342003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155053882664088821926245341 58145205999033308222342003)
              ·
                refine ⟨87217808998549962333513005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58145205999033308222342003 87217808998549962333513005)
                ·
                  refine ⟨32706678374456235875067377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87217808998549962333513005 32706678374456235875067377)
                  ·
                    refine ⟨24530008780842176906300533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32706678374456235875067377 24530008780842176906300533)
                    ·
                      refine ⟨2299688323203954084965675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24530008780842176906300533 2299688323203954084965675)
                      ·
                        rfl

theorem cell23_4478627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_4478627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478627 prefixEnd_4478627 := by exact prefixLift 4478627
  have htrace : WordTrace (prefixWord ++ tailWord_4478627) baseStart_4478627 baseEnd_4478627 := by
    simpa [prefixWord, tailWord_4478627, baseEnd_4478627] using wordTrace_append hprefix tailTrace_4478627
  have hstable : (prefixWord ++ tailWord_4478627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478627).length < 2 ^ (prefixWord ++ tailWord_4478627).sum := by decide
  have hdescent : baseEnd_4478627 < baseStart_4478627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478667 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 6]
def baseStart_4478667 : Nat := 118140960795 + 4478667 * 2 ^ 59
def prefixEnd_4478667 : Nat := 4983230072969 + 3 ^ 40 * 4478667 * 2
def baseEnd_4478667 : Nat := 2299708862430133928465491

theorem tailTrace_4478667 : CollatzResearch.WordTrace tailWord_4478667 prefixEnd_4478667 2299708862430133928465491 := by
  unfold tailWord_4478667
  simp only [CollatzResearch.WordTrace]
  refine ⟨163350405265561829272274255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108900270177041219514849503 163350405265561829272274255)
  ·
    refine ⟨245025607898342743908411383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163350405265561829272274255 245025607898342743908411383)
    ·
      refine ⟨367538411847514115862617075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245025607898342743908411383 367538411847514115862617075)
      ·
        refine ⟨551307617771271173793925613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367538411847514115862617075 551307617771271173793925613)
        ·
          refine ⟨206740356664226690172722105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 551307617771271173793925613 206740356664226690172722105)
          ·
            refine ⟨155055267498170017629541579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206740356664226690172722105 155055267498170017629541579)
            ·
              refine ⟨232582901247255026444312369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155055267498170017629541579 232582901247255026444312369)
              ·
                refine ⟨174437175935441269833234277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232582901247255026444312369 174437175935441269833234277)
                ·
                  refine ⟨32706970487895238093731427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174437175935441269833234277 32706970487895238093731427)
                  ·
                    refine ⟨49060455731842857140597141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32706970487895238093731427 49060455731842857140597141)
                    ·
                      refine ⟨2299708862430133928465491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49060455731842857140597141 2299708862430133928465491)
                      ·
                        rfl

theorem cell23_4478667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_4478667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478667 prefixEnd_4478667 := by exact prefixLift 4478667
  have htrace : WordTrace (prefixWord ++ tailWord_4478667) baseStart_4478667 baseEnd_4478667 := by
    simpa [prefixWord, tailWord_4478667, baseEnd_4478667] using wordTrace_append hprefix tailTrace_4478667
  have hstable : (prefixWord ++ tailWord_4478667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478667).length < 2 ^ (prefixWord ++ tailWord_4478667).sum := by decide
  have hdescent : baseEnd_4478667 < baseStart_4478667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478668 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_4478668 : Nat := 118140960795 + 4478668 * 2 ^ 59
def prefixEnd_4478668 : Nat := 4983230072969 + 3 ^ 40 * 4478668 * 2
def baseEnd_4478668 : Nat := 766569791970262808184329

theorem tailTrace_4478668 : CollatzResearch.WordTrace tailWord_4478668 prefixEnd_4478668 766569791970262808184329 := by
  unfold tailWord_4478668
  simp only [CollatzResearch.WordTrace]
  refine ⟨81675220869279103221530329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108900294492372137628707105 81675220869279103221530329)
  ·
    refine ⟨61256415651959327416147747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81675220869279103221530329 61256415651959327416147747)
    ·
      refine ⟨91884623477938991124221621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61256415651959327416147747 91884623477938991124221621)
      ·
        refine ⟨8614183451056780417895777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91884623477938991124221621 8614183451056780417895777)
        ·
          refine ⟨6460637588292585313421833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8614183451056780417895777 6460637588292585313421833)
          ·
            refine ⟨4845478191219438985066375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6460637588292585313421833 4845478191219438985066375)
            ·
              refine ⟨7268217286829158477599563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4845478191219438985066375 7268217286829158477599563)
              ·
                refine ⟨10902325930243737716399345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7268217286829158477599563 10902325930243737716399345)
                ·
                  refine ⟨8176744447682803287299509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10902325930243737716399345 8176744447682803287299509)
                  ·
                    refine ⟨766569791970262808184329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8176744447682803287299509 766569791970262808184329)
                    ·
                      rfl

theorem cell23_4478668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_4478668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478668 prefixEnd_4478668 := by exact prefixLift 4478668
  have htrace : WordTrace (prefixWord ++ tailWord_4478668) baseStart_4478668 baseEnd_4478668 := by
    simpa [prefixWord, tailWord_4478668, baseEnd_4478668] using wordTrace_append hprefix tailTrace_4478668
  have hstable : (prefixWord ++ tailWord_4478668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478668).length < 2 ^ (prefixWord ++ tailWord_4478668).sum := by decide
  have hdescent : baseEnd_4478668 < baseStart_4478668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478698 : List Nat := [3, 1, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_4478698 : Nat := 118140960795 + 4478698 * 2 ^ 59
def prefixEnd_4478698 : Nat := 4983230072969 + 3 ^ 40 * 4478698 * 2
def baseEnd_4478698 : Nat := 766574926776807769059283

theorem tailTrace_4478698 : CollatzResearch.WordTrace tailWord_4478698 prefixEnd_4478698 766574926776807769059283 := by
  unfold tailWord_4478698
  simp only [CollatzResearch.WordTrace]
  refine ⟨40837883982112380391663187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108901023952299681044435165 40837883982112380391663187)
  ·
    refine ⟨61256825973168570587494781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40837883982112380391663187 61256825973168570587494781)
    ·
      refine ⟨22971309739938213970310543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61256825973168570587494781 22971309739938213970310543)
      ·
        refine ⟨34456964609907320955465815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22971309739938213970310543 34456964609907320955465815)
        ·
          refine ⟨51685446914860981433198723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34456964609907320955465815 51685446914860981433198723)
          ·
            refine ⟨77528170372291472149798085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51685446914860981433198723 77528170372291472149798085)
            ·
              refine ⟨14536531944804651028087141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77528170372291472149798085 14536531944804651028087141)
              ·
                refine ⟨2725599739650872067766339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14536531944804651028087141 2725599739650872067766339)
                ·
                  refine ⟨4088399609476308101649509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725599739650872067766339 4088399609476308101649509)
                  ·
                    refine ⟨766574926776807769059283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4088399609476308101649509 766574926776807769059283)
                    ·
                      rfl

theorem cell23_4478698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_4478698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478698 prefixEnd_4478698 := by exact prefixLift 4478698
  have htrace : WordTrace (prefixWord ++ tailWord_4478698) baseStart_4478698 baseEnd_4478698 := by
    simpa [prefixWord, tailWord_4478698, baseEnd_4478698] using wordTrace_append hprefix tailTrace_4478698
  have hstable : (prefixWord ++ tailWord_4478698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478698).length < 2 ^ (prefixWord ++ tailWord_4478698).sum := by decide
  have hdescent : baseEnd_4478698 < baseStart_4478698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478731 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 1, 5, 2]
def baseStart_4478731 : Nat := 118140960795 + 4478731 * 2 ^ 59
def prefixEnd_4478731 : Nat := 4983230072969 + 3 ^ 40 * 4478731 * 2
def baseEnd_4478731 : Nat := 2299741725192021678065197

theorem tailTrace_4478731 : CollatzResearch.WordTrace tailWord_4478731 prefixEnd_4478731 2299741725192021678065197 := by
  unfold tailWord_4478731
  simp only [CollatzResearch.WordTrace]
  refine ⟨163352739537329968202604047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108901826358219978801736031 163352739537329968202604047)
  ·
    refine ⟨245029109305994952303906071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163352739537329968202604047 245029109305994952303906071)
    ·
      refine ⟨367543663958992428455859107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245029109305994952303906071 367543663958992428455859107)
      ·
        refine ⟨551315495938488642683788661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367543663958992428455859107 551315495938488642683788661)
        ·
          refine ⟨51685827744233310251605187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 551315495938488642683788661 51685827744233310251605187)
          ·
            refine ⟨77528741616349965377407781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51685827744233310251605187 77528741616349965377407781)
            ·
              refine ⟨14536639053065618508263959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77528741616349965377407781 14536639053065618508263959)
              ·
                refine ⟨21804958579598427762395939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14536639053065618508263959 21804958579598427762395939)
                ·
                  refine ⟨32707437869397641643593909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21804958579598427762395939 32707437869397641643593909)
                  ·
                    refine ⟨3066322300256028904086929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32707437869397641643593909 3066322300256028904086929)
                    ·
                      refine ⟨2299741725192021678065197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066322300256028904086929 2299741725192021678065197)
                      ·
                        rfl

theorem cell23_4478731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 5, 2].length) (baseStart_4478731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478731 prefixEnd_4478731 := by exact prefixLift 4478731
  have htrace : WordTrace (prefixWord ++ tailWord_4478731) baseStart_4478731 baseEnd_4478731 := by
    simpa [prefixWord, tailWord_4478731, baseEnd_4478731] using wordTrace_append hprefix tailTrace_4478731
  have hstable : (prefixWord ++ tailWord_4478731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478731).length < 2 ^ (prefixWord ++ tailWord_4478731).sum := by decide
  have hdescent : baseEnd_4478731 < baseStart_4478731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478741 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_4478741 : Nat := 118140960795 + 4478741 * 2 ^ 59
def prefixEnd_4478741 : Nat := 4983230072969 + 3 ^ 40 * 4478741 * 2
def baseEnd_4478741 : Nat := 766582286666188879646717

theorem tailTrace_4478741 : CollatzResearch.WordTrace tailWord_4478741 prefixEnd_4478741 766582286666188879646717 := by
  unfold tailWord_4478741
  simp only [CollatzResearch.WordTrace]
  refine ⟨163353104267293739910468077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108902069511529159940312051 163353104267293739910468077)
  ·
    refine ⟨61257414100235152466425529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163353104267293739910468077 61257414100235152466425529)
    ·
      refine ⟨45943060575176364349819147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61257414100235152466425529 45943060575176364349819147)
      ·
        refine ⟨68914590862764546524728721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45943060575176364349819147 68914590862764546524728721)
        ·
          refine ⟨51685943147073409893546541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68914590862764546524728721 51685943147073409893546541)
          ·
            refine ⟨19382228680152528710079953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51685943147073409893546541 19382228680152528710079953)
            ·
              refine ⟨14536671510114396532559965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19382228680152528710079953 14536671510114396532559965)
              ·
                refine ⟨5451251816292898699709987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14536671510114396532559965 5451251816292898699709987)
                ·
                  refine ⟨8176877724439348049564981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5451251816292898699709987 8176877724439348049564981)
                  ·
                    refine ⟨766582286666188879646717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8176877724439348049564981 766582286666188879646717)
                    ·
                      rfl

theorem cell23_4478741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_4478741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478741 prefixEnd_4478741 := by exact prefixLift 4478741
  have htrace : WordTrace (prefixWord ++ tailWord_4478741) baseStart_4478741 baseEnd_4478741 := by
    simpa [prefixWord, tailWord_4478741, baseEnd_4478741] using wordTrace_append hprefix tailTrace_4478741
  have hstable : (prefixWord ++ tailWord_4478741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478741).length < 2 ^ (prefixWord ++ tailWord_4478741).sum := by decide
  have hdescent : baseEnd_4478741 < baseStart_4478741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478748 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_4478748 : Nat := 118140960795 + 4478748 * 2 ^ 59
def prefixEnd_4478748 : Nat := 4983230072969 + 3 ^ 40 * 4478748 * 2
def baseEnd_4478748 : Nat := 2299750454363148111552619

theorem tailTrace_4478748 : CollatzResearch.WordTrace tailWord_4478748 prefixEnd_4478748 2299750454363148111552619 := by
  unfold tailWord_4478748
  simp only [CollatzResearch.WordTrace]
  refine ⟨81676679789134190052986449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108902239718845586737315265 81676679789134190052986449)
  ·
    refine ⟨61257509841850642539739837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81676679789134190052986449 61257509841850642539739837)
    ·
      refine ⟨22971566190693990952402439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61257509841850642539739837 22971566190693990952402439)
      ·
        refine ⟨34457349286040986428603659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22971566190693990952402439 34457349286040986428603659)
        ·
          refine ⟨51686023929061479642905489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34457349286040986428603659 51686023929061479642905489)
          ·
            refine ⟨38764517946796109732179117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51686023929061479642905489 38764517946796109732179117)
            ·
              refine ⟨14536694230048541149567169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38764517946796109732179117 14536694230048541149567169)
              ·
                refine ⟨10902520672536405862175377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14536694230048541149567169 10902520672536405862175377)
                ·
                  refine ⟨8176890504402304396631533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10902520672536405862175377 8176890504402304396631533)
                  ·
                    refine ⟨3066333939150864148736825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8176890504402304396631533 3066333939150864148736825)
                    ·
                      refine ⟨2299750454363148111552619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066333939150864148736825 2299750454363148111552619)
                      ·
                        rfl

theorem cell23_4478748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_4478748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478748 prefixEnd_4478748 := by exact prefixLift 4478748
  have htrace : WordTrace (prefixWord ++ tailWord_4478748) baseStart_4478748 baseEnd_4478748 := by
    simpa [prefixWord, tailWord_4478748, baseEnd_4478748] using wordTrace_append hprefix tailTrace_4478748
  have hstable : (prefixWord ++ tailWord_4478748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478748).length < 2 ^ (prefixWord ++ tailWord_4478748).sum := by decide
  have hdescent : baseEnd_4478748 < baseStart_4478748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478778 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_4478778 : Nat := 118140960795 + 4478778 * 2 ^ 59
def prefixEnd_4478778 : Nat := 4983230072969 + 3 ^ 40 * 4478778 * 2
def baseEnd_4478778 : Nat := 2299765858782782994177481

theorem tailTrace_4478778 : CollatzResearch.WordTrace tailWord_4478778 prefixEnd_4478778 2299765858782782994177481 := by
  unfold tailWord_4478778
  simp only [CollatzResearch.WordTrace]
  refine ⟨40838613442039923807391247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108902969178773130153043325 40838613442039923807391247)
  ·
    refine ⟨61257920163059885711086871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40838613442039923807391247 61257920163059885711086871)
    ·
      refine ⟨91886880244589828566630307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61257920163059885711086871 91886880244589828566630307)
      ·
        refine ⟨137830320366884742849945461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91886880244589828566630307 137830320366884742849945461)
        ·
          refine ⟨12921592534395444642182387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137830320366884742849945461 12921592534395444642182387)
          ·
            refine ⟨19382388801593166963273581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12921592534395444642182387 19382388801593166963273581)
            ·
              refine ⟨7268395800597437611227593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19382388801593166963273581 7268395800597437611227593)
              ·
                refine ⟨5451296850448078208420695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7268395800597437611227593 5451296850448078208420695)
                ·
                  refine ⟨8176945275672117312631043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5451296850448078208420695 8176945275672117312631043)
                  ·
                    refine ⟨12265417913508175968946565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8176945275672117312631043 12265417913508175968946565)
                    ·
                      refine ⟨2299765858782782994177481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12265417913508175968946565 2299765858782782994177481)
                      ·
                        rfl

theorem cell23_4478778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_4478778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478778 prefixEnd_4478778 := by exact prefixLift 4478778
  have htrace : WordTrace (prefixWord ++ tailWord_4478778) baseStart_4478778 baseEnd_4478778 := by
    simpa [prefixWord, tailWord_4478778, baseEnd_4478778] using wordTrace_append hprefix tailTrace_4478778
  have hstable : (prefixWord ++ tailWord_4478778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478778).length < 2 ^ (prefixWord ++ tailWord_4478778).sum := by decide
  have hdescent : baseEnd_4478778 < baseStart_4478778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478818 : List Nat := [3, 3, 2, 1, 2, 3, 1, 8]
def baseStart_4478818 : Nat := 118140960795 + 4478818 * 2 ^ 59
def prefixEnd_4478818 : Nat := 4983230072969 + 3 ^ 40 * 4478818 * 2
def baseEnd_4478818 : Nat := 85177274000331956951011

theorem tailTrace_4478818 : CollatzResearch.WordTrace tailWord_4478818 prefixEnd_4478818 85177274000331956951011 := by
  unfold tailWord_4478818
  simp only [CollatzResearch.WordTrace]
  refine ⟨40838978172003695515255277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108903941792009854707347405 40838978172003695515255277)
  ·
    refine ⟨15314616814501385818220729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40838978172003695515255277 15314616814501385818220729)
    ·
      refine ⟨11485962610876039363665547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15314616814501385818220729 11485962610876039363665547)
      ·
        refine ⟨17228943916314059045498321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11485962610876039363665547 17228943916314059045498321)
        ·
          refine ⟨12921707937235544284123741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17228943916314059045498321 12921707937235544284123741)
          ·
            refine ⟨4845640476463329106546403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12921707937235544284123741 4845640476463329106546403)
            ·
              refine ⟨7268460714694993659819605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4845640476463329106546403 7268460714694993659819605)
              ·
                refine ⟨85177274000331956951011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7268460714694993659819605 85177274000331956951011)
                ·
                  rfl

theorem cell23_4478818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 8].length) (baseStart_4478818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478818 prefixEnd_4478818 := by exact prefixLift 4478818
  have htrace : WordTrace (prefixWord ++ tailWord_4478818) baseStart_4478818 baseEnd_4478818 := by
    simpa [prefixWord, tailWord_4478818, baseEnd_4478818] using wordTrace_append hprefix tailTrace_4478818
  have hstable : (prefixWord ++ tailWord_4478818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478818).length < 2 ^ (prefixWord ++ tailWord_4478818).sum := by decide
  have hdescent : baseEnd_4478818 < baseStart_4478818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478828 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_4478828 : Nat := 118140960795 + 4478828 * 2 ^ 59
def prefixEnd_4478828 : Nat := 4983230072969 + 3 ^ 40 * 4478828 * 2
def baseEnd_4478828 : Nat := 2299791532815507798552251

theorem tailTrace_4478828 : CollatzResearch.WordTrace tailWord_4478828 prefixEnd_4478828 2299791532815507798552251 := by
  unfold tailWord_4478828
  simp only [CollatzResearch.WordTrace]
  refine ⟨81678138708989276884442569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108904184945319035845923425 81678138708989276884442569)
  ·
    refine ⟨61258604031741957663331927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81678138708989276884442569 61258604031741957663331927)
    ·
      refine ⟨91887906047612936494997891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61258604031741957663331927 91887906047612936494997891)
      ·
        refine ⟨137831859071419404742496837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91887906047612936494997891 137831859071419404742496837)
        ·
          refine ⟨25843473575891138389218157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137831859071419404742496837 25843473575891138389218157)
          ·
            refine ⟨9691302590959176895956809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25843473575891138389218157 9691302590959176895956809)
            ·
              refine ⟨7268476943219382671967607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9691302590959176895956809 7268476943219382671967607)
              ·
                refine ⟨10902715414829074007951411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7268476943219382671967607 10902715414829074007951411)
                ·
                  refine ⟨16354073122243611011927117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10902715414829074007951411 16354073122243611011927117)
                  ·
                    refine ⟨6132777420841354129472669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16354073122243611011927117 6132777420841354129472669)
                    ·
                      refine ⟨2299791532815507798552251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6132777420841354129472669 2299791532815507798552251)
                      ·
                        rfl

theorem cell23_4478828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_4478828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478828 prefixEnd_4478828 := by exact prefixLift 4478828
  have htrace : WordTrace (prefixWord ++ tailWord_4478828) baseStart_4478828 baseEnd_4478828 := by
    simpa [prefixWord, tailWord_4478828, baseEnd_4478828] using wordTrace_append hprefix tailTrace_4478828
  have hstable : (prefixWord ++ tailWord_4478828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478828).length < 2 ^ (prefixWord ++ tailWord_4478828).sum := by decide
  have hdescent : baseEnd_4478828 < baseStart_4478828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478846 : List Nat := [4, 2, 3, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4478846 : Nat := 118140960795 + 4478846 * 2 ^ 59
def prefixEnd_4478846 : Nat := 4983230072969 + 3 ^ 40 * 4478846 * 2
def baseEnd_4478846 : Nat := 2299800775467288728127169

theorem tailTrace_4478846 : CollatzResearch.WordTrace tailWord_4478846 prefixEnd_4478846 2299800775467288728127169 := by
  unfold tailWord_4478846
  simp only [CollatzResearch.WordTrace]
  refine ⟨20419616741489167855380049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108904622621275561895360261 20419616741489167855380049)
  ·
    refine ⟨15314712556116875891535037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20419616741489167855380049 15314712556116875891535037)
    ·
      refine ⟨5743017208543828459325639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15314712556116875891535037 5743017208543828459325639)
      ·
        refine ⟨8614525812815742688988459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743017208543828459325639 8614525812815742688988459)
        ·
          refine ⟨12921788719223614033482689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8614525812815742688988459 12921788719223614033482689)
          ·
            refine ⟨9691341539417710525112017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12921788719223614033482689 9691341539417710525112017)
            ·
              refine ⟨7268506154563282893834013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9691341539417710525112017 7268506154563282893834013)
              ·
                refine ⟨2725689807961231085187755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7268506154563282893834013 2725689807961231085187755)
                ·
                  refine ⟨4088534711941846627781633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725689807961231085187755 4088534711941846627781633)
                  ·
                    refine ⟨3066401033956384970836225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4088534711941846627781633 3066401033956384970836225)
                    ·
                      refine ⟨2299800775467288728127169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066401033956384970836225 2299800775467288728127169)
                      ·
                        rfl

theorem cell23_4478846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4478846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478846 prefixEnd_4478846 := by exact prefixLift 4478846
  have htrace : WordTrace (prefixWord ++ tailWord_4478846) baseStart_4478846 baseEnd_4478846 := by
    simpa [prefixWord, tailWord_4478846, baseEnd_4478846] using wordTrace_append hprefix tailTrace_4478846
  have hstable : (prefixWord ++ tailWord_4478846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478846).length < 2 ^ (prefixWord ++ tailWord_4478846).sum := by decide
  have hdescent : baseEnd_4478846 < baseStart_4478846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478849 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_4478849 : Nat := 118140960795 + 4478849 * 2 ^ 59
def prefixEnd_4478849 : Nat := 4983230072969 + 3 ^ 40 * 4478849 * 2
def baseEnd_4478849 : Nat := 2299802315909252216389655

theorem tailTrace_4478849 : CollatzResearch.WordTrace tailWord_4478849 prefixEnd_4478849 2299802315909252216389655 := by
  unfold tailWord_4478849
  simp only [CollatzResearch.WordTrace]
  refine ⟨163357043350902474355399601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108904695567268316236933067 163357043350902474355399601)
  ·
    refine ⟨122517782513176855766549701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163357043350902474355399601 122517782513176855766549701)
    ·
      refine ⟨22972084221220660456228069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122517782513176855766549701 22972084221220660456228069)
      ·
        refine ⟨4307265791478873835542763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22972084221220660456228069 4307265791478873835542763)
        ·
          refine ⟨6460898687218310753314145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307265791478873835542763 6460898687218310753314145)
          ·
            refine ⟨4845674015413733064985609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6460898687218310753314145 4845674015413733064985609)
            ·
              refine ⟨3634255511560299798739207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845674015413733064985609 3634255511560299798739207)
              ·
                refine ⟨5451383267340449698108811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3634255511560299798739207 5451383267340449698108811)
                ·
                  refine ⟨8177074901010674547163217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5451383267340449698108811 8177074901010674547163217)
                  ·
                    refine ⟨6132806175758005910372413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8177074901010674547163217 6132806175758005910372413)
                    ·
                      refine ⟨2299802315909252216389655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6132806175758005910372413 2299802315909252216389655)
                      ·
                        rfl

theorem cell23_4478849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_4478849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478849 prefixEnd_4478849 := by exact prefixLift 4478849
  have htrace : WordTrace (prefixWord ++ tailWord_4478849) baseStart_4478849 baseEnd_4478849 := by
    simpa [prefixWord, tailWord_4478849, baseEnd_4478849] using wordTrace_append hprefix tailTrace_4478849
  have hstable : (prefixWord ++ tailWord_4478849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478849).length < 2 ^ (prefixWord ++ tailWord_4478849).sum := by decide
  have hdescent : baseEnd_4478849 < baseStart_4478849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478862 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4478862 : Nat := 118140960795 + 4478862 * 2 ^ 59
def prefixEnd_4478862 : Nat := 4983230072969 + 3 ^ 40 * 4478862 * 2
def baseEnd_4478862 : Nat := 2299808991157760665527095

theorem tailTrace_4478862 : CollatzResearch.WordTrace tailWord_4478862 prefixEnd_4478862 2299808991157760665527095 := by
  unfold tailWord_4478862
  simp only [CollatzResearch.WordTrace]
  refine ⟨20419689687481922196952855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108905011666570251717081893 20419689687481922196952855)
  ·
    refine ⟨30629534531222883295429283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20419689687481922196952855 30629534531222883295429283)
    ·
      refine ⟨45944301796834324943143925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30629534531222883295429283 45944301796834324943143925)
      ·
        refine ⟨4307278293453217963419743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45944301796834324943143925 4307278293453217963419743)
        ·
          refine ⟨6460917440179826945129615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307278293453217963419743 6460917440179826945129615)
          ·
            refine ⟨9691376160269740417694423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460917440179826945129615 9691376160269740417694423)
            ·
              refine ⟨14537064240404610626541635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9691376160269740417694423 14537064240404610626541635)
              ·
                refine ⟨21805596360606915939812453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14537064240404610626541635 21805596360606915939812453)
                ·
                  refine ⟨4088549317613796738714835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21805596360606915939812453 4088549317613796738714835)
                  ·
                    refine ⟨6132823976420695108072253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4088549317613796738714835 6132823976420695108072253)
                    ·
                      refine ⟨2299808991157760665527095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6132823976420695108072253 2299808991157760665527095)
                      ·
                        rfl

theorem cell23_4478862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4478862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478862 prefixEnd_4478862 := by exact prefixLift 4478862
  have htrace : WordTrace (prefixWord ++ tailWord_4478862) baseStart_4478862 baseEnd_4478862 := by
    simpa [prefixWord, tailWord_4478862, baseEnd_4478862] using wordTrace_append hprefix tailTrace_4478862
  have hstable : (prefixWord ++ tailWord_4478862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478862).length < 2 ^ (prefixWord ++ tailWord_4478862).sum := by decide
  have hdescent : baseEnd_4478862 < baseStart_4478862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478864 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_4478864 : Nat := 118140960795 + 4478864 * 2 ^ 59
def prefixEnd_4478864 : Nat := 4983230072969 + 3 ^ 40 * 4478864 * 2
def baseEnd_4478864 : Nat := 2299810018119069657702085

theorem tailTrace_4478864 : CollatzResearch.WordTrace tailWord_4478864 prefixEnd_4478864 2299810018119069657702085 := by
  unfold tailWord_4478864
  simp only [CollatzResearch.WordTrace]
  refine ⟨81678795222924065958597823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108905060297232087944797097 81678795222924065958597823)
  ·
    refine ⟨122518192834386098937896735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81678795222924065958597823 122518192834386098937896735)
    ·
      refine ⟨183777289251579148406845103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122518192834386098937896735 183777289251579148406845103)
      ·
        refine ⟨275665933877368722610267655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183777289251579148406845103 275665933877368722610267655)
        ·
          refine ⟨413498900816053083915401483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275665933877368722610267655 413498900816053083915401483)
          ·
            refine ⟨620248351224079625873102225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413498900816053083915401483 620248351224079625873102225)
            ·
              refine ⟨465186263418059719404826669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620248351224079625873102225 465186263418059719404826669)
              ·
                refine ⟨174444848781772394776810001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 465186263418059719404826669 174444848781772394776810001)
                ·
                  refine ⟨130833636586329296082607501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174444848781772394776810001 130833636586329296082607501)
                  ·
                    refine ⟨49062613719873486030977813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130833636586329296082607501 49062613719873486030977813)
                    ·
                      refine ⟨2299810018119069657702085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49062613719873486030977813 2299810018119069657702085)
                      ·
                        rfl

theorem cell23_4478864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_4478864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478864 prefixEnd_4478864 := by exact prefixLift 4478864
  have htrace : WordTrace (prefixWord ++ tailWord_4478864) baseStart_4478864 baseEnd_4478864 := by
    simpa [prefixWord, tailWord_4478864, baseEnd_4478864] using wordTrace_append hprefix tailTrace_4478864
  have hstable : (prefixWord ++ tailWord_4478864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478864).length < 2 ^ (prefixWord ++ tailWord_4478864).sum := by decide
  have hdescent : baseEnd_4478864 < baseStart_4478864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478885 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 2, 2, 2]
def baseStart_4478885 : Nat := 118140960795 + 4478885 * 2 ^ 59
def prefixEnd_4478885 : Nat := 4983230072969 + 3 ^ 40 * 4478885 * 2
def baseEnd_4478885 : Nat := 2299820801212814075539489

theorem tailTrace_4478885 : CollatzResearch.WordTrace tailWord_4478885 prefixEnd_4478885 2299820801212814075539489 := by
  unfold tailWord_4478885
  simp only [CollatzResearch.WordTrace]
  refine ⟨163358356378772052503710109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108905570919181368335806739 163358356378772052503710109)
  ·
    refine ⟨61259383642039519688891291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163358356378772052503710109 61259383642039519688891291)
    ·
      refine ⟨91889075463059279533336937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61259383642039519688891291 91889075463059279533336937)
      ·
        refine ⟨68916806597294459650002703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91889075463059279533336937 68916806597294459650002703)
        ·
          refine ⟨103375209895941689475004055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68916806597294459650002703 103375209895941689475004055)
          ·
            refine ⟨155062814843912534212506083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103375209895941689475004055 155062814843912534212506083)
            ·
              refine ⟨232594222265868801318759125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155062814843912534212506083 232594222265868801318759125)
              ·
                refine ⟨5451427084356300030908417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 232594222265868801318759125 5451427084356300030908417)
                ·
                  refine ⟨4088570313267225023181313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5451427084356300030908417 4088570313267225023181313)
                  ·
                    refine ⟨3066427734950418767385985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4088570313267225023181313 3066427734950418767385985)
                    ·
                      refine ⟨2299820801212814075539489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066427734950418767385985 2299820801212814075539489)
                      ·
                        rfl

theorem cell23_4478885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_4478885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478885 prefixEnd_4478885 := by exact prefixLift 4478885
  have htrace : WordTrace (prefixWord ++ tailWord_4478885) baseStart_4478885 baseEnd_4478885 := by
    simpa [prefixWord, tailWord_4478885, baseEnd_4478885] using wordTrace_append hprefix tailTrace_4478885
  have hstable : (prefixWord ++ tailWord_4478885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478885).length < 2 ^ (prefixWord ++ tailWord_4478885).sum := by decide
  have hdescent : baseEnd_4478885 < baseStart_4478885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4478921 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 2, 5]
def baseStart_4478921 : Nat := 118140960795 + 4478921 * 2 ^ 59
def prefixEnd_4478921 : Nat := 4983230072969 + 3 ^ 40 * 4478921 * 2
def baseEnd_4478921 : Nat := 766613095505458644896441

theorem tailTrace_4478921 : CollatzResearch.WordTrace tailWord_4478921 prefixEnd_4478921 766613095505458644896441 := by
  unfold tailWord_4478921
  simp only [CollatzResearch.WordTrace]
  refine ⟨163359669406641630652020617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108906446271094420434680411 163359669406641630652020617)
  ·
    refine ⟨122519752054981222989015463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163359669406641630652020617 122519752054981222989015463)
    ·
      refine ⟨183779628082471834483523195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122519752054981222989015463 183779628082471834483523195)
      ·
        refine ⟨275669442123707751725284793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183779628082471834483523195 275669442123707751725284793)
        ·
          refine ⟨206752081592780813793963595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275669442123707751725284793 206752081592780813793963595)
          ·
            refine ⟨310128122389171220690945393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206752081592780813793963595 310128122389171220690945393)
            ·
              refine ⟨232596091791878415518209045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310128122389171220690945393 232596091791878415518209045)
              ·
                refine ⟨10902941802744300727416049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 232596091791878415518209045 10902941802744300727416049)
                ·
                  refine ⟨8177206352058225545562037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10902941802744300727416049 8177206352058225545562037)
                  ·
                    refine ⟨766613095505458644896441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8177206352058225545562037 766613095505458644896441)
                    ·
                      rfl

theorem cell23_4478921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_4478921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4478921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4478921 prefixEnd_4478921 := by exact prefixLift 4478921
  have htrace : WordTrace (prefixWord ++ tailWord_4478921) baseStart_4478921 baseEnd_4478921 := by
    simpa [prefixWord, tailWord_4478921, baseEnd_4478921] using wordTrace_append hprefix tailTrace_4478921
  have hstable : (prefixWord ++ tailWord_4478921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4478921).length < 2 ^ (prefixWord ++ tailWord_4478921).sum := by decide
  have hdescent : baseEnd_4478921 < baseStart_4478921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4478921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479032 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 6]
def baseStart_4479032 : Nat := 118140960795 + 4479032 * 2 ^ 59
def prefixEnd_4479032 : Nat := 4983230072969 + 3 ^ 40 * 4479032 * 2
def baseEnd_4479032 : Nat := 255544031429891666711257

theorem tailTrace_4479032 : CollatzResearch.WordTrace tailWord_4479032 prefixEnd_4479032 255544031429891666711257 := by
  unfold tailWord_4479032
  simp only [CollatzResearch.WordTrace]
  refine ⟨81681858954619748304655675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108909145272826331072874233 81681858954619748304655675)
  ·
    refine ⟨122522788431929622456983513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81681858954619748304655675 122522788431929622456983513)
    ·
      refine ⟨91892091323947216842737635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122522788431929622456983513 91892091323947216842737635)
      ·
        refine ⟨137838136985920825264106453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91892091323947216842737635 137838136985920825264106453)
        ·
          refine ⟨3230581335607519342127495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 137838136985920825264106453 3230581335607519342127495)
          ·
            refine ⟨4845872003411279013191243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230581335607519342127495 4845872003411279013191243)
            ·
              refine ⟨7268808005116918519786865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4845872003411279013191243 7268808005116918519786865)
              ·
                refine ⟨5451606003837688889840149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7268808005116918519786865 5451606003837688889840149)
                ·
                  refine ⟨255544031429891666711257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5451606003837688889840149 255544031429891666711257)
                  ·
                    rfl

theorem cell23_4479032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 6].length) (baseStart_4479032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479032 prefixEnd_4479032 := by exact prefixLift 4479032
  have htrace : WordTrace (prefixWord ++ tailWord_4479032) baseStart_4479032 baseEnd_4479032 := by
    simpa [prefixWord, tailWord_4479032, baseEnd_4479032] using wordTrace_append hprefix tailTrace_4479032
  have hstable : (prefixWord ++ tailWord_4479032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479032).length < 2 ^ (prefixWord ++ tailWord_4479032).sum := by decide
  have hdescent : baseEnd_4479032 < baseStart_4479032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479048 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_4479048 : Nat := 118140960795 + 4479048 * 2 ^ 59
def prefixEnd_4479048 : Nat := 4983230072969 + 3 ^ 40 * 4479048 * 2
def baseEnd_4479048 : Nat := 2299904498559496937801239

theorem tailTrace_4479048 : CollatzResearch.WordTrace tailWord_4479048 prefixEnd_4479048 2299904498559496937801239 := by
  unfold tailWord_4479048
  simp only [CollatzResearch.WordTrace]
  refine ⟨81682150738590765670946899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108909534318121020894595865 81682150738590765670946899)
  ·
    refine ⟨122523226107886148506420349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81682150738590765670946899 122523226107886148506420349)
    ·
      refine ⟨45946209790457305689907631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122523226107886148506420349 45946209790457305689907631)
      ·
        refine ⟨68919314685685958534861447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45946209790457305689907631 68919314685685958534861447)
        ·
          refine ⟨103378972028528937802292171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68919314685685958534861447 103378972028528937802292171)
          ·
            refine ⟨155068458042793406703438257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103378972028528937802292171 155068458042793406703438257)
            ·
              refine ⟨116301343532095055027578693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155068458042793406703438257 116301343532095055027578693)
              ·
                refine ⟨21806501912267822817671005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116301343532095055027578693 21806501912267822817671005)
                ·
                  refine ⟨8177438217100433556626627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21806501912267822817671005 8177438217100433556626627)
                  ·
                    refine ⟨12266157325650650334939941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8177438217100433556626627 12266157325650650334939941)
                    ·
                      refine ⟨2299904498559496937801239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12266157325650650334939941 2299904498559496937801239)
                      ·
                        rfl

theorem cell23_4479048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_4479048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479048 prefixEnd_4479048 := by exact prefixLift 4479048
  have htrace : WordTrace (prefixWord ++ tailWord_4479048) baseStart_4479048 baseEnd_4479048 := by
    simpa [prefixWord, tailWord_4479048, baseEnd_4479048] using wordTrace_append hprefix tailTrace_4479048
  have hstable : (prefixWord ++ tailWord_4479048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479048).length < 2 ^ (prefixWord ++ tailWord_4479048).sum := by decide
  have hdescent : baseEnd_4479048 < baseStart_4479048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479065 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 4]
def baseStart_4479065 : Nat := 118140960795 + 4479065 * 2 ^ 59
def prefixEnd_4479065 : Nat := 4983230072969 + 3 ^ 40 * 4479065 * 2
def baseEnd_4479065 : Nat := 2299913227730623371288661

theorem tailTrace_4479065 : CollatzResearch.WordTrace tailWord_4479065 prefixEnd_4479065 2299913227730623371288661 := by
  unfold tailWord_4479065
  simp only [CollatzResearch.WordTrace]
  refine ⟨163364921518119943245262649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108909947678746628830175099 163364921518119943245262649)
  ·
    refine ⟨122523691138589957433946987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163364921518119943245262649 122523691138589957433946987)
    ·
      refine ⟨183785536707884936150920481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122523691138589957433946987 183785536707884936150920481)
      ·
        refine ⟨137839152530913702113190361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183785536707884936150920481 137839152530913702113190361)
        ·
          refine ⟨103379364398185276584892771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137839152530913702113190361 103379364398185276584892771)
          ·
            refine ⟨155069046597277914877339157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103379364398185276584892771 155069046597277914877339157)
            ·
              refine ⟨7268861559247402259875273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155069046597277914877339157 7268861559247402259875273)
              ·
                refine ⟨5451646169435551694906455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7268861559247402259875273 5451646169435551694906455)
                ·
                  refine ⟨8177469254153327542359683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5451646169435551694906455 8177469254153327542359683)
                  ·
                    refine ⟨12266203881229991313539525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8177469254153327542359683 12266203881229991313539525)
                    ·
                      refine ⟨2299913227730623371288661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12266203881229991313539525 2299913227730623371288661)
                      ·
                        rfl

theorem cell23_4479065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_4479065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479065 prefixEnd_4479065 := by exact prefixLift 4479065
  have htrace : WordTrace (prefixWord ++ tailWord_4479065) baseStart_4479065 baseEnd_4479065 := by
    simpa [prefixWord, tailWord_4479065, baseEnd_4479065] using wordTrace_append hprefix tailTrace_4479065
  have hstable : (prefixWord ++ tailWord_4479065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479065).length < 2 ^ (prefixWord ++ tailWord_4479065).sum := by decide
  have hdescent : baseEnd_4479065 < baseStart_4479065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479070 : List Nat := [4, 4, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4479070 : Nat := 118140960795 + 4479070 * 2 ^ 59
def prefixEnd_4479070 : Nat := 4983230072969 + 3 ^ 40 * 4479070 * 2
def baseEnd_4479070 : Nat := 766638598377965283908713

theorem tailTrace_4479070 : CollatzResearch.WordTrace tailWord_4479070 prefixEnd_4479070 766638598377965283908713 := by
  unfold tailWord_4479070
  simp only [CollatzResearch.WordTrace]
  refine ⟨20420637985387728637399333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108910069255401219399463109 20420637985387728637399333)
  ·
    refine ⟨3828869622260199119512375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20420637985387728637399333 3828869622260199119512375)
    ·
      refine ⟨5743304433390298679268563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828869622260199119512375 5743304433390298679268563)
      ·
        refine ⟨8614956650085448018902845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743304433390298679268563 8614956650085448018902845)
        ·
          refine ⟨3230608743782043007088567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8614956650085448018902845 3230608743782043007088567)
          ·
            refine ⟨4845913115673064510632851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230608743782043007088567 4845913115673064510632851)
            ·
              refine ⟨7268869673509596765949277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4845913115673064510632851 7268869673509596765949277)
              ·
                refine ⟨2725826127566098787230979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7268869673509596765949277 2725826127566098787230979)
                ·
                  refine ⟨4088739191349148180846469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725826127566098787230979 4088739191349148180846469)
                  ·
                    refine ⟨766638598377965283908713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4088739191349148180846469 766638598377965283908713)
                    ·
                      rfl

theorem cell23_4479070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4479070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479070 prefixEnd_4479070 := by exact prefixLift 4479070
  have htrace : WordTrace (prefixWord ++ tailWord_4479070) baseStart_4479070 baseEnd_4479070 := by
    simpa [prefixWord, tailWord_4479070, baseEnd_4479070] using wordTrace_append hprefix tailTrace_4479070
  have hstable : (prefixWord ++ tailWord_4479070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479070).length < 2 ^ (prefixWord ++ tailWord_4479070).sum := by decide
  have hdescent : baseEnd_4479070 < baseStart_4479070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479085 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_4479085 : Nat := 118140960795 + 4479085 * 2 ^ 59
def prefixEnd_4479085 : Nat := 4983230072969 + 3 ^ 40 * 4479085 * 2
def baseEnd_4479085 : Nat := 2299923497343713293038569

theorem tailTrace_4479085 : CollatzResearch.WordTrace tailWord_4479085 prefixEnd_4479085 2299923497343713293038569 := by
  unfold tailWord_4479085
  simp only [CollatzResearch.WordTrace]
  refine ⟨163365650978047486660990709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108910433985364991107327139 163365650978047486660990709)
  ·
    refine ⟨15315529779191951874467879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163365650978047486660990709 15315529779191951874467879)
    ·
      refine ⟨22973294668787927811701819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15315529779191951874467879 22973294668787927811701819)
      ·
        refine ⟨34459942003181891717552729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22973294668787927811701819 34459942003181891717552729)
        ·
          refine ⟨25844956502386418788164547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34459942003181891717552729 25844956502386418788164547)
          ·
            refine ⟨38767434753579628182246821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25844956502386418788164547 38767434753579628182246821)
            ·
              refine ⟨7268894016296180284171279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38767434753579628182246821 7268894016296180284171279)
              ·
                refine ⟨10903341024444270426256919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7268894016296180284171279 10903341024444270426256919)
                ·
                  refine ⟨16355011536666405639385379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10903341024444270426256919 16355011536666405639385379)
                  ·
                    refine ⟨24532517304999608459078069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16355011536666405639385379 24532517304999608459078069)
                    ·
                      refine ⟨2299923497343713293038569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24532517304999608459078069 2299923497343713293038569)
                      ·
                        rfl

theorem cell23_4479085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_4479085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479085 prefixEnd_4479085 := by exact prefixLift 4479085
  have htrace : WordTrace (prefixWord ++ tailWord_4479085) baseStart_4479085 baseEnd_4479085 := by
    simpa [prefixWord, tailWord_4479085, baseEnd_4479085] using wordTrace_append hprefix tailTrace_4479085
  have hstable : (prefixWord ++ tailWord_4479085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479085).length < 2 ^ (prefixWord ++ tailWord_4479085).sum := by decide
  have hdescent : baseEnd_4479085 < baseStart_4479085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479088 : List Nat := [2, 1, 1, 1, 5, 4, 9]
def baseStart_4479088 : Nat := 118140960795 + 4479088 * 2 ^ 59
def prefixEnd_4479088 : Nat := 4983230072969 + 3 ^ 40 * 4479088 * 2
def baseEnd_4479088 : Nat := 28394136268958972608655

theorem tailTrace_4479088 : CollatzResearch.WordTrace tailWord_4479088 prefixEnd_4479088 28394136268958972608655 := by
  unfold tailWord_4479088
  simp only [CollatzResearch.WordTrace]
  refine ⟨81682880198518309086674959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108910506931357745448899945 81682880198518309086674959)
  ·
    refine ⟨122524320297777463630012439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81682880198518309086674959 122524320297777463630012439)
    ·
      refine ⟨183786480446666195445018659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122524320297777463630012439 183786480446666195445018659)
      ·
        refine ⟨275679720669999293167527989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183786480446666195445018659 275679720669999293167527989)
        ·
          refine ⟨25844973812812433734455749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 275679720669999293167527989 25844973812812433734455749)
          ·
            refine ⟨4845932589902331325210453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25844973812812433734455749 4845932589902331325210453)
            ·
              refine ⟨28394136268958972608655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4845932589902331325210453 28394136268958972608655)
              ·
                rfl

theorem cell23_4479088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 9].length) (baseStart_4479088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479088 prefixEnd_4479088 := by exact prefixLift 4479088
  have htrace : WordTrace (prefixWord ++ tailWord_4479088) baseStart_4479088 baseEnd_4479088 := by
    simpa [prefixWord, tailWord_4479088, baseEnd_4479088] using wordTrace_append hprefix tailTrace_4479088
  have hstable : (prefixWord ++ tailWord_4479088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479088).length < 2 ^ (prefixWord ++ tailWord_4479088).sum := by decide
  have hdescent : baseEnd_4479088 < baseStart_4479088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479105 : List Nat := [1, 2, 4, 2, 3, 1, 2, 8]
def baseStart_4479105 : Nat := 118140960795 + 4479105 * 2 ^ 59
def prefixEnd_4479105 : Nat := 4983230072969 + 3 ^ 40 * 4479105 * 2
def baseEnd_4479105 : Nat := 85182732109511230177351

theorem tailTrace_4479105 : CollatzResearch.WordTrace tailWord_4479105 prefixEnd_4479105 85182732109511230177351 := by
  unfold tailWord_4479105
  simp only [CollatzResearch.WordTrace]
  refine ⟨163366380437975030076718769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108910920291983353384479179 163366380437975030076718769)
  ·
    refine ⟨122524785328481272557539077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163366380437975030076718769 122524785328481272557539077)
    ·
      refine ⟨22973397249090238604538577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122524785328481272557539077 22973397249090238604538577)
      ·
        refine ⟨17230047936817678953403933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22973397249090238604538577 17230047936817678953403933)
        ·
          refine ⟨6461267976306629607526475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17230047936817678953403933 6461267976306629607526475)
          ·
            refine ⟨9691901964459944411289713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461267976306629607526475 9691901964459944411289713)
            ·
              refine ⟨7268926473344958308467285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9691901964459944411289713 7268926473344958308467285)
              ·
                refine ⟨85182732109511230177351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7268926473344958308467285 85182732109511230177351)
                ·
                  rfl

theorem cell23_4479105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 8].length) (baseStart_4479105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479105 prefixEnd_4479105 := by exact prefixLift 4479105
  have htrace : WordTrace (prefixWord ++ tailWord_4479105) baseStart_4479105 baseEnd_4479105 := by
    simpa [prefixWord, tailWord_4479105, baseEnd_4479105] using wordTrace_append hprefix tailTrace_4479105
  have hstable : (prefixWord ++ tailWord_4479105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479105).length < 2 ^ (prefixWord ++ tailWord_4479105).sum := by decide
  have hdescent : baseEnd_4479105 < baseStart_4479105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479108 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4479108 : Nat := 118140960795 + 4479108 * 2 ^ 59
def prefixEnd_4479108 : Nat := 4983230072969 + 3 ^ 40 * 4479108 * 2
def baseEnd_4479108 : Nat := 2299935307398766703050963

theorem tailTrace_4479108 : CollatzResearch.WordTrace tailWord_4479108 prefixEnd_4479108 2299935307398766703050963 := by
  unfold tailWord_4479108
  simp only [CollatzResearch.WordTrace]
  refine ⟨81683244928482080794538989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108910993237976107726051985 81683244928482080794538989)
  ·
    refine ⟨30631216848180780297952121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81683244928482080794538989 30631216848180780297952121)
    ·
      refine ⟨22973412636135585223464091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30631216848180780297952121 22973412636135585223464091)
      ·
        refine ⟨34460118954203377835196137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22973412636135585223464091 34460118954203377835196137)
        ·
          refine ⟨25845089215652533376397103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34460118954203377835196137 25845089215652533376397103)
          ·
            refine ⟨38767633823478800064595655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25845089215652533376397103 38767633823478800064595655)
            ·
              refine ⟨58151450735218200096893483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38767633823478800064595655 58151450735218200096893483)
              ·
                refine ⟨87227176102827300145340225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58151450735218200096893483 87227176102827300145340225)
                ·
                  refine ⟨65420382077120475109005169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87227176102827300145340225 65420382077120475109005169)
                  ·
                    refine ⟨49065286557840356331753877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65420382077120475109005169 49065286557840356331753877)
                    ·
                      refine ⟨2299935307398766703050963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49065286557840356331753877 2299935307398766703050963)
                      ·
                        rfl

theorem cell23_4479108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4479108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479108 prefixEnd_4479108 := by exact prefixLift 4479108
  have htrace : WordTrace (prefixWord ++ tailWord_4479108) baseStart_4479108 baseEnd_4479108 := by
    simpa [prefixWord, tailWord_4479108, baseEnd_4479108] using wordTrace_append hprefix tailTrace_4479108
  have hstable : (prefixWord ++ tailWord_4479108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479108).length < 2 ^ (prefixWord ++ tailWord_4479108).sum := by decide
  have hdescent : baseEnd_4479108 < baseStart_4479108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479109 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_4479109 : Nat := 118140960795 + 4479109 * 2 ^ 59
def prefixEnd_4479109 : Nat := 4983230072969 + 3 ^ 40 * 4479109 * 2
def baseEnd_4479109 : Nat := 766645273626473733046153

theorem tailTrace_4479109 : CollatzResearch.WordTrace tailWord_4479109 prefixEnd_4479109 766645273626473733046153 := by
  unfold tailWord_4479109
  simp only [CollatzResearch.WordTrace]
  refine ⟨163366526329960538759864381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108911017553307025839909587 163366526329960538759864381)
  ·
    refine ⟨61262447373735202034949143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163366526329960538759864381 61262447373735202034949143)
    ·
      refine ⟨91893671060602803052423715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61262447373735202034949143 91893671060602803052423715)
      ·
        refine ⟨137840506590904204578635573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91893671060602803052423715 137840506590904204578635573)
        ·
          refine ⟨12922547492897269179247085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137840506590904204578635573 12922547492897269179247085)
          ·
            refine ⟨4845955309836475942217657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12922547492897269179247085 4845955309836475942217657)
            ·
              refine ⟨3634466482377356956663243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845955309836475942217657 3634466482377356956663243)
              ·
                refine ⟨5451699723566035434994865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3634466482377356956663243 5451699723566035434994865)
                ·
                  refine ⟨4088774792674526576246149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5451699723566035434994865 4088774792674526576246149)
                  ·
                    refine ⟨766645273626473733046153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4088774792674526576246149 766645273626473733046153)
                    ·
                      rfl

theorem cell23_4479109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_4479109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479109 prefixEnd_4479109 := by exact prefixLift 4479109
  have htrace : WordTrace (prefixWord ++ tailWord_4479109) baseStart_4479109 baseEnd_4479109 := by
    simpa [prefixWord, tailWord_4479109, baseEnd_4479109] using wordTrace_append hprefix tailTrace_4479109
  have hstable : (prefixWord ++ tailWord_4479109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479109).length < 2 ^ (prefixWord ++ tailWord_4479109).sum := by decide
  have hdescent : baseEnd_4479109 < baseStart_4479109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479149 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_4479149 : Nat := 118140960795 + 4479149 * 2 ^ 59
def prefixEnd_4479149 : Nat := 4983230072969 + 3 ^ 40 * 4479149 * 2
def baseEnd_4479149 : Nat := 2299956360105601042638275

theorem tailTrace_4479149 : CollatzResearch.WordTrace tailWord_4479149 prefixEnd_4479149 2299956360105601042638275 := by
  unfold tailWord_4479149
  simp only [CollatzResearch.WordTrace]
  refine ⟨163367985249815625591320501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108911990166543750394213667 163367985249815625591320501)
  ·
    refine ⟨15315748617170214899186297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163367985249815625591320501 15315748617170214899186297)
    ·
      refine ⟨11486811462877661174389723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15315748617170214899186297 11486811462877661174389723)
      ·
        refine ⟨17230217194316491761584585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11486811462877661174389723 17230217194316491761584585)
        ·
          refine ⟨12922662895737368821188439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17230217194316491761584585 12922662895737368821188439)
          ·
            refine ⟨19383994343606053231782659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12922662895737368821188439 19383994343606053231782659)
            ·
              refine ⟨29075991515409079847673989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19383994343606053231782659 29075991515409079847673989)
              ·
                refine ⟨5451748409139202471438873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29075991515409079847673989 5451748409139202471438873)
                ·
                  refine ⟨4088811306854401853579155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5451748409139202471438873 4088811306854401853579155)
                  ·
                    refine ⟨6133216960281602780368733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4088811306854401853579155 6133216960281602780368733)
                    ·
                      refine ⟨2299956360105601042638275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6133216960281602780368733 2299956360105601042638275)
                      ·
                        rfl

theorem cell23_4479149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_4479149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479149 prefixEnd_4479149 := by exact prefixLift 4479149
  have htrace : WordTrace (prefixWord ++ tailWord_4479149) baseStart_4479149 baseEnd_4479149 := by
    simpa [prefixWord, tailWord_4479149, baseEnd_4479149] using wordTrace_append hprefix tailTrace_4479149
  have hstable : (prefixWord ++ tailWord_4479149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479149).length < 2 ^ (prefixWord ++ tailWord_4479149).sum := by decide
  have hdescent : baseEnd_4479149 < baseStart_4479149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479150 : List Nat := [4, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4479150 : Nat := 118140960795 + 4479150 * 2 ^ 59
def prefixEnd_4479150 : Nat := 4983230072969 + 3 ^ 40 * 4479150 * 2
def baseEnd_4479150 : Nat := 2299956873586255538725771

theorem tailTrace_4479150 : CollatzResearch.WordTrace tailWord_4479150 prefixEnd_4479150 2299956873586255538725771 := by
  unfold tailWord_4479150
  simp only [CollatzResearch.WordTrace]
  refine ⟨20421002715351500345263363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108912014481874668508071269 20421002715351500345263363)
  ·
    refine ⟨30631504073027250517895045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20421002715351500345263363 30631504073027250517895045)
    ·
      refine ⟨5743407013692609472105321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30631504073027250517895045 5743407013692609472105321)
      ·
        refine ⟨4307555260269457104078991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5743407013692609472105321 4307555260269457104078991)
        ·
          refine ⟨6461332890404185656118487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307555260269457104078991 6461332890404185656118487)
          ·
            refine ⟨9691999335606278484177731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461332890404185656118487 9691999335606278484177731)
            ·
              refine ⟨14537999003409417726266597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9691999335606278484177731 14537999003409417726266597)
              ·
                refine ⟨2725874813139265823674987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14537999003409417726266597 2725874813139265823674987)
                ·
                  refine ⟨4088812219708898735512481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725874813139265823674987 4088812219708898735512481)
                  ·
                    refine ⟨3066609164781674051634361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4088812219708898735512481 3066609164781674051634361)
                    ·
                      refine ⟨2299956873586255538725771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066609164781674051634361 2299956873586255538725771)
                      ·
                        rfl

theorem cell23_4479150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4479150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479150 prefixEnd_4479150 := by exact prefixLift 4479150
  have htrace : WordTrace (prefixWord ++ tailWord_4479150) baseStart_4479150 baseEnd_4479150 := by
    simpa [prefixWord, tailWord_4479150, baseEnd_4479150] using wordTrace_append hprefix tailTrace_4479150
  have hstable : (prefixWord ++ tailWord_4479150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479150).length < 2 ^ (prefixWord ++ tailWord_4479150).sum := by decide
  have hdescent : baseEnd_4479150 < baseStart_4479150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479155 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 5, 4, 2]
def baseStart_4479155 : Nat := 118140960795 + 4479155 * 2 ^ 59
def prefixEnd_4479155 : Nat := 4983230072969 + 3 ^ 40 * 4479155 * 2
def baseEnd_4479155 : Nat := 2299959440989528019163247

theorem tailTrace_4479155 : CollatzResearch.WordTrace tailWord_4479155 prefixEnd_4479155 2299959440989528019163247 := by
  unfold tailWord_4479155
  simp only [CollatzResearch.WordTrace]
  refine ⟨163368204087793888616038919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108912136058529259077359279 163368204087793888616038919)
  ·
    refine ⟨245052306131690832924058379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163368204087793888616038919 245052306131690832924058379)
    ·
      refine ⟨367578459197536249386087569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245052306131690832924058379 367578459197536249386087569)
      ·
        refine ⟨275683844398152187039565677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367578459197536249386087569 275683844398152187039565677)
        ·
          refine ⟨103381441649307070139837129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275683844398152187039565677 103381441649307070139837129)
          ·
            refine ⟨77536081236980302604877847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103381441649307070139837129 77536081236980302604877847)
            ·
              refine ⟨116304121855470453907316771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77536081236980302604877847 116304121855470453907316771)
              ·
                refine ⟨174456182783205680860975157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116304121855470453907316771 174456182783205680860975157)
                ·
                  refine ⟨16355267135925532580716421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174456182783205680860975157 16355267135925532580716421)
                  ·
                    refine ⟨3066612587986037358884329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16355267135925532580716421 3066612587986037358884329)
                    ·
                      refine ⟨2299959440989528019163247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066612587986037358884329 2299959440989528019163247)
                      ·
                        rfl

theorem cell23_4479155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 4, 2].length) (baseStart_4479155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479155 prefixEnd_4479155 := by exact prefixLift 4479155
  have htrace : WordTrace (prefixWord ++ tailWord_4479155) baseStart_4479155 baseEnd_4479155 := by
    simpa [prefixWord, tailWord_4479155, baseEnd_4479155] using wordTrace_append hprefix tailTrace_4479155
  have hstable : (prefixWord ++ tailWord_4479155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479155).length < 2 ^ (prefixWord ++ tailWord_4479155).sum := by decide
  have hdescent : baseEnd_4479155 < baseStart_4479155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479156 : List Nat := [2, 5, 3, 1, 1, 2, 1, 8]
def baseStart_4479156 : Nat := 118140960795 + 4479156 * 2 ^ 59
def prefixEnd_4479156 : Nat := 4983230072969 + 3 ^ 40 * 4479156 * 2
def baseEnd_4479156 : Nat := 85183702017414167231509

theorem tailTrace_4479156 : CollatzResearch.WordTrace tailWord_4479156 prefixEnd_4479156 85183702017414167231509 := by
  unfold tailWord_4479156
  simp only [CollatzResearch.WordTrace]
  refine ⟨81684120280395132893412661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108912160373860177191216881 81684120280395132893412661)
  ·
    refine ⟨7657886276287043708757437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81684120280395132893412661 7657886276287043708757437)
    ·
      refine ⟨2871707353607641390784039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7657886276287043708757437 2871707353607641390784039)
      ·
        refine ⟨4307561030411462086176059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871707353607641390784039 4307561030411462086176059)
        ·
          refine ⟨6461341545617193129264089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4307561030411462086176059 6461341545617193129264089)
          ·
            refine ⟨4846006159212894846948067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6461341545617193129264089 4846006159212894846948067)
            ·
              refine ⟨7269009238819342270422101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4846006159212894846948067 7269009238819342270422101)
              ·
                refine ⟨85183702017414167231509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7269009238819342270422101 85183702017414167231509)
                ·
                  rfl

theorem cell23_4479156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 8].length) (baseStart_4479156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479156 prefixEnd_4479156 := by exact prefixLift 4479156
  have htrace : WordTrace (prefixWord ++ tailWord_4479156) baseStart_4479156 baseEnd_4479156 := by
    simpa [prefixWord, tailWord_4479156, baseEnd_4479156] using wordTrace_append hprefix tailTrace_4479156
  have hstable : (prefixWord ++ tailWord_4479156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479156).length < 2 ^ (prefixWord ++ tailWord_4479156).sum := by decide
  have hdescent : baseEnd_4479156 < baseStart_4479156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479195 : List Nat := [1, 1, 1, 1, 1, 1, 1, 11, 5]
def baseStart_4479195 : Nat := 118140960795 + 4479195 * 2 ^ 59
def prefixEnd_4479195 : Nat := 4983230072969 + 3 ^ 40 * 4479195 * 2
def baseEnd_4479195 : Nat := 255553331135078651407007

theorem tailTrace_4479195 : CollatzResearch.WordTrace tailWord_4479195 prefixEnd_4479195 255553331135078651407007 := by
  unfold tailWord_4479195
  simp only [CollatzResearch.WordTrace]
  refine ⟨163369663007648975447495039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108913108671765983631663359 163369663007648975447495039)
  ·
    refine ⟨245054494511473463171242559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163369663007648975447495039 245054494511473463171242559)
    ·
      refine ⟨367581741767210194756863839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245054494511473463171242559 367581741767210194756863839)
      ·
        refine ⟨551372612650815292135295759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367581741767210194756863839 551372612650815292135295759)
        ·
          refine ⟨827058918976222938202943639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551372612650815292135295759 827058918976222938202943639)
          ·
            refine ⟨1240588378464334407304415459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827058918976222938202943639 1240588378464334407304415459)
            ·
              refine ⟨1860882567696501610956623189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240588378464334407304415459 1860882567696501610956623189)
              ·
                refine ⟨2725902198774172281674741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1860882567696501610956623189 2725902198774172281674741)
                ·
                  refine ⟨255553331135078651407007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2725902198774172281674741 255553331135078651407007)
                  ·
                    rfl

theorem cell23_4479195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 5].length) (baseStart_4479195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479195 prefixEnd_4479195 := by exact prefixLift 4479195
  have htrace : WordTrace (prefixWord ++ tailWord_4479195) baseStart_4479195 baseEnd_4479195 := by
    simpa [prefixWord, tailWord_4479195, baseEnd_4479195] using wordTrace_append hprefix tailTrace_4479195
  have hstable : (prefixWord ++ tailWord_4479195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479195).length < 2 ^ (prefixWord ++ tailWord_4479195).sum := by decide
  have hdescent : baseEnd_4479195 < baseStart_4479195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479222 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_4479222 : Nat := 118140960795 + 4479222 * 2 ^ 59
def prefixEnd_4479222 : Nat := 4983230072969 + 3 ^ 40 * 4479222 * 2
def baseEnd_4479222 : Nat := 2299993844193379257025439

theorem tailTrace_4479222 : CollatzResearch.WordTrace tailWord_4479222 prefixEnd_4479222 2299993844193379257025439 := by
  unfold tailWord_4479222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210665486159447441170495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108913765185700772705818613 10210665486159447441170495)
  ·
    refine ⟨15315998229239171161755743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10210665486159447441170495 15315998229239171161755743)
    ·
      refine ⟨22973997343858756742633615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15315998229239171161755743 22973997343858756742633615)
      ·
        refine ⟨34460996015788135113950423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22973997343858756742633615 34460996015788135113950423)
        ·
          refine ⟨51691494023682202670925635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34460996015788135113950423 51691494023682202670925635)
          ·
            refine ⟨77537241035523304006388453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51691494023682202670925635 77537241035523304006388453)
            ·
              refine ⟨14538232694160619501197835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77537241035523304006388453 14538232694160619501197835)
              ·
                refine ⟨21807349041240929251796753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14538232694160619501197835 21807349041240929251796753)
                ·
                  refine ⟨16355511780930696938847565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21807349041240929251796753 16355511780930696938847565)
                  ·
                    refine ⟨6133316917849011352067837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16355511780930696938847565 6133316917849011352067837)
                    ·
                      refine ⟨2299993844193379257025439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6133316917849011352067837 2299993844193379257025439)
                      ·
                        rfl

theorem cell23_4479222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_4479222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479222 prefixEnd_4479222 := by exact prefixLift 4479222
  have htrace : WordTrace (prefixWord ++ tailWord_4479222) baseStart_4479222 baseEnd_4479222 := by
    simpa [prefixWord, tailWord_4479222, baseEnd_4479222] using wordTrace_append hprefix tailTrace_4479222
  have hstable : (prefixWord ++ tailWord_4479222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479222).length < 2 ^ (prefixWord ++ tailWord_4479222).sum := by decide
  have hdescent : baseEnd_4479222 < baseStart_4479222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479322 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2]
def baseStart_4479322 : Nat := 118140960795 + 4479322 * 2 ^ 59
def prefixEnd_4479322 : Nat := 4983230072969 + 3 ^ 40 * 4479322 * 2
def baseEnd_4479322 : Nat := 2300045192258828865774979

theorem tailTrace_4479322 : CollatzResearch.WordTrace tailWord_4479322 prefixEnd_4479322 2300045192258828865774979 := by
  unfold tailWord_4479322
  simp only [CollatzResearch.WordTrace]
  refine ⟨40843573769547219034342055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108916196718792584091578813 40843573769547219034342055)
  ·
    refine ⟨61265360654320828551513083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40843573769547219034342055 61265360654320828551513083)
    ·
      refine ⟨91898040981481242827269625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61265360654320828551513083 91898040981481242827269625)
      ·
        refine ⟨68923530736110932120452219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91898040981481242827269625 68923530736110932120452219)
        ·
          refine ⟨103385296104166398180678329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68923530736110932120452219 103385296104166398180678329)
          ·
            refine ⟨77538972078124798635508747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103385296104166398180678329 77538972078124798635508747)
            ·
              refine ⟨116308458117187197953263121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77538972078124798635508747 116308458117187197953263121)
              ·
                refine ⟨87231343587890398464947341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116308458117187197953263121 87231343587890398464947341)
                ·
                  refine ⟨32711753845458899424355253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87231343587890398464947341 32711753845458899424355253)
                  ·
                    refine ⟨3066726923011771821033305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32711753845458899424355253 3066726923011771821033305)
                    ·
                      refine ⟨2300045192258828865774979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066726923011771821033305 2300045192258828865774979)
                      ·
                        rfl

theorem cell23_4479322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_4479322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479322 prefixEnd_4479322 := by exact prefixLift 4479322
  have htrace : WordTrace (prefixWord ++ tailWord_4479322) baseStart_4479322 baseEnd_4479322 := by
    simpa [prefixWord, tailWord_4479322, baseEnd_4479322] using wordTrace_append hprefix tailTrace_4479322
  have hstable : (prefixWord ++ tailWord_4479322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479322).length < 2 ^ (prefixWord ++ tailWord_4479322).sum := by decide
  have hdescent : baseEnd_4479322 < baseStart_4479322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479350 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4479350 : Nat := 118140960795 + 4479350 * 2 ^ 59
def prefixEnd_4479350 : Nat := 4983230072969 + 3 ^ 40 * 4479350 * 2
def baseEnd_4479350 : Nat := 2300059569717154756224851

theorem tailTrace_4479350 : CollatzResearch.WordTrace tailWord_4479350 prefixEnd_4479350 2300059569717154756224851 := by
  unfold tailWord_4479350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210957270130464807461719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108916877548058291279591669 10210957270130464807461719)
  ·
    refine ⟨15316435905195697211192579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10210957270130464807461719 15316435905195697211192579)
    ·
      refine ⟨22974653857793545816788869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15316435905195697211192579 22974653857793545816788869)
      ·
        refine ⟨4307747598336289840647913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22974653857793545816788869 4307747598336289840647913)
        ·
          refine ⟨3230810698752217380485935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4307747598336289840647913 3230810698752217380485935)
          ·
            refine ⟨4846216048128326070728903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230810698752217380485935 4846216048128326070728903)
            ·
              refine ⟨7269324072192489106093355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4846216048128326070728903 7269324072192489106093355)
              ·
                refine ⟨10903986108288733659140033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7269324072192489106093355 10903986108288733659140033)
                ·
                  refine ⟨8177989581216550244355025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10903986108288733659140033 8177989581216550244355025)
                  ·
                    refine ⟨6133492185912412683266269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8177989581216550244355025 6133492185912412683266269)
                    ·
                      refine ⟨2300059569717154756224851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6133492185912412683266269 2300059569717154756224851)
                      ·
                        rfl

theorem cell23_4479350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4479350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479350 prefixEnd_4479350 := by exact prefixLift 4479350
  have htrace : WordTrace (prefixWord ++ tailWord_4479350) baseStart_4479350 baseEnd_4479350 := by
    simpa [prefixWord, tailWord_4479350, baseEnd_4479350] using wordTrace_append hprefix tailTrace_4479350
  have hstable : (prefixWord ++ tailWord_4479350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479350).length < 2 ^ (prefixWord ++ tailWord_4479350).sum := by decide
  have hdescent : baseEnd_4479350 < baseStart_4479350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479363 : List Nat := [1, 1, 1, 3, 6, 1, 2, 3, 1, 1, 3]
def baseStart_4479363 : Nat := 118140960795 + 4479363 * 2 ^ 59
def prefixEnd_4479363 : Nat := 4983230072969 + 3 ^ 40 * 4479363 * 2
def baseEnd_4479363 : Nat := 2300066244965663205362291

theorem tailTrace_4479363 : CollatzResearch.WordTrace tailWord_4479363 prefixEnd_4479363 2300066244965663205362291 := by
  unfold tailWord_4479363
  simp only [CollatzResearch.WordTrace]
  refine ⟨163375790471040340139610743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108917193647360226759740495 163375790471040340139610743)
  ·
    refine ⟨245063685706560510209416115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163375790471040340139610743 245063685706560510209416115)
    ·
      refine ⟨367595528559840765314124173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245063685706560510209416115 367595528559840765314124173)
      ·
        refine ⟨137848323209940286992796565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367595528559840765314124173 137848323209940286992796565)
        ·
          refine ⟨6461640150465950952787339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 137848323209940286992796565 6461640150465950952787339)
          ·
            refine ⟨9692460225698926429181009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461640150465950952787339 9692460225698926429181009)
            ·
              refine ⟨7269345169274194821885757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9692460225698926429181009 7269345169274194821885757)
              ·
                refine ⟨2726004438477823058207159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7269345169274194821885757 2726004438477823058207159)
                ·
                  refine ⟨4089006657716734587310739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726004438477823058207159 4089006657716734587310739)
                  ·
                    refine ⟨6133509986575101880966109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4089006657716734587310739 6133509986575101880966109)
                    ·
                      refine ⟨2300066244965663205362291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6133509986575101880966109 2300066244965663205362291)
                      ·
                        rfl

theorem cell23_4479363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_4479363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479363 prefixEnd_4479363 := by exact prefixLift 4479363
  have htrace : WordTrace (prefixWord ++ tailWord_4479363) baseStart_4479363 baseEnd_4479363 := by
    simpa [prefixWord, tailWord_4479363, baseEnd_4479363] using wordTrace_append hprefix tailTrace_4479363
  have hstable : (prefixWord ++ tailWord_4479363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479363).length < 2 ^ (prefixWord ++ tailWord_4479363).sum := by decide
  have hdescent : baseEnd_4479363 < baseStart_4479363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479365 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_4479365 : Nat := 118140960795 + 4479365 * 2 ^ 59
def prefixEnd_4479365 : Nat := 4983230072969 + 3 ^ 40 * 4479365 * 2
def baseEnd_4479365 : Nat := 2300067271926972197537281

theorem tailTrace_4479365 : CollatzResearch.WordTrace tailWord_4479365 prefixEnd_4479365 2300067271926972197537281 := by
  unfold tailWord_4479365
  simp only [CollatzResearch.WordTrace]
  refine ⟨163375863417033094481183549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108917242278022062987455699 163375863417033094481183549)
  ·
    refine ⟨61265948781387410430443831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163375863417033094481183549 61265948781387410430443831)
    ·
      refine ⟨91898923172081115645665747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61265948781387410430443831 91898923172081115645665747)
      ·
        refine ⟨137848384758121673468498621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91898923172081115645665747 137848384758121673468498621)
        ·
          refine ⟨51693144284295627550686983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137848384758121673468498621 51693144284295627550686983)
          ·
            refine ⟨77539716426443441326030475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51693144284295627550686983 77539716426443441326030475)
            ·
              refine ⟨116309574639665161989045713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77539716426443441326030475 116309574639665161989045713)
              ·
                refine ⟨87232180979748871491784285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116309574639665161989045713 87232180979748871491784285)
                ·
                  refine ⟨32712067867405826809419107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87232180979748871491784285 32712067867405826809419107)
                  ·
                    refine ⟨49068101801108740214128661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32712067867405826809419107 49068101801108740214128661)
                    ·
                      refine ⟨2300067271926972197537281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49068101801108740214128661 2300067271926972197537281)
                      ·
                        rfl

theorem cell23_4479365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_4479365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479365 prefixEnd_4479365 := by exact prefixLift 4479365
  have htrace : WordTrace (prefixWord ++ tailWord_4479365) baseStart_4479365 baseEnd_4479365 := by
    simpa [prefixWord, tailWord_4479365, baseEnd_4479365] using wordTrace_append hprefix tailTrace_4479365
  have hstable : (prefixWord ++ tailWord_4479365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479365).length < 2 ^ (prefixWord ++ tailWord_4479365).sum := by decide
  have hdescent : baseEnd_4479365 < baseStart_4479365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479369 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 4]
def baseStart_4479369 : Nat := 118140960795 + 4479369 * 2 ^ 59
def prefixEnd_4479369 : Nat := 4983230072969 + 3 ^ 40 * 4479369 * 2
def baseEnd_4479369 : Nat := 2300069325849590181887263

theorem tailTrace_4479369 : CollatzResearch.WordTrace tailWord_4479369 prefixEnd_4479369 2300069325849590181887263 := by
  unfold tailWord_4479369
  simp only [CollatzResearch.WordTrace]
  refine ⟨163376009309018603164329161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108917339539345735442886107 163376009309018603164329161)
  ·
    refine ⟨122532006981763952373246871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163376009309018603164329161 122532006981763952373246871)
    ·
      refine ⟨183798010472645928559870307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122532006981763952373246871 183798010472645928559870307)
      ·
        refine ⟨275697015708968892839805461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183798010472645928559870307 275697015708968892839805461)
        ·
          refine ⟨12923297611357916851865881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 275697015708968892839805461 12923297611357916851865881)
          ·
            refine ⟨9692473208518437638899411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12923297611357916851865881 9692473208518437638899411)
            ·
              refine ⟨14538709812777656458349117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9692473208518437638899411 14538709812777656458349117)
              ·
                refine ⟨5452016179791621171880919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14538709812777656458349117 5452016179791621171880919)
                ·
                  refine ⟨8178024269687431757821379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5452016179791621171880919 8178024269687431757821379)
                  ·
                    refine ⟨12267036404531147636732069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8178024269687431757821379 12267036404531147636732069)
                    ·
                      refine ⟨2300069325849590181887263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12267036404531147636732069 2300069325849590181887263)
                      ·
                        rfl

theorem cell23_4479369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 1, 4].length) (baseStart_4479369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479369 prefixEnd_4479369 := by exact prefixLift 4479369
  have htrace : WordTrace (prefixWord ++ tailWord_4479369) baseStart_4479369 baseEnd_4479369 := by
    simpa [prefixWord, tailWord_4479369, baseEnd_4479369] using wordTrace_append hprefix tailTrace_4479369
  have hstable : (prefixWord ++ tailWord_4479369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479369).length < 2 ^ (prefixWord ++ tailWord_4479369).sum := by decide
  have hdescent : baseEnd_4479369 < baseStart_4479369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479386 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2]
def baseStart_4479386 : Nat := 118140960795 + 4479386 * 2 ^ 59
def prefixEnd_4479386 : Nat := 4983230072969 + 3 ^ 40 * 4479386 * 2
def baseEnd_4479386 : Nat := 2300078055020716615374685

theorem tailTrace_4479386 : CollatzResearch.WordTrace tailWord_4479386 prefixEnd_4479386 2300078055020716615374685 := by
  unfold tailWord_4479386
  simp only [CollatzResearch.WordTrace]
  refine ⟨40844157337489253766924503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108917752899971343378465341 40844157337489253766924503)
  ·
    refine ⟨61266236006233880650386755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40844157337489253766924503 61266236006233880650386755)
    ·
      refine ⟨91899354009350820975580133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61266236006233880650386755 91899354009350820975580133)
      ·
        refine ⟨17231128876753278932921275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91899354009350820975580133 17231128876753278932921275)
        ·
          refine ⟨25846693315129918399381913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17231128876753278932921275 25846693315129918399381913)
          ·
            refine ⟨19385019986347438799536435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25846693315129918399381913 19385019986347438799536435)
            ·
              refine ⟨29077529979521158199304653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19385019986347438799536435 29077529979521158199304653)
              ·
                refine ⟨10904073742320434324739245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29077529979521158199304653 10904073742320434324739245)
                ·
                  refine ⟨4089027653370162871777217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10904073742320434324739245 4089027653370162871777217)
                  ·
                    refine ⟨3066770740027622153832913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089027653370162871777217 3066770740027622153832913)
                    ·
                      refine ⟨2300078055020716615374685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066770740027622153832913 2300078055020716615374685)
                      ·
                        rfl

theorem cell23_4479386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_4479386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479386 prefixEnd_4479386 := by exact prefixLift 4479386
  have htrace : WordTrace (prefixWord ++ tailWord_4479386) baseStart_4479386 baseEnd_4479386 := by
    simpa [prefixWord, tailWord_4479386, baseEnd_4479386] using wordTrace_append hprefix tailTrace_4479386
  have hstable : (prefixWord ++ tailWord_4479386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479386).length < 2 ^ (prefixWord ++ tailWord_4479386).sum := by decide
  have hdescent : baseEnd_4479386 < baseStart_4479386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479389 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_4479389 : Nat := 118140960795 + 4479389 * 2 ^ 59
def prefixEnd_4479389 : Nat := 4983230072969 + 3 ^ 40 * 4479389 * 2
def baseEnd_4479389 : Nat := 2300079595462680103637171

theorem tailTrace_4479389 : CollatzResearch.WordTrace tailWord_4479389 prefixEnd_4479389 2300079595462680103637171 := by
  unfold tailWord_4479389
  simp only [CollatzResearch.WordTrace]
  refine ⟨163376738768946146580057221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108917825845964097720038147 163376738768946146580057221)
  ·
    refine ⟨30633138519177402483760729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163376738768946146580057221 30633138519177402483760729)
    ·
      refine ⟨22974853889383051862820547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30633138519177402483760729 22974853889383051862820547)
      ·
        refine ⟨34462280834074577794230821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22974853889383051862820547 34462280834074577794230821)
        ·
          refine ⟨6461677656388983336418279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34462280834074577794230821 6461677656388983336418279)
          ·
            refine ⟨9692516484583475004627419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6461677656388983336418279 9692516484583475004627419)
            ·
              refine ⟨14538774726875212506941129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9692516484583475004627419 14538774726875212506941129)
              ·
                refine ⟨10904081045156409380205847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14538774726875212506941129 10904081045156409380205847)
                ·
                  refine ⟨16356121567734614070308771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10904081045156409380205847 16356121567734614070308771)
                  ·
                    refine ⟨24534182351601921105463157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16356121567734614070308771 24534182351601921105463157)
                    ·
                      refine ⟨2300079595462680103637171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24534182351601921105463157 2300079595462680103637171)
                      ·
                        rfl

theorem cell23_4479389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_4479389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479389 prefixEnd_4479389 := by exact prefixLift 4479389
  have htrace : WordTrace (prefixWord ++ tailWord_4479389) baseStart_4479389 baseEnd_4479389 := by
    simpa [prefixWord, tailWord_4479389, baseEnd_4479389] using wordTrace_append hprefix tailTrace_4479389
  have hstable : (prefixWord ++ tailWord_4479389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479389).length < 2 ^ (prefixWord ++ tailWord_4479389).sum := by decide
  have hdescent : baseEnd_4479389 < baseStart_4479389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479399 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_4479399 : Nat := 118140960795 + 4479399 * 2 ^ 59
def prefixEnd_4479399 : Nat := 4983230072969 + 3 ^ 40 * 4479399 * 2
def baseEnd_4479399 : Nat := 2300084730269225064512125

theorem tailTrace_4479399 : CollatzResearch.WordTrace tailWord_4479399 prefixEnd_4479399 2300084730269225064512125 := by
  unfold tailWord_4479399
  simp only [CollatzResearch.WordTrace]
  refine ⟨163377103498909918287921251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108918068999273278858614167 163377103498909918287921251)
  ·
    refine ⟨245065655248364877431881877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163377103498909918287921251 245065655248364877431881877)
    ·
      refine ⟨11487452589767103629619463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 245065655248364877431881877 11487452589767103629619463)
      ·
        refine ⟨17231178884650655444429195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11487452589767103629619463 17231178884650655444429195)
        ·
          refine ⟨25846768326975983166643793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17231178884650655444429195 25846768326975983166643793)
          ·
            refine ⟨19385076245231987374982845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25846768326975983166643793 19385076245231987374982845)
            ·
              refine ⟨7269403591961995265618567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19385076245231987374982845 7269403591961995265618567)
              ·
                refine ⟨10904105387942992898427851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7269403591961995265618567 10904105387942992898427851)
                ·
                  refine ⟨16356158081914489347641777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10904105387942992898427851 16356158081914489347641777)
                  ·
                    refine ⟨12267118561435867010731333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16356158081914489347641777 12267118561435867010731333)
                    ·
                      refine ⟨2300084730269225064512125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12267118561435867010731333 2300084730269225064512125)
                      ·
                        rfl

theorem cell23_4479399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_4479399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479399 prefixEnd_4479399 := by exact prefixLift 4479399
  have htrace : WordTrace (prefixWord ++ tailWord_4479399) baseStart_4479399 baseEnd_4479399 := by
    simpa [prefixWord, tailWord_4479399, baseEnd_4479399] using wordTrace_append hprefix tailTrace_4479399
  have hstable : (prefixWord ++ tailWord_4479399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479399).length < 2 ^ (prefixWord ++ tailWord_4479399).sum := by decide
  have hdescent : baseEnd_4479399 < baseStart_4479399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479409 : List Nat := [1, 2, 2, 4, 1, 4, 2, 7]
def baseStart_4479409 : Nat := 118140960795 + 4479409 * 2 ^ 59
def prefixEnd_4479409 : Nat := 4983230072969 + 3 ^ 40 * 4479409 * 2
def baseEnd_4479409 : Nat := 85188513521324815755077

theorem tailTrace_4479409 : CollatzResearch.WordTrace tailWord_4479409 prefixEnd_4479409 85188513521324815755077 := by
  unfold tailWord_4479409
  simp only [CollatzResearch.WordTrace]
  refine ⟨163377468228873689995785281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108918312152582459997190187 163377468228873689995785281)
  ·
    refine ⟨122533101171655267496838961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163377468228873689995785281 122533101171655267496838961)
    ·
      refine ⟨91899825878741450622629221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122533101171655267496838961 91899825878741450622629221)
      ·
        refine ⟨17231217352264021991742979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91899825878741450622629221 17231217352264021991742979)
        ·
          refine ⟨25846826028396032987614469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17231217352264021991742979 25846826028396032987614469)
          ·
            refine ⟨4846279880324256185177713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25846826028396032987614469 4846279880324256185177713)
            ·
              refine ⟨3634709910243192138883285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4846279880324256185177713 3634709910243192138883285)
              ·
                refine ⟨85188513521324815755077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3634709910243192138883285 85188513521324815755077)
                ·
                  rfl

theorem cell23_4479409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 7].length) (baseStart_4479409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479409 prefixEnd_4479409 := by exact prefixLift 4479409
  have htrace : WordTrace (prefixWord ++ tailWord_4479409) baseStart_4479409 baseEnd_4479409 := by
    simpa [prefixWord, tailWord_4479409, baseEnd_4479409] using wordTrace_append hprefix tailTrace_4479409
  have hstable : (prefixWord ++ tailWord_4479409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479409).length < 2 ^ (prefixWord ++ tailWord_4479409).sum := by decide
  have hdescent : baseEnd_4479409 < baseStart_4479409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479420 : List Nat := [2, 2, 2, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_4479420 : Nat := 118140960795 + 4479420 * 2 ^ 59
def prefixEnd_4479420 : Nat := 4983230072969 + 3 ^ 40 * 4479420 * 2
def baseEnd_4479420 : Nat := 2300095513362969482349529

theorem tailTrace_4479420 : CollatzResearch.WordTrace tailWord_4479420 prefixEnd_4479420 2300095513362969482349529 := by
  unfold tailWord_4479420
  simp only [CollatzResearch.WordTrace]
  refine ⟨81688934715916919437217857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108918579621222559249623809 81688934715916919437217857)
  ·
    refine ⟨61266701036937689577913393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81688934715916919437217857 61266701036937689577913393)
    ·
      refine ⟨45950025777703267183435045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61266701036937689577913393 45950025777703267183435045)
      ·
        refine ⟨8615629833319362596894071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45950025777703267183435045 8615629833319362596894071)
        ·
          refine ⟨12923444749979043895341107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8615629833319362596894071 12923444749979043895341107)
          ·
            refine ⟨19385167124968565843011661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12923444749979043895341107 19385167124968565843011661)
            ·
              refine ⟨7269437671863212191129373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19385167124968565843011661 7269437671863212191129373)
              ·
                refine ⟨2726039126948704571673515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7269437671863212191129373 2726039126948704571673515)
                ·
                  refine ⟨4089058690423056857510273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726039126948704571673515 4089058690423056857510273)
                  ·
                    refine ⟨3066794017817292643132705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089058690423056857510273 3066794017817292643132705)
                    ·
                      refine ⟨2300095513362969482349529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066794017817292643132705 2300095513362969482349529)
                      ·
                        rfl

theorem cell23_4479420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_4479420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479420 prefixEnd_4479420 := by exact prefixLift 4479420
  have htrace : WordTrace (prefixWord ++ tailWord_4479420) baseStart_4479420 baseEnd_4479420 := by
    simpa [prefixWord, tailWord_4479420, baseEnd_4479420] using wordTrace_append hprefix tailTrace_4479420
  have hstable : (prefixWord ++ tailWord_4479420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479420).length < 2 ^ (prefixWord ++ tailWord_4479420).sum := by decide
  have hdescent : baseEnd_4479420 < baseStart_4479420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479509 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_4479509 : Nat := 118140960795 + 4479509 * 2 ^ 59
def prefixEnd_4479509 : Nat := 4983230072969 + 3 ^ 40 * 4479509 * 2
def baseEnd_4479509 : Nat := 2300141213141219634136619

theorem tailTrace_4479509 : CollatzResearch.WordTrace tailWord_4479509 prefixEnd_4479509 2300141213141219634136619 := by
  unfold tailWord_4479509
  simp only [CollatzResearch.WordTrace]
  refine ⟨163381115528511407074425581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108920743685674271382950387 163381115528511407074425581)
  ·
    refine ⟨61267918323191777652909593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163381115528511407074425581 61267918323191777652909593)
    ·
      refine ⟨45950938742393833239682195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61267918323191777652909593 45950938742393833239682195)
      ·
        refine ⟨68926408113590749859523293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45950938742393833239682195 68926408113590749859523293)
        ·
          refine ⟨25847403042596531197321235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68926408113590749859523293 25847403042596531197321235)
          ·
            refine ⟨38771104563894796795981853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25847403042596531197321235 38771104563894796795981853)
            ·
              refine ⟨14539164211460548798493195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38771104563894796795981853 14539164211460548798493195)
              ·
                refine ⟨21808746317190823197739793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14539164211460548798493195 21808746317190823197739793)
                ·
                  refine ⟨16356559737893117398304845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21808746317190823197739793 16356559737893117398304845)
                  ·
                    refine ⟨6133709901709919024364317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16356559737893117398304845 6133709901709919024364317)
                    ·
                      refine ⟨2300141213141219634136619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6133709901709919024364317 2300141213141219634136619)
                      ·
                        rfl

theorem cell23_4479509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_4479509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479509 prefixEnd_4479509 := by exact prefixLift 4479509
  have htrace : WordTrace (prefixWord ++ tailWord_4479509) baseStart_4479509 baseEnd_4479509 := by
    simpa [prefixWord, tailWord_4479509, baseEnd_4479509] using wordTrace_append hprefix tailTrace_4479509
  have hstable : (prefixWord ++ tailWord_4479509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479509).length < 2 ^ (prefixWord ++ tailWord_4479509).sum := by decide
  have hdescent : baseEnd_4479509 < baseStart_4479509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479519 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 4, 5, 2]
def baseStart_4479519 : Nat := 118140960795 + 4479519 * 2 ^ 59
def prefixEnd_4479519 : Nat := 4983230072969 + 3 ^ 40 * 4479519 * 2
def baseEnd_4479519 : Nat := 2300146347947764595011573

theorem tailTrace_4479519 : CollatzResearch.WordTrace tailWord_4479519 prefixEnd_4479519 2300146347947764595011573 := by
  unfold tailWord_4479519
  simp only [CollatzResearch.WordTrace]
  refine ⟨163381480258475178782289611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108920986838983452521526407 163381480258475178782289611)
  ·
    refine ⟨245072220387712768173434417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163381480258475178782289611 245072220387712768173434417)
    ·
      refine ⟨183804165290784576130075813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245072220387712768173434417 183804165290784576130075813)
      ·
        refine ⟨34463280992022108024389215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183804165290784576130075813 34463280992022108024389215)
        ·
          refine ⟨51694921488033162036583823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34463280992022108024389215 51694921488033162036583823)
          ·
            refine ⟨77542382232049743054875735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51694921488033162036583823 77542382232049743054875735)
            ·
              refine ⟨116313573348074614582313603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77542382232049743054875735 116313573348074614582313603)
              ·
                refine ⟨174470360022111921873470405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116313573348074614582313603 174470360022111921873470405)
                ·
                  refine ⟨32713192504145985351275701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174470360022111921873470405 32713192504145985351275701)
                  ·
                    refine ⟨3066861797263686126682097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32713192504145985351275701 3066861797263686126682097)
                    ·
                      refine ⟨2300146347947764595011573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066861797263686126682097 2300146347947764595011573)
                      ·
                        rfl

theorem cell23_4479519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_4479519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479519 prefixEnd_4479519 := by exact prefixLift 4479519
  have htrace : WordTrace (prefixWord ++ tailWord_4479519) baseStart_4479519 baseEnd_4479519 := by
    simpa [prefixWord, tailWord_4479519, baseEnd_4479519] using wordTrace_append hprefix tailTrace_4479519
  have hstable : (prefixWord ++ tailWord_4479519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479519).length < 2 ^ (prefixWord ++ tailWord_4479519).sum := by decide
  have hdescent : baseEnd_4479519 < baseStart_4479519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479552 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_4479552 : Nat := 118140960795 + 4479552 * 2 ^ 59
def prefixEnd_4479552 : Nat := 4983230072969 + 3 ^ 40 * 4479552 * 2
def baseEnd_4479552 : Nat := 2300163292809362965898921

theorem tailTrace_4479552 : CollatzResearch.WordTrace tailWord_4479552 prefixEnd_4479552 2300163292809362965898921 := by
  unfold tailWord_4479552
  simp only [CollatzResearch.WordTrace]
  refine ⟨81691341933677812709120455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108921789244903750278827273 81691341933677812709120455)
  ·
    refine ⟨122537012900516719063680683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81691341933677812709120455 122537012900516719063680683)
    ·
      refine ⟨183805519350775078595521025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122537012900516719063680683 183805519350775078595521025)
      ·
        refine ⟨137854139513081308946640769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183805519350775078595521025 137854139513081308946640769)
        ·
          refine ⟨103390604634810981709980577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137854139513081308946640769 103390604634810981709980577)
          ·
            refine ⟨77542953476108236282485433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103390604634810981709980577 77542953476108236282485433)
            ·
              refine ⟨58157215107081177211864075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77542953476108236282485433 58157215107081177211864075)
              ·
                refine ⟨87235822660621765817796113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58157215107081177211864075 87235822660621765817796113)
                ·
                  refine ⟨65426866995466324363347085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87235822660621765817796113 65426866995466324363347085)
                  ·
                    refine ⟨24535075123299871636255157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65426866995466324363347085 24535075123299871636255157)
                    ·
                      refine ⟨2300163292809362965898921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24535075123299871636255157 2300163292809362965898921)
                      ·
                        rfl

theorem cell23_4479552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_4479552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479552 prefixEnd_4479552 := by exact prefixLift 4479552
  have htrace : WordTrace (prefixWord ++ tailWord_4479552) baseStart_4479552 baseEnd_4479552 := by
    simpa [prefixWord, tailWord_4479552, baseEnd_4479552] using wordTrace_append hprefix tailTrace_4479552
  have hstable : (prefixWord ++ tailWord_4479552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479552).length < 2 ^ (prefixWord ++ tailWord_4479552).sum := by decide
  have hdescent : baseEnd_4479552 < baseStart_4479552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479566 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_4479566 : Nat := 118140960795 + 4479566 * 2 ^ 59
def prefixEnd_4479566 : Nat := 4983230072969 + 3 ^ 40 * 4479566 * 2
def baseEnd_4479566 : Nat := 2300170481538525911123857

theorem tailTrace_4479566 : CollatzResearch.WordTrace tailWord_4479566 prefixEnd_4479566 2300170481538525911123857 := by
  unfold tailWord_4479566
  simp only [CollatzResearch.WordTrace]
  refine ⟨20422899311163113226156319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108922129659536603872833701 20422899311163113226156319)
  ·
    refine ⟨30634348966744669839234479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20422899311163113226156319 30634348966744669839234479)
    ·
      refine ⟨45951523450117004758851719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30634348966744669839234479 45951523450117004758851719)
      ·
        refine ⟨68927285175175507138277579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45951523450117004758851719 68927285175175507138277579)
        ·
          refine ⟨103390927762763260707416369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68927285175175507138277579 103390927762763260707416369)
          ·
            refine ⟨77543195822072445530562277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103390927762763260707416369 77543195822072445530562277)
            ·
              refine ⟨14539349216638583536980427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77543195822072445530562277 14539349216638583536980427)
              ·
                refine ⟨21809023824957875305470641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14539349216638583536980427 21809023824957875305470641)
                ·
                  refine ⟨16356767868718406479102981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21809023824957875305470641 16356767868718406479102981)
                  ·
                    refine ⟨3066893975384701214831809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16356767868718406479102981 3066893975384701214831809)
                    ·
                      refine ⟨2300170481538525911123857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066893975384701214831809 2300170481538525911123857)
                      ·
                        rfl

theorem cell23_4479566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_4479566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479566 prefixEnd_4479566 := by exact prefixLift 4479566
  have htrace : WordTrace (prefixWord ++ tailWord_4479566) baseStart_4479566 baseEnd_4479566 := by
    simpa [prefixWord, tailWord_4479566, baseEnd_4479566] using wordTrace_append hprefix tailTrace_4479566
  have hstable : (prefixWord ++ tailWord_4479566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479566).length < 2 ^ (prefixWord ++ tailWord_4479566).sum := by decide
  have hdescent : baseEnd_4479566 < baseStart_4479566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479569 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_4479569 : Nat := 118140960795 + 4479569 * 2 ^ 59
def prefixEnd_4479569 : Nat := 4983230072969 + 3 ^ 40 * 4479569 * 2
def baseEnd_4479569 : Nat := 2300172021980489399386343

theorem tailTrace_4479569 : CollatzResearch.WordTrace tailWord_4479569 prefixEnd_4479569 2300172021980489399386343 := by
  unfold tailWord_4479569
  simp only [CollatzResearch.WordTrace]
  refine ⟨163383303908294037321609761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108922202605529358214406507 163383303908294037321609761)
  ·
    refine ⟨122537477931220527991207321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163383303908294037321609761 122537477931220527991207321)
    ·
      refine ⟨91903108448415395993405491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122537477931220527991207321 91903108448415395993405491)
      ·
        refine ⟨137854662672623093990108237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91903108448415395993405491 137854662672623093990108237)
        ·
          refine ⟨51695498502233660246290589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137854662672623093990108237 51695498502233660246290589)
          ·
            refine ⟨19385811938337622592358971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51695498502233660246290589 19385811938337622592358971)
            ·
              refine ⟨29078717907506433888538457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19385811938337622592358971 29078717907506433888538457)
              ·
                refine ⟨21809038430629825416403843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29078717907506433888538457 21809038430629825416403843)
                ·
                  refine ⟨32713557645944738124605765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21809038430629825416403843 32713557645944738124605765)
                  ·
                    refine ⟨6133792058614638398363581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32713557645944738124605765 6133792058614638398363581)
                    ·
                      refine ⟨2300172021980489399386343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6133792058614638398363581 2300172021980489399386343)
                      ·
                        rfl

theorem cell23_4479569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_4479569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479569 prefixEnd_4479569 := by exact prefixLift 4479569
  have htrace : WordTrace (prefixWord ++ tailWord_4479569) baseStart_4479569 baseEnd_4479569 := by
    simpa [prefixWord, tailWord_4479569, baseEnd_4479569] using wordTrace_append hprefix tailTrace_4479569
  have hstable : (prefixWord ++ tailWord_4479569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479569).length < 2 ^ (prefixWord ++ tailWord_4479569).sum := by decide
  have hdescent : baseEnd_4479569 < baseStart_4479569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479667 : List Nat := [1, 1, 1, 2, 3, 6, 2, 2, 1, 1, 3]
def baseStart_4479667 : Nat := 118140960795 + 4479667 * 2 ^ 59
def prefixEnd_4479667 : Nat := 4983230072969 + 3 ^ 40 * 4479667 * 2
def baseEnd_4479667 : Nat := 2300222343084630015960893

theorem tailTrace_4479667 : CollatzResearch.WordTrace tailWord_4479667 prefixEnd_4479667 2300222343084630015960893 := by
  unfold tailWord_4479667
  simp only [CollatzResearch.WordTrace]
  refine ⟨163386878261939000058677255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108924585507959333372451503 163386878261939000058677255)
  ·
    refine ⟨245080317392908500088015883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163386878261939000058677255 245080317392908500088015883)
    ·
      refine ⟨367620476089362750132023825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245080317392908500088015883 367620476089362750132023825)
      ·
        refine ⟨275715357067022062599017869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367620476089362750132023825 275715357067022062599017869)
        ·
          refine ⟨103393258900133273474631701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275715357067022062599017869 103393258900133273474631701)
          ·
            refine ⟨4846559010943747194123361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103393258900133273474631701 4846559010943747194123361)
            ·
              refine ⟨3634919258207810395592521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4846559010943747194123361 3634919258207810395592521)
              ·
                refine ⟨2726189443655857796694391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3634919258207810395592521 2726189443655857796694391)
                ·
                  refine ⟨4089284165483786695041587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726189443655857796694391 4089284165483786695041587)
                  ·
                    refine ⟨6133926248225680042562381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4089284165483786695041587 6133926248225680042562381)
                    ·
                      refine ⟨2300222343084630015960893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6133926248225680042562381 2300222343084630015960893)
                      ·
                        rfl

theorem cell23_4479667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 1, 3].length) (baseStart_4479667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479667 prefixEnd_4479667 := by exact prefixLift 4479667
  have htrace : WordTrace (prefixWord ++ tailWord_4479667) baseStart_4479667 baseEnd_4479667 := by
    simpa [prefixWord, tailWord_4479667, baseEnd_4479667] using wordTrace_append hprefix tailTrace_4479667
  have hstable : (prefixWord ++ tailWord_4479667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479667).length < 2 ^ (prefixWord ++ tailWord_4479667).sum := by decide
  have hdescent : baseEnd_4479667 < baseStart_4479667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479673 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 3, 2, 2]
def baseStart_4479673 : Nat := 118140960795 + 4479673 * 2 ^ 59
def prefixEnd_4479673 : Nat := 4983230072969 + 3 ^ 40 * 4479673 * 2
def baseEnd_4479673 : Nat := 2300225423968556992485865

theorem tailTrace_4479673 : CollatzResearch.WordTrace tailWord_4479673 prefixEnd_4479673 2300225423968556992485865 := by
  unfold tailWord_4479673
  simp only [CollatzResearch.WordTrace]
  refine ⟨163387097099917263083395673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108924731399944842055597115 163387097099917263083395673)
  ·
    refine ⟨122540322824937947312546755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163387097099917263083395673 122540322824937947312546755)
    ·
      refine ⟨183810484237406920968820133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122540322824937947312546755 183810484237406920968820133)
      ·
        refine ⟨34464465794513797681653775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183810484237406920968820133 34464465794513797681653775)
        ·
          refine ⟨51696698691770696522480663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34464465794513797681653775 51696698691770696522480663)
          ·
            refine ⟨77545048037656044783720995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51696698691770696522480663 77545048037656044783720995)
            ·
              refine ⟨116317572056484067175581493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77545048037656044783720995 116317572056484067175581493)
              ·
                refine ⟨10904772380295381297710765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116317572056484067175581493 10904772380295381297710765)
                ·
                  refine ⟨4089289642610767986641537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10904772380295381297710765 4089289642610767986641537)
                  ·
                    refine ⟨3066967231958075989981153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089289642610767986641537 3066967231958075989981153)
                    ·
                      refine ⟨2300225423968556992485865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066967231958075989981153 2300225423968556992485865)
                      ·
                        rfl

theorem cell23_4479673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_4479673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479673 prefixEnd_4479673 := by exact prefixLift 4479673
  have htrace : WordTrace (prefixWord ++ tailWord_4479673) baseStart_4479673 baseEnd_4479673 := by
    simpa [prefixWord, tailWord_4479673, baseEnd_4479673] using wordTrace_append hprefix tailTrace_4479673
  have hstable : (prefixWord ++ tailWord_4479673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479673).length < 2 ^ (prefixWord ++ tailWord_4479673).sum := by decide
  have hdescent : baseEnd_4479673 < baseStart_4479673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479676 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_4479676 : Nat := 118140960795 + 4479676 * 2 ^ 59
def prefixEnd_4479676 : Nat := 4983230072969 + 3 ^ 40 * 4479676 * 2
def baseEnd_4479676 : Nat := 2300226964410520480748351

theorem tailTrace_4479676 : CollatzResearch.WordTrace tailWord_4479676 prefixEnd_4479676 2300226964410520480748351 := by
  unfold tailWord_4479676
  simp only [CollatzResearch.WordTrace]
  refine ⟨81693603259453197297877441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108924804345937596397169921 81693603259453197297877441)
  ·
    refine ⟨61270202444589897973408081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81693603259453197297877441 61270202444589897973408081)
    ·
      refine ⟨45952651833442423480056061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61270202444589897973408081 45952651833442423480056061)
      ·
        refine ⟨17232244437540908805021023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45952651833442423480056061 17232244437540908805021023)
        ·
          refine ⟨25848366656311363207531535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17232244437540908805021023 25848366656311363207531535)
          ·
            refine ⟨38772549984467044811297303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25848366656311363207531535 38772549984467044811297303)
            ·
              refine ⟨58158824976700567216945955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38772549984467044811297303 58158824976700567216945955)
              ·
                refine ⟨87238237465050850825418933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58158824976700567216945955 87238237465050850825418933)
                ·
                  refine ⟨8178584762348517264883025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87238237465050850825418933 8178584762348517264883025)
                  ·
                    refine ⟨6133938571761387948662269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8178584762348517264883025 6133938571761387948662269)
                    ·
                      refine ⟨2300226964410520480748351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6133938571761387948662269 2300226964410520480748351)
                      ·
                        rfl

theorem cell23_4479676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_4479676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479676 prefixEnd_4479676 := by exact prefixLift 4479676
  have htrace : WordTrace (prefixWord ++ tailWord_4479676) baseStart_4479676 baseEnd_4479676 := by
    simpa [prefixWord, tailWord_4479676, baseEnd_4479676] using wordTrace_append hprefix tailTrace_4479676
  have hstable : (prefixWord ++ tailWord_4479676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479676).length < 2 ^ (prefixWord ++ tailWord_4479676).sum := by decide
  have hdescent : baseEnd_4479676 < baseStart_4479676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479679 : List Nat := [1, 1, 2, 2, 2, 4, 3, 8]
def baseStart_4479679 : Nat := 118140960795 + 4479679 * 2 ^ 59
def prefixEnd_4479679 : Nat := 4983230072969 + 3 ^ 40 * 4479679 * 2
def baseEnd_4479679 : Nat := 85193648327869776630031

theorem tailTrace_4479679 : CollatzResearch.WordTrace tailWord_4479679 prefixEnd_4479679 85193648327869776630031 := by
  unfold tailWord_4479679
  simp only [CollatzResearch.WordTrace]
  refine ⟨163387315937895526108114091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108924877291930350738742727 163387315937895526108114091)
  ·
    refine ⟨245080973906843289162171137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163387315937895526108114091 245080973906843289162171137)
    ·
      refine ⟨183810730430132466871628353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245080973906843289162171137 183810730430132466871628353)
      ·
        refine ⟨137858047822599350153721265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183810730430132466871628353 137858047822599350153721265)
        ·
          refine ⟨103393535866949512615290949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137858047822599350153721265 103393535866949512615290949)
          ·
            refine ⟨19386287975053033615367053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103393535866949512615290949 19386287975053033615367053)
            ·
              refine ⟨7269857990644887605762645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19386287975053033615367053 7269857990644887605762645)
              ·
                refine ⟨85193648327869776630031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7269857990644887605762645 85193648327869776630031)
                ·
                  rfl

theorem cell23_4479679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 8].length) (baseStart_4479679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479679 prefixEnd_4479679 := by exact prefixLift 4479679
  have htrace : WordTrace (prefixWord ++ tailWord_4479679) baseStart_4479679 baseEnd_4479679 := by
    simpa [prefixWord, tailWord_4479679, baseEnd_4479679] using wordTrace_append hprefix tailTrace_4479679
  have hstable : (prefixWord ++ tailWord_4479679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479679).length < 2 ^ (prefixWord ++ tailWord_4479679).sum := by decide
  have hdescent : baseEnd_4479679 < baseStart_4479679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479690 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_4479690 : Nat := 118140960795 + 4479690 * 2 ^ 59
def prefixEnd_4479690 : Nat := 4983230072969 + 3 ^ 40 * 4479690 * 2
def baseEnd_4479690 : Nat := 2300234153139683425973287

theorem tailTrace_4479690 : CollatzResearch.WordTrace tailWord_4479690 prefixEnd_4479690 2300234153139683425973287 := by
  unfold tailWord_4479690
  simp only [CollatzResearch.WordTrace]
  refine ⟨40846929285213918746691131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108925144760570449991176349 40846929285213918746691131)
  ·
    refine ⟨61270393927820878120036697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40846929285213918746691131 61270393927820878120036697)
    ·
      refine ⟨45952795445865658590027523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61270393927820878120036697 45952795445865658590027523)
      ·
        refine ⟨68929193168798487885041285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45952795445865658590027523 68929193168798487885041285)
        ·
          refine ⟨12924223719149716478445241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68929193168798487885041285 12924223719149716478445241)
          ·
            refine ⟨9693167789362287358833931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12924223719149716478445241 9693167789362287358833931)
            ·
              refine ⟨14539751684043431038250897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9693167789362287358833931 14539751684043431038250897)
              ·
                refine ⟨10904813763032573278688173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14539751684043431038250897 10904813763032573278688173)
                ·
                  refine ⟨4089305161137214979508065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10904813763032573278688173 4089305161137214979508065)
                  ·
                    refine ⟨3066978870852911234631049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089305161137214979508065 3066978870852911234631049)
                    ·
                      refine ⟨2300234153139683425973287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3066978870852911234631049 2300234153139683425973287)
                      ·
                        rfl

theorem cell23_4479690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_4479690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479690 prefixEnd_4479690 := by exact prefixLift 4479690
  have htrace : WordTrace (prefixWord ++ tailWord_4479690) baseStart_4479690 baseEnd_4479690 := by
    simpa [prefixWord, tailWord_4479690, baseEnd_4479690] using wordTrace_append hprefix tailTrace_4479690
  have hstable : (prefixWord ++ tailWord_4479690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479690).length < 2 ^ (prefixWord ++ tailWord_4479690).sum := by decide
  have hdescent : baseEnd_4479690 < baseStart_4479690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479706 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_4479706 : Nat := 118140960795 + 4479706 * 2 ^ 59
def prefixEnd_4479706 : Nat := 4983230072969 + 3 ^ 40 * 4479706 * 2
def baseEnd_4479706 : Nat := 2300242368830155363373213

theorem tailTrace_4479706 : CollatzResearch.WordTrace tailWord_4479706 prefixEnd_4479706 2300242368830155363373213 := by
  unfold tailWord_4479706
  simp only [CollatzResearch.WordTrace]
  refine ⟨40847075177199427429836743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108925533805865139812897981 40847075177199427429836743)
  ·
    refine ⟨61270612765799141144755115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40847075177199427429836743 61270612765799141144755115)
    ·
      refine ⟨91905919148698711717132673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61270612765799141144755115 91905919148698711717132673)
      ·
        refine ⟨68929439361524033787849505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91905919148698711717132673 68929439361524033787849505)
        ·
          refine ⟨51697079521143025340887129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68929439361524033787849505 51697079521143025340887129)
          ·
            refine ⟨38772809640857269005665347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51697079521143025340887129 38772809640857269005665347)
            ·
              refine ⟨58159214461285903508498021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38772809640857269005665347 58159214461285903508498021)
              ·
                refine ⟨10904852711491106907843379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58159214461285903508498021 10904852711491106907843379)
                ·
                  refine ⟨16357279067236660361765069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10904852711491106907843379 16357279067236660361765069)
                  ·
                    refine ⟨6133979650213747635661901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16357279067236660361765069 6133979650213747635661901)
                    ·
                      refine ⟨2300242368830155363373213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6133979650213747635661901 2300242368830155363373213)
                      ·
                        rfl

theorem cell23_4479706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_4479706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479706 prefixEnd_4479706 := by exact prefixLift 4479706
  have htrace : WordTrace (prefixWord ++ tailWord_4479706) baseStart_4479706 baseEnd_4479706 := by
    simpa [prefixWord, tailWord_4479706, baseEnd_4479706] using wordTrace_append hprefix tailTrace_4479706
  have hstable : (prefixWord ++ tailWord_4479706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479706).length < 2 ^ (prefixWord ++ tailWord_4479706).sum := by decide
  have hdescent : baseEnd_4479706 < baseStart_4479706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479749 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_4479749 : Nat := 118140960795 + 4479749 * 2 ^ 59
def prefixEnd_4479749 : Nat := 4983230072969 + 3 ^ 40 * 4479749 * 2
def baseEnd_4479749 : Nat := 2300264448498298695135515

theorem tailTrace_4479749 : CollatzResearch.WordTrace tailWord_4479749 prefixEnd_4479749 2300264448498298695135515 := by
  unfold tailWord_4479749
  simp only [CollatzResearch.WordTrace]
  refine ⟨163389869047641928063162301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108926579365094618708774867 163389869047641928063162301)
  ·
    refine ⟨61271200892865723023685863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163389869047641928063162301 61271200892865723023685863)
    ·
      refine ⟨91906801339298584535528795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61271200892865723023685863 91906801339298584535528795)
      ·
        refine ⟨137860202008947876803293193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91906801339298584535528795 137860202008947876803293193)
        ·
          refine ⟨103395151506710907602469895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137860202008947876803293193 103395151506710907602469895)
          ·
            refine ⟨155092727260066361403704843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103395151506710907602469895 155092727260066361403704843)
            ·
              refine ⟨232639090890099542105557265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155092727260066361403704843 232639090890099542105557265)
              ·
                refine ⟨174479318167574656579167949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232639090890099542105557265 174479318167574656579167949)
                ·
                  refine ⟨65429744312840496217187981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174479318167574656579167949 65429744312840496217187981)
                  ·
                    refine ⟨24536154117315186081445493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65429744312840496217187981 24536154117315186081445493)
                    ·
                      refine ⟨2300264448498298695135515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24536154117315186081445493 2300264448498298695135515)
                      ·
                        rfl

theorem cell23_4479749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_4479749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479749 prefixEnd_4479749 := by exact prefixLift 4479749
  have htrace : WordTrace (prefixWord ++ tailWord_4479749) baseStart_4479749 baseEnd_4479749 := by
    simpa [prefixWord, tailWord_4479749, baseEnd_4479749] using wordTrace_append hprefix tailTrace_4479749
  have hstable : (prefixWord ++ tailWord_4479749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479749).length < 2 ^ (prefixWord ++ tailWord_4479749).sum := by decide
  have hdescent : baseEnd_4479749 < baseStart_4479749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479763 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 6, 2, 2]
def baseStart_4479763 : Nat := 118140960795 + 4479763 * 2 ^ 59
def prefixEnd_4479763 : Nat := 4983230072969 + 3 ^ 40 * 4479763 * 2
def baseEnd_4479763 : Nat := 2300271637227461640360451

theorem tailTrace_4479763 : CollatzResearch.WordTrace tailWord_4479763 prefixEnd_4479763 2300271637227461640360451 := by
  unfold tailWord_4479763
  simp only [CollatzResearch.WordTrace]
  refine ⟨163390379669591208454171943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108926919779727472302781295 163390379669591208454171943)
  ·
    refine ⟨245085569504386812681257915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163390379669591208454171943 245085569504386812681257915)
    ·
      refine ⟨367628354256580219021886873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245085569504386812681257915 367628354256580219021886873)
      ·
        refine ⟨275721265692435164266415155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367628354256580219021886873 275721265692435164266415155)
        ·
          refine ⟨413581898538652746399622733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275721265692435164266415155 413581898538652746399622733)
          ·
            refine ⟨155093211951994779899858525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 413581898538652746399622733 155093211951994779899858525)
            ·
              refine ⟨58159954481998042462446947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155093211951994779899858525 58159954481998042462446947)
              ·
                refine ⟨87239931722997063693670421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58159954481998042462446947 87239931722997063693670421)
                ·
                  refine ⟨4089371799515487360640801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87239931722997063693670421 4089371799515487360640801)
                  ·
                    refine ⟨3067028849636615520480601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089371799515487360640801 3067028849636615520480601)
                    ·
                      refine ⟨2300271637227461640360451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067028849636615520480601 2300271637227461640360451)
                      ·
                        rfl

theorem cell23_4479763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 2, 2].length) (baseStart_4479763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479763 prefixEnd_4479763 := by exact prefixLift 4479763
  have htrace : WordTrace (prefixWord ++ tailWord_4479763) baseStart_4479763 baseEnd_4479763 := by
    simpa [prefixWord, tailWord_4479763, baseEnd_4479763] using wordTrace_append hprefix tailTrace_4479763
  have hstable : (prefixWord ++ tailWord_4479763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479763).length < 2 ^ (prefixWord ++ tailWord_4479763).sum := by decide
  have hdescent : baseEnd_4479763 < baseStart_4479763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479779 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 9]
def baseStart_4479779 : Nat := 118140960795 + 4479779 * 2 ^ 59
def prefixEnd_4479779 : Nat := 4983230072969 + 3 ^ 40 * 4479779 * 2
def baseEnd_4479779 : Nat := 2300279852917933577760377

theorem tailTrace_4479779 : CollatzResearch.WordTrace tailWord_4479779 prefixEnd_4479779 2300279852917933577760377 := by
  unfold tailWord_4479779
  simp only [CollatzResearch.WordTrace]
  refine ⟨163390963237533243186754391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108927308825022162124502927 163390963237533243186754391)
  ·
    refine ⟨245086444856299864780131587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163390963237533243186754391 245086444856299864780131587)
    ·
      refine ⟨367629667284449797170197381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245086444856299864780131587 367629667284449797170197381)
      ·
        refine ⟨68930562615834336969412009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 367629667284449797170197381 68930562615834336969412009)
        ·
          refine ⟨51697921961875752727059007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68930562615834336969412009 51697921961875752727059007)
          ·
            refine ⟨77546882942813629090588511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51697921961875752727059007 77546882942813629090588511)
            ·
              refine ⟨116320324414220443635882767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77546882942813629090588511 116320324414220443635882767)
              ·
                refine ⟨174480486621330665453824151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116320324414220443635882767 174480486621330665453824151)
                ·
                  refine ⟨261720729931995998180736227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174480486621330665453824151 261720729931995998180736227)
                  ·
                    refine ⟨392581094897993997271104341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 261720729931995998180736227 392581094897993997271104341)
                    ·
                      refine ⟨2300279852917933577760377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 392581094897993997271104341 2300279852917933577760377)
                      ·
                        rfl

theorem cell23_4479779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_4479779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479779 prefixEnd_4479779 := by exact prefixLift 4479779
  have htrace : WordTrace (prefixWord ++ tailWord_4479779) baseStart_4479779 baseEnd_4479779 := by
    simpa [prefixWord, tailWord_4479779, baseEnd_4479779] using wordTrace_append hprefix tailTrace_4479779
  have hstable : (prefixWord ++ tailWord_4479779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479779).length < 2 ^ (prefixWord ++ tailWord_4479779).sum := by decide
  have hdescent : baseEnd_4479779 < baseStart_4479779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479797 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_4479797 : Nat := 118140960795 + 4479797 * 2 ^ 59
def prefixEnd_4479797 : Nat := 4983230072969 + 3 ^ 40 * 4479797 * 2
def baseEnd_4479797 : Nat := 2300289095569714507335295

theorem tailTrace_4479797 : CollatzResearch.WordTrace tailWord_4479797 prefixEnd_4479797 2300289095569714507335295 := by
  unfold tailWord_4479797
  simp only [CollatzResearch.WordTrace]
  refine ⟨163391619751468032260909645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108927746500978688173939763 163391619751468032260909645)
  ·
    refine ⟨61271857406800512097841117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163391619751468032260909645 61271857406800512097841117)
    ·
      refine ⟨22976946527550192036690419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61271857406800512097841117 22976946527550192036690419)
      ·
        refine ⟨34465419791325288055035629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22976946527550192036690419 34465419791325288055035629)
        ·
          refine ⟨12924532421746983020638361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34465419791325288055035629 12924532421746983020638361)
          ·
            refine ⟨9693399316310237265478771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12924532421746983020638361 9693399316310237265478771)
            ·
              refine ⟨14540098974465355898218157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9693399316310237265478771 14540098974465355898218157)
              ·
                refine ⟨5452537115424508461831809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14540098974465355898218157 5452537115424508461831809)
                ·
                  refine ⟨4089402836568381346373857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5452537115424508461831809 4089402836568381346373857)
                  ·
                    refine ⟨3067052127426286009780393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089402836568381346373857 3067052127426286009780393)
                    ·
                      refine ⟨2300289095569714507335295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067052127426286009780393 2300289095569714507335295)
                      ·
                        rfl

theorem cell23_4479797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_4479797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479797 prefixEnd_4479797 := by exact prefixLift 4479797
  have htrace : WordTrace (prefixWord ++ tailWord_4479797) baseStart_4479797 baseEnd_4479797 := by
    simpa [prefixWord, tailWord_4479797, baseEnd_4479797] using wordTrace_append hprefix tailTrace_4479797
  have hstable : (prefixWord ++ tailWord_4479797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479797).length < 2 ^ (prefixWord ++ tailWord_4479797).sum := by decide
  have hdescent : baseEnd_4479797 < baseStart_4479797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479814 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4479814 : Nat := 118140960795 + 4479814 * 2 ^ 59
def prefixEnd_4479814 : Nat := 4983230072969 + 3 ^ 40 * 4479814 * 2
def baseEnd_4479814 : Nat := 2300297824740840940822717

theorem tailTrace_4479814 : CollatzResearch.WordTrace tailWord_4479814 prefixEnd_4479814 2300297824740840940822717 := by
  unfold tailWord_4479814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5106007493512701380133703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108928159861604296109518997 5106007493512701380133703)
  ·
    refine ⟨7659011240269052070200555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5106007493512701380133703 7659011240269052070200555)
    ·
      refine ⟨11488516860403578105300833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7659011240269052070200555 11488516860403578105300833)
      ·
        refine ⟨8616387645302683578975625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11488516860403578105300833 8616387645302683578975625)
        ·
          refine ⟨6462290733977012684231719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8616387645302683578975625 6462290733977012684231719)
          ·
            refine ⟨9693436100965519026347579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6462290733977012684231719 9693436100965519026347579)
            ·
              refine ⟨14540154151448278539521369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9693436100965519026347579 14540154151448278539521369)
              ·
                refine ⟨10905115613586208904641027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14540154151448278539521369 10905115613586208904641027)
                ·
                  refine ⟨16357673420379313356961541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10905115613586208904641027 16357673420379313356961541)
                  ·
                    refine ⟨3067063766321121254430289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16357673420379313356961541 3067063766321121254430289)
                    ·
                      refine ⟨2300297824740840940822717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067063766321121254430289 2300297824740840940822717)
                      ·
                        rfl

theorem cell23_4479814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4479814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479814 prefixEnd_4479814 := by exact prefixLift 4479814
  have htrace : WordTrace (prefixWord ++ tailWord_4479814) baseStart_4479814 baseEnd_4479814 := by
    simpa [prefixWord, tailWord_4479814, baseEnd_4479814] using wordTrace_append hprefix tailTrace_4479814
  have hstable : (prefixWord ++ tailWord_4479814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479814).length < 2 ^ (prefixWord ++ tailWord_4479814).sum := by decide
  have hdescent : baseEnd_4479814 < baseStart_4479814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479826 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_4479826 : Nat := 118140960795 + 4479826 * 2 ^ 59
def prefixEnd_4479826 : Nat := 4983230072969 + 3 ^ 40 * 4479826 * 2
def baseEnd_4479826 : Nat := 2300303986508694893872661

theorem tailTrace_4479826 : CollatzResearch.WordTrace tailWord_4479826 prefixEnd_4479826 2300303986508694893872661 := by
  unfold tailWord_4479826
  simp only [CollatzResearch.WordTrace]
  refine ⟨40848169367090742553428833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108928451645575313475810221 40848169367090742553428833)
  ·
    refine ⟨30636127025318056915071625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40848169367090742553428833 30636127025318056915071625)
    ·
      refine ⟨22977095268988542686303719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30636127025318056915071625 22977095268988542686303719)
      ·
        refine ⟨34465642903482814029455579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22977095268988542686303719 34465642903482814029455579)
        ·
          refine ⟨51698464355224221044183369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34465642903482814029455579 51698464355224221044183369)
          ·
            refine ⟨38773848266418165783137527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51698464355224221044183369 38773848266418165783137527)
            ·
              refine ⟨58160772399627248674706291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38773848266418165783137527 58160772399627248674706291)
              ·
                refine ⟨87241158599440873012059437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58160772399627248674706291 87241158599440873012059437)
                ·
                  refine ⟨32715434474790327379522289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87241158599440873012059437 32715434474790327379522289)
                  ·
                    refine ⟨24536575856092745534641717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32715434474790327379522289 24536575856092745534641717)
                    ·
                      refine ⟨2300303986508694893872661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24536575856092745534641717 2300303986508694893872661)
                      ·
                        rfl

theorem cell23_4479826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_4479826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479826 prefixEnd_4479826 := by exact prefixLift 4479826
  have htrace : WordTrace (prefixWord ++ tailWord_4479826) baseStart_4479826 baseEnd_4479826 := by
    simpa [prefixWord, tailWord_4479826, baseEnd_4479826] using wordTrace_append hprefix tailTrace_4479826
  have hstable : (prefixWord ++ tailWord_4479826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479826).length < 2 ^ (prefixWord ++ tailWord_4479826).sum := by decide
  have hdescent : baseEnd_4479826 < baseStart_4479826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479876 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 8]
def baseStart_4479876 : Nat := 118140960795 + 4479876 * 2 ^ 59
def prefixEnd_4479876 : Nat := 4983230072969 + 3 ^ 40 * 4479876 * 2
def baseEnd_4479876 : Nat := 255592184504602188694159

theorem tailTrace_4479876 : CollatzResearch.WordTrace tailWord_4479876 prefixEnd_4479876 255592184504602188694159 := by
  unfold tailWord_4479876
  simp only [CollatzResearch.WordTrace]
  refine ⟨81697250559090914376517741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108929667412121219168690321 81697250559090914376517741)
  ·
    refine ⟨30636468959659092891194153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81697250559090914376517741 30636468959659092891194153)
    ·
      refine ⟨22977351719744319668395615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30636468959659092891194153 22977351719744319668395615)
      ·
        refine ⟨34466027579616479502593423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22977351719744319668395615 34466027579616479502593423)
        ·
          refine ⟨51699041369424719253890135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34466027579616479502593423 51699041369424719253890135)
          ·
            refine ⟨77548562054137078880835203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51699041369424719253890135 77548562054137078880835203)
            ·
              refine ⟨116322843081205618321252805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77548562054137078880835203 116322843081205618321252805)
              ·
                refine ⟨21810533077726053435234901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116322843081205618321252805 21810533077726053435234901)
                ·
                  refine ⟨255592184504602188694159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21810533077726053435234901 255592184504602188694159)
                  ·
                    rfl

theorem cell23_4479876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_4479876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479876 prefixEnd_4479876 := by exact prefixLift 4479876
  have htrace : WordTrace (prefixWord ++ tailWord_4479876) baseStart_4479876 baseEnd_4479876 := by
    simpa [prefixWord, tailWord_4479876, baseEnd_4479876] using wordTrace_append hprefix tailTrace_4479876
  have hstable : (prefixWord ++ tailWord_4479876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479876).length < 2 ^ (prefixWord ++ tailWord_4479876).sum := by decide
  have hdescent : baseEnd_4479876 < baseStart_4479876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479893 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 6]
def baseStart_4479893 : Nat := 118140960795 + 4479893 * 2 ^ 59
def prefixEnd_4479893 : Nat := 4983230072969 + 3 ^ 40 * 4479893 * 2
def baseEnd_4479893 : Nat := 255593154412505125748317

theorem tailTrace_4479893 : CollatzResearch.WordTrace tailWord_4479893 prefixEnd_4479893 255593154412505125748317 := by
  unfold tailWord_4479893
  simp only [CollatzResearch.WordTrace]
  refine ⟨163395121159120240656404333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108930080772746827104269555 163395121159120240656404333)
  ·
    refine ⟨61273170434670090246151625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163395121159120240656404333 61273170434670090246151625)
    ·
      refine ⟨45954877826002567684613719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61273170434670090246151625 45954877826002567684613719)
      ·
        refine ⟨68932316739003851526920579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45954877826002567684613719 68932316739003851526920579)
        ·
          refine ⟨103398475108505777290380869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68932316739003851526920579 103398475108505777290380869)
          ·
            refine ⟨19387214082844833241946413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103398475108505777290380869 19387214082844833241946413)
            ·
              refine ⟨7270205281066812465729905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19387214082844833241946413 7270205281066812465729905)
              ·
                refine ⟨5452653960800109349297429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7270205281066812465729905 5452653960800109349297429)
                ·
                  refine ⟨255593154412505125748317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5452653960800109349297429 255593154412505125748317)
                  ·
                    rfl

theorem cell23_4479893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_4479893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479893 prefixEnd_4479893 := by exact prefixLift 4479893
  have htrace : WordTrace (prefixWord ++ tailWord_4479893) baseStart_4479893 baseEnd_4479893 := by
    simpa [prefixWord, tailWord_4479893, baseEnd_4479893] using wordTrace_append hprefix tailTrace_4479893
  have hstable : (prefixWord ++ tailWord_4479893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479893).length < 2 ^ (prefixWord ++ tailWord_4479893).sum := by decide
  have hdescent : baseEnd_4479893 < baseStart_4479893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479913 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 3, 5, 2]
def baseStart_4479913 : Nat := 118140960795 + 4479913 * 2 ^ 59
def prefixEnd_4479913 : Nat := 4983230072969 + 3 ^ 40 * 4479913 * 2
def baseEnd_4479913 : Nat := 2300348659325636053484761

theorem tailTrace_4479913 : CollatzResearch.WordTrace tailWord_4479913 prefixEnd_4479913 2300348659325636053484761 := by
  unfold tailWord_4479913
  simp only [CollatzResearch.WordTrace]
  refine ⟨163395850619047784072132393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108930567079365189381421595 163395850619047784072132393)
  ·
    refine ⟨122546887964285838054099295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163395850619047784072132393 122546887964285838054099295)
    ·
      refine ⟨183820331946428757081148943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122546887964285838054099295 183820331946428757081148943)
      ·
        refine ⟨275730497919643135621723415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183820331946428757081148943 275730497919643135621723415)
        ·
          refine ⟨413595746879464703432585123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275730497919643135621723415 413595746879464703432585123)
          ·
            refine ⟨620393620319197055148877685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413595746879464703432585123 620393620319197055148877685)
            ·
              refine ⟨58161901904924723920207283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 620393620319197055148877685 58161901904924723920207283)
              ·
                refine ⟨87242852857387085880310925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58161901904924723920207283 87242852857387085880310925)
                ·
                  refine ⟨32716069821520157205116597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87242852857387085880310925 32716069821520157205116597)
                  ·
                    refine ⟨3067131545767514737979681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32716069821520157205116597 3067131545767514737979681)
                    ·
                      refine ⟨2300348659325636053484761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067131545767514737979681 2300348659325636053484761)
                      ·
                        rfl

theorem cell23_4479913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 5, 2].length) (baseStart_4479913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479913 prefixEnd_4479913 := by exact prefixLift 4479913
  have htrace : WordTrace (prefixWord ++ tailWord_4479913) baseStart_4479913 baseEnd_4479913 := by
    simpa [prefixWord, tailWord_4479913, baseEnd_4479913] using wordTrace_append hprefix tailTrace_4479913
  have hstable : (prefixWord ++ tailWord_4479913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479913).length < 2 ^ (prefixWord ++ tailWord_4479913).sum := by decide
  have hdescent : baseEnd_4479913 < baseStart_4479913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479930 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2]
def baseStart_4479930 : Nat := 118140960795 + 4479930 * 2 ^ 59
def prefixEnd_4479930 : Nat := 4983230072969 + 3 ^ 40 * 4479930 * 2
def baseEnd_4479930 : Nat := 2300357388496762486972183

theorem tailTrace_4479930 : CollatzResearch.WordTrace tailWord_4479930 prefixEnd_4479930 2300357388496762486972183 := by
  unfold tailWord_4479930
  simp only [CollatzResearch.WordTrace]
  refine ⟨40849117664996548993875311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108930980439990797317000829 40849117664996548993875311)
  ·
    refine ⟨61273676497494823490812967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40849117664996548993875311 61273676497494823490812967)
    ·
      refine ⟨91910514746242235236219451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61273676497494823490812967 91910514746242235236219451)
      ·
        refine ⟨137865772119363352854329177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91910514746242235236219451 137865772119363352854329177)
        ·
          refine ⟨103399329089522514640746883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137865772119363352854329177 103399329089522514640746883)
          ·
            refine ⟨155098993634283771961120325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103399329089522514640746883 155098993634283771961120325)
            ·
              refine ⟨29081061306428207242710061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155098993634283771961120325 29081061306428207242710061)
              ·
                refine ⟨10905397989910577716016273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29081061306428207242710061 10905397989910577716016273)
                ·
                  refine ⟨8179048492432933287012205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10905397989910577716016273 8179048492432933287012205)
                  ·
                    refine ⟨3067143184662349982629577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8179048492432933287012205 3067143184662349982629577)
                    ·
                      refine ⟨2300357388496762486972183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067143184662349982629577 2300357388496762486972183)
                      ·
                        rfl

theorem cell23_4479930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_4479930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479930 prefixEnd_4479930 := by exact prefixLift 4479930
  have htrace : WordTrace (prefixWord ++ tailWord_4479930) baseStart_4479930 baseEnd_4479930 := by
    simpa [prefixWord, tailWord_4479930, baseEnd_4479930] using wordTrace_append hprefix tailTrace_4479930
  have hstable : (prefixWord ++ tailWord_4479930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479930).length < 2 ^ (prefixWord ++ tailWord_4479930).sum := by decide
  have hdescent : baseEnd_4479930 < baseStart_4479930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479953 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 4, 4]
def baseStart_4479953 : Nat := 118140960795 + 4479953 * 2 ^ 59
def prefixEnd_4479953 : Nat := 4983230072969 + 3 ^ 40 * 4479953 * 2
def baseEnd_4479953 : Nat := 766789732850605298994859

theorem tailTrace_4479953 : CollatzResearch.WordTrace tailWord_4479953 prefixEnd_4479953 766789732850605298994859 := by
  unfold tailWord_4479953
  simp only [CollatzResearch.WordTrace]
  refine ⟨163397309538902870903588513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108931539692601913935725675 163397309538902870903588513)
  ·
    refine ⟨122547982154177153177691385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163397309538902870903588513 122547982154177153177691385)
    ·
      refine ⟨91910986615632864883268539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122547982154177153177691385 91910986615632864883268539)
      ·
        refine ⟨137866479923449297324902809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91910986615632864883268539 137866479923449297324902809)
        ·
          refine ⟨103399859942586972993677107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137866479923449297324902809 103399859942586972993677107)
          ·
            refine ⟨155099789913880459490515661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103399859942586972993677107 155099789913880459490515661)
            ·
              refine ⟨58162421217705172308943373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155099789913880459490515661 58162421217705172308943373)
              ·
                refine ⟨21810907956639439615853765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58162421217705172308943373 21810907956639439615853765)
                ·
                  refine ⟨4089545241869894927972581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21810907956639439615853765 4089545241869894927972581)
                  ·
                    refine ⟨766789732850605298994859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4089545241869894927972581 766789732850605298994859)
                    ·
                      rfl

theorem cell23_4479953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_4479953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479953 prefixEnd_4479953 := by exact prefixLift 4479953
  have htrace : WordTrace (prefixWord ++ tailWord_4479953) baseStart_4479953 baseEnd_4479953 := by
    simpa [prefixWord, tailWord_4479953, baseEnd_4479953] using wordTrace_append hprefix tailTrace_4479953
  have hstable : (prefixWord ++ tailWord_4479953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479953).length < 2 ^ (prefixWord ++ tailWord_4479953).sum := by decide
  have hdescent : baseEnd_4479953 < baseStart_4479953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479954 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4479954 : Nat := 118140960795 + 4479954 * 2 ^ 59
def prefixEnd_4479954 : Nat := 4983230072969 + 3 ^ 40 * 4479954 * 2
def baseEnd_4479954 : Nat := 2300369712032470393072073

theorem tailTrace_4479954 : CollatzResearch.WordTrace tailWord_4479954 prefixEnd_4479954 2300369712032470393072073 := by
  unfold tailWord_4479954
  simp only [CollatzResearch.WordTrace]
  refine ⟨40849336502974812018593729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108931564007932832049583277 40849336502974812018593729)
  ·
    refine ⟨30637002377231109013945297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40849336502974812018593729 30637002377231109013945297)
    ·
      refine ⟨22977751782923331760458973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30637002377231109013945297 22977751782923331760458973)
      ·
        refine ⟨8616656918596249410172115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22977751782923331760458973 8616656918596249410172115)
        ·
          refine ⟨12924985377894374115258173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8616656918596249410172115 12924985377894374115258173)
          ·
            refine ⟨4846869516710390293221815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12924985377894374115258173 4846869516710390293221815)
            ·
              refine ⟨7270304275065585439832723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4846869516710390293221815 7270304275065585439832723)
              ·
                refine ⟨10905456412598378159749085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270304275065585439832723 10905456412598378159749085)
                ·
                  refine ⟨4089546154724391809905907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10905456412598378159749085 4089546154724391809905907)
                  ·
                    refine ⟨6134319232086587714858861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4089546154724391809905907 6134319232086587714858861)
                    ·
                      refine ⟨2300369712032470393072073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6134319232086587714858861 2300369712032470393072073)
                      ·
                        rfl

theorem cell23_4479954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4479954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479954 prefixEnd_4479954 := by exact prefixLift 4479954
  have htrace : WordTrace (prefixWord ++ tailWord_4479954) baseStart_4479954 baseEnd_4479954 := by
    simpa [prefixWord, tailWord_4479954, baseEnd_4479954] using wordTrace_append hprefix tailTrace_4479954
  have hstable : (prefixWord ++ tailWord_4479954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479954).length < 2 ^ (prefixWord ++ tailWord_4479954).sum := by decide
  have hdescent : baseEnd_4479954 < baseStart_4479954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4479990 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4479990 : Nat := 118140960795 + 4479990 * 2 ^ 59
def prefixEnd_4479990 : Nat := 4983230072969 + 3 ^ 40 * 4479990 * 2
def baseEnd_4479990 : Nat := 2300388197336032252221907

theorem tailTrace_4479990 : CollatzResearch.WordTrace tailWord_4479990 prefixEnd_4479990 2300388197336032252221907 := by
  unfold tailWord_4479990
  simp only [CollatzResearch.WordTrace]
  refine ⟨10212416189985551638917839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108932439359845884148456949 10212416189985551638917839)
  ·
    refine ⟨15318624284978327458376759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10212416189985551638917839 15318624284978327458376759)
    ·
      refine ⟨22977936427467491187565139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15318624284978327458376759 22977936427467491187565139)
      ·
        refine ⟨34466904641201236781347709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22977936427467491187565139 34466904641201236781347709)
        ·
          refine ⟨12925089240450463793005391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34466904641201236781347709 12925089240450463793005391)
          ·
            refine ⟨19387633860675695689508087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12925089240450463793005391 19387633860675695689508087)
            ·
              refine ⟨29081450791013543534262131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19387633860675695689508087 29081450791013543534262131)
              ·
                refine ⟨43622176186520315301393197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29081450791013543534262131 43622176186520315301393197)
                ·
                  refine ⟨16358316069945118238022449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43622176186520315301393197 16358316069945118238022449)
                  ·
                    refine ⟨12268737052458838678516837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16358316069945118238022449 12268737052458838678516837)
                    ·
                      refine ⟨2300388197336032252221907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12268737052458838678516837 2300388197336032252221907)
                      ·
                        rfl

theorem cell23_4479990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4479990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4479990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4479990 prefixEnd_4479990 := by exact prefixLift 4479990
  have htrace : WordTrace (prefixWord ++ tailWord_4479990) baseStart_4479990 baseEnd_4479990 := by
    simpa [prefixWord, tailWord_4479990, baseEnd_4479990] using wordTrace_append hprefix tailTrace_4479990
  have hstable : (prefixWord ++ tailWord_4479990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4479990).length < 2 ^ (prefixWord ++ tailWord_4479990).sum := by decide
  have hdescent : baseEnd_4479990 < baseStart_4479990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4479990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480011 : List Nat := [1, 1, 1, 1, 6, 2, 4, 2, 1, 2, 2]
def baseStart_4480011 : Nat := 118140960795 + 4480011 * 2 ^ 59
def prefixEnd_4480011 : Nat := 4983230072969 + 3 ^ 40 * 4480011 * 2
def baseEnd_4480011 : Nat := 2300398980429776670059311

theorem tailTrace_4480011 : CollatzResearch.WordTrace tailWord_4480011 prefixEnd_4480011 2300398980429776670059311 := by
  unfold tailWord_4480011
  simp only [CollatzResearch.WordTrace]
  refine ⟨163399424972692746809199887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108932949981795164539466591 163399424972692746809199887)
  ·
    refine ⟨245099137459039120213799831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163399424972692746809199887 245099137459039120213799831)
    ·
      refine ⟨367648706188558680320699747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245099137459039120213799831 367648706188558680320699747)
      ·
        refine ⟨551473059282838020481049621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367648706188558680320699747 551473059282838020481049621)
        ·
          refine ⟨25850299653883032210049201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 551473059282838020481049621 25850299653883032210049201)
          ·
            refine ⟨19387724740412274157536901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25850299653883032210049201 19387724740412274157536901)
            ·
              refine ⟨3635198388827301404538169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19387724740412274157536901 3635198388827301404538169)
              ·
                refine ⟨2726398791620476053403627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635198388827301404538169 2726398791620476053403627)
                ·
                  refine ⟨4089598187430714080105441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726398791620476053403627 4089598187430714080105441)
                  ·
                    refine ⟨3067198640573035560079081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089598187430714080105441 3067198640573035560079081)
                    ·
                      refine ⟨2300398980429776670059311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067198640573035560079081 2300398980429776670059311)
                      ·
                        rfl

theorem cell23_4480011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 2, 2].length) (baseStart_4480011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480011 prefixEnd_4480011 := by exact prefixLift 4480011
  have htrace : WordTrace (prefixWord ++ tailWord_4480011) baseStart_4480011 baseEnd_4480011 := by
    simpa [prefixWord, tailWord_4480011, baseEnd_4480011] using wordTrace_append hprefix tailTrace_4480011
  have hstable : (prefixWord ++ tailWord_4480011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480011).length < 2 ^ (prefixWord ++ tailWord_4480011).sum := by decide
  have hdescent : baseEnd_4480011 < baseStart_4480011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480037 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 1, 3, 2]
def baseStart_4480037 : Nat := 118140960795 + 4480037 * 2 ^ 59
def prefixEnd_4480037 : Nat := 4983230072969 + 3 ^ 40 * 4480037 * 2
def baseEnd_4480037 : Nat := 2300412330926793568334191

theorem tailTrace_4480037 : CollatzResearch.WordTrace tailWord_4480037 prefixEnd_4480037 2300412330926793568334191 := by
  unfold tailWord_4480037
  simp only [CollatzResearch.WordTrace]
  refine ⟨163400373270598553249646365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108933582180399035499764243 163400373270598553249646365)
  ·
    refine ⟨61275139976474457468617387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163400373270598553249646365 61275139976474457468617387)
    ·
      refine ⟨91912709964711686202926081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61275139976474457468617387 91912709964711686202926081)
      ·
        refine ⟨68934532473533764652194561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91912709964711686202926081 68934532473533764652194561)
        ·
          refine ⟨51700899355150323489145921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68934532473533764652194561 51700899355150323489145921)
          ·
            refine ⟨38775674516362742616859441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51700899355150323489145921 38775674516362742616859441)
            ·
              refine ⟨29081755887272056962644581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38775674516362742616859441 29081755887272056962644581)
              ·
                refine ⟨5452829228863510680495859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29081755887272056962644581 5452829228863510680495859)
                ·
                  refine ⟨8179243843295266020743789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5452829228863510680495859 8179243843295266020743789)
                  ·
                    refine ⟨3067216441235724757778921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8179243843295266020743789 3067216441235724757778921)
                    ·
                      refine ⟨2300412330926793568334191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067216441235724757778921 2300412330926793568334191)
                      ·
                        rfl

theorem cell23_4480037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_4480037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480037 prefixEnd_4480037 := by exact prefixLift 4480037
  have htrace : WordTrace (prefixWord ++ tailWord_4480037) baseStart_4480037 baseEnd_4480037 := by
    simpa [prefixWord, tailWord_4480037, baseEnd_4480037] using wordTrace_append hprefix tailTrace_4480037
  have hstable : (prefixWord ++ tailWord_4480037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480037).length < 2 ^ (prefixWord ++ tailWord_4480037).sum := by decide
  have hdescent : baseEnd_4480037 < baseStart_4480037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480053 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_4480053 : Nat := 118140960795 + 4480053 * 2 ^ 59
def prefixEnd_4480053 : Nat := 4983230072969 + 3 ^ 40 * 4480053 * 2
def baseEnd_4480053 : Nat := 2300420546617265505734117

theorem tailTrace_4480053 : CollatzResearch.WordTrace tailWord_4480053 prefixEnd_4480053 2300420546617265505734117 := by
  unfold tailWord_4480053
  simp only [CollatzResearch.WordTrace]
  refine ⟨163400956838540587982228813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108933971225693725321485875 163400956838540587982228813)
  ·
    refine ⟨61275358814452720493335805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163400956838540587982228813 61275358814452720493335805)
    ·
      refine ⟨22978259555419770185000927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61275358814452720493335805 22978259555419770185000927)
      ·
        refine ⟨34467389333129655277501391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22978259555419770185000927 34467389333129655277501391)
        ·
          refine ⟨51701083999694482916252087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34467389333129655277501391 51701083999694482916252087)
          ·
            refine ⟨77551625999541724374378131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51701083999694482916252087 77551625999541724374378131)
            ·
              refine ⟨116327438999312586561567197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77551625999541724374378131 116327438999312586561567197)
              ·
                refine ⟨43622789624742219960587699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116327438999312586561567197 43622789624742219960587699)
                ·
                  refine ⟨65434184437113329940881549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43622789624742219960587699 65434184437113329940881549)
                  ·
                    refine ⟨24537819163917498727830581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65434184437113329940881549 24537819163917498727830581)
                    ·
                      refine ⟨2300420546617265505734117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24537819163917498727830581 2300420546617265505734117)
                      ·
                        rfl

theorem cell23_4480053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_4480053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480053 prefixEnd_4480053 := by exact prefixLift 4480053
  have htrace : WordTrace (prefixWord ++ tailWord_4480053) baseStart_4480053 baseEnd_4480053 := by
    simpa [prefixWord, tailWord_4480053, baseEnd_4480053] using wordTrace_append hprefix tailTrace_4480053
  have hstable : (prefixWord ++ tailWord_4480053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480053).length < 2 ^ (prefixWord ++ tailWord_4480053).sum := by decide
  have hdescent : baseEnd_4480053 < baseStart_4480053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480067 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 4, 2, 2]
def baseStart_4480067 : Nat := 118140960795 + 4480067 * 2 ^ 59
def prefixEnd_4480067 : Nat := 4983230072969 + 3 ^ 40 * 4480067 * 2
def baseEnd_4480067 : Nat := 2300427735346428450959053

theorem tailTrace_4480067 : CollatzResearch.WordTrace tailWord_4480067 prefixEnd_4480067 2300427735346428450959053 := by
  unfold tailWord_4480067
  simp only [CollatzResearch.WordTrace]
  refine ⟨163401467460489868373238455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108934311640326578915492303 163401467460489868373238455)
  ·
    refine ⟨245102201190734802559857683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163401467460489868373238455 245102201190734802559857683)
    ·
      refine ⟨367653301786102203839786525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245102201190734802559857683 367653301786102203839786525)
      ·
        refine ⟨137869988169788326439919947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367653301786102203839786525 137869988169788326439919947)
        ·
          refine ⟨206804982254682489659879921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137869988169788326439919947 206804982254682489659879921)
          ·
            refine ⟨155103736691011867244909941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206804982254682489659879921 155103736691011867244909941)
            ·
              refine ⟨14540975314782362554210307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155103736691011867244909941 14540975314782362554210307)
              ·
                refine ⟨21811462972173543831315461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14540975314782362554210307 21811462972173543831315461)
                ·
                  refine ⟨4089649307282539468371649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21811462972173543831315461 4089649307282539468371649)
                  ·
                    refine ⟨3067236980461904601278737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089649307282539468371649 3067236980461904601278737)
                    ·
                      refine ⟨2300427735346428450959053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067236980461904601278737 2300427735346428450959053)
                      ·
                        rfl

theorem cell23_4480067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_4480067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480067 prefixEnd_4480067 := by exact prefixLift 4480067
  have htrace : WordTrace (prefixWord ++ tailWord_4480067) baseStart_4480067 baseEnd_4480067 := by
    simpa [prefixWord, tailWord_4480067, baseEnd_4480067] using wordTrace_append hprefix tailTrace_4480067
  have hstable : (prefixWord ++ tailWord_4480067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480067).length < 2 ^ (prefixWord ++ tailWord_4480067).sum := by decide
  have hdescent : baseEnd_4480067 < baseStart_4480067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480084 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_4480084 : Nat := 118140960795 + 4480084 * 2 ^ 59
def prefixEnd_4480084 : Nat := 4983230072969 + 3 ^ 40 * 4480084 * 2
def baseEnd_4480084 : Nat := 2300436464517554884446475

theorem tailTrace_4480084 : CollatzResearch.WordTrace tailWord_4480084 prefixEnd_4480084 2300436464517554884446475 := by
  unfold tailWord_4480084
  simp only [CollatzResearch.WordTrace]
  refine ⟨81701043750714140138303653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108934725000952186851071537 81701043750714140138303653)
  ·
    refine ⟨15318945703258901275931935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81701043750714140138303653 15318945703258901275931935)
    ·
      refine ⟨22978418554888351913897903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15318945703258901275931935 22978418554888351913897903)
      ·
        refine ⟨34467627832332527870846855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22978418554888351913897903 34467627832332527870846855)
        ·
          refine ⟨51701441748498791806270283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34467627832332527870846855 51701441748498791806270283)
          ·
            refine ⟨77552162622748187709405425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51701441748498791806270283 77552162622748187709405425)
            ·
              refine ⟨58164121967061140782054069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77552162622748187709405425 58164121967061140782054069)
              ·
                refine ⟨5452886434411981948317569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58164121967061140782054069 5452886434411981948317569)
                ·
                  refine ⟨4089664825808986461238177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5452886434411981948317569 4089664825808986461238177)
                  ·
                    refine ⟨3067248619356739845928633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089664825808986461238177 3067248619356739845928633)
                    ·
                      refine ⟨2300436464517554884446475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067248619356739845928633 2300436464517554884446475)
                      ·
                        rfl

theorem cell23_4480084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_4480084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480084 prefixEnd_4480084 := by exact prefixLift 4480084
  have htrace : WordTrace (prefixWord ++ tailWord_4480084) baseStart_4480084 baseEnd_4480084 := by
    simpa [prefixWord, tailWord_4480084, baseEnd_4480084] using wordTrace_append hprefix tailTrace_4480084
  have hstable : (prefixWord ++ tailWord_4480084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480084).length < 2 ^ (prefixWord ++ tailWord_4480084).sum := by decide
  have hdescent : baseEnd_4480084 < baseStart_4480084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480153 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_4480153 : Nat := 118140960795 + 4480153 * 2 ^ 59
def prefixEnd_4480153 : Nat := 4983230072969 + 3 ^ 40 * 4480153 * 2
def baseEnd_4480153 : Nat := 2300471894682715114483657

theorem tailTrace_4480153 : CollatzResearch.WordTrace tailWord_4480153 prefixEnd_4480153 2300471894682715114483657 := by
  unfold tailWord_4480153
  simp only [CollatzResearch.WordTrace]
  refine ⟨163404604138178305060869113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108936402758785536707246075 163404604138178305060869113)
  ·
    refine ⟨122553453103633728795651835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163404604138178305060869113 122553453103633728795651835)
    ·
      refine ⟨183830179655450593193477753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122553453103633728795651835 183830179655450593193477753)
      ·
        refine ⟨137872634741587944895108315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183830179655450593193477753 137872634741587944895108315)
        ·
          refine ⟨206808952112381917342662473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137872634741587944895108315 206808952112381917342662473)
          ·
            refine ⟨155106714084286438006996855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206808952112381917342662473 155106714084286438006996855)
            ·
              refine ⟨232660071126429657010495283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155106714084286438006996855 232660071126429657010495283)
              ·
                refine ⟨348990106689644485515742925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232660071126429657010495283 348990106689644485515742925)
                ·
                  refine ⟨130871290008616682068403597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348990106689644485515742925 130871290008616682068403597)
                  ·
                    refine ⟨49076733753231255775651349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130871290008616682068403597 49076733753231255775651349)
                    ·
                      refine ⟨2300471894682715114483657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49076733753231255775651349 2300471894682715114483657)
                      ·
                        rfl

theorem cell23_4480153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_4480153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480153 prefixEnd_4480153 := by exact prefixLift 4480153
  have htrace : WordTrace (prefixWord ++ tailWord_4480153) baseStart_4480153 baseEnd_4480153 := by
    simpa [prefixWord, tailWord_4480153, baseEnd_4480153] using wordTrace_append hprefix tailTrace_4480153
  have hstable : (prefixWord ++ tailWord_4480153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480153).length < 2 ^ (prefixWord ++ tailWord_4480153).sum := by decide
  have hdescent : baseEnd_4480153 < baseStart_4480153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480157 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_4480157 : Nat := 118140960795 + 4480157 * 2 ^ 59
def prefixEnd_4480157 : Nat := 4983230072969 + 3 ^ 40 * 4480157 * 2
def baseEnd_4480157 : Nat := 2300473948605333098833639

theorem tailTrace_4480157 : CollatzResearch.WordTrace tailWord_4480157 prefixEnd_4480157 2300473948605333098833639 := by
  unfold tailWord_4480157
  simp only [CollatzResearch.WordTrace]
  refine ⟨163404750030163813744014725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108936500020109209162676483 163404750030163813744014725)
  ·
    refine ⟨30638390630655715077002761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163404750030163813744014725 30638390630655715077002761)
    ·
      refine ⟨22978792972991786307752071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30638390630655715077002761 22978792972991786307752071)
      ·
        refine ⟨34468189459487679461628107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22978792972991786307752071 34468189459487679461628107)
        ·
          refine ⟨51702284189231519192442161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34468189459487679461628107 51702284189231519192442161)
          ·
            refine ⟨38776713141923639394331621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51702284189231519192442161 38776713141923639394331621)
            ·
              refine ⟨7270633714110682386437179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38776713141923639394331621 7270633714110682386437179)
              ·
                refine ⟨10905950571166023579655769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270633714110682386437179 10905950571166023579655769)
                ·
                  refine ⟨8179462928374517684741827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10905950571166023579655769 8179462928374517684741827)
                  ·
                    refine ⟨12269194392561776527112741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8179462928374517684741827 12269194392561776527112741)
                    ·
                      refine ⟨2300473948605333098833639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12269194392561776527112741 2300473948605333098833639)
                      ·
                        rfl

theorem cell23_4480157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_4480157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480157 prefixEnd_4480157 := by exact prefixLift 4480157
  have htrace : WordTrace (prefixWord ++ tailWord_4480157) baseStart_4480157 baseEnd_4480157 := by
    simpa [prefixWord, tailWord_4480157, baseEnd_4480157] using wordTrace_append hprefix tailTrace_4480157
  have hstable : (prefixWord ++ tailWord_4480157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480157).length < 2 ^ (prefixWord ++ tailWord_4480157).sum := by decide
  have hdescent : baseEnd_4480157 < baseStart_4480157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480163 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 10]
def baseStart_4480163 : Nat := 118140960795 + 4480163 * 2 ^ 59
def prefixEnd_4480163 : Nat := 4983230072969 + 3 ^ 40 * 4480163 * 2
def baseEnd_4480163 : Nat := 255608558832140008373179

theorem tailTrace_4480163 : CollatzResearch.WordTrace tailWord_4480163 prefixEnd_4480163 255608558832140008373179 := by
  unfold tailWord_4480163
  simp only [CollatzResearch.WordTrace]
  refine ⟨163404968868142076768733143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108936645912094717845822095 163404968868142076768733143)
  ·
    refine ⟨245107453302213115153099715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163404968868142076768733143 245107453302213115153099715)
    ·
      refine ⟨367661179953319672729649573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245107453302213115153099715 367661179953319672729649573)
      ·
        refine ⟨68936471241247438636809295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 367661179953319672729649573 68936471241247438636809295)
        ·
          refine ⟨103404706861871157955213943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68936471241247438636809295 103404706861871157955213943)
          ·
            refine ⟨155107060292806736932820915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103404706861871157955213943 155107060292806736932820915)
            ·
              refine ⟨232660590439210105399231373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155107060292806736932820915 232660590439210105399231373)
              ·
                refine ⟨87247721414703789524711765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232660590439210105399231373 87247721414703789524711765)
                ·
                  refine ⟨255608558832140008373179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 87247721414703789524711765 255608558832140008373179)
                  ·
                    rfl

theorem cell23_4480163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 10].length) (baseStart_4480163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480163 prefixEnd_4480163 := by exact prefixLift 4480163
  have htrace : WordTrace (prefixWord ++ tailWord_4480163) baseStart_4480163 baseEnd_4480163 := by
    simpa [prefixWord, tailWord_4480163, baseEnd_4480163] using wordTrace_append hprefix tailTrace_4480163
  have hstable : (prefixWord ++ tailWord_4480163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480163).length < 2 ^ (prefixWord ++ tailWord_4480163).sum := by decide
  have hdescent : baseEnd_4480163 < baseStart_4480163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480231 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 6]
def baseStart_4480231 : Nat := 118140960795 + 4480231 * 2 ^ 59
def prefixEnd_4480231 : Nat := 4983230072969 + 3 ^ 40 * 4480231 * 2
def baseEnd_4480231 : Nat := 255612438463751756589811

theorem tailTrace_4480231 : CollatzResearch.WordTrace tailWord_4480231 prefixEnd_4480231 255612438463751756589811 := by
  unfold tailWord_4480231
  simp only [CollatzResearch.WordTrace]
  refine ⟨163407449031895724382208547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108938299354597149588139031 163407449031895724382208547)
  ·
    refine ⟨245111173547843586573312821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163407449031895724382208547 245111173547843586573312821)
    ·
      refine ⟨22979172520110336241248077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245111173547843586573312821 22979172520110336241248077)
      ·
        refine ⟨8617189695041376090468029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22979172520110336241248077 8617189695041376090468029)
        ·
          refine ⟨3231446135640516033925511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8617189695041376090468029 3231446135640516033925511)
          ·
            refine ⟨4847169203460774050888267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231446135640516033925511 4847169203460774050888267)
            ·
              refine ⟨7270753805191161076332401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847169203460774050888267 7270753805191161076332401)
              ·
                refine ⟨5453065353893370807249301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7270753805191161076332401 5453065353893370807249301)
                ·
                  refine ⟨255612438463751756589811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5453065353893370807249301 255612438463751756589811)
                  ·
                    rfl

theorem cell23_4480231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 6].length) (baseStart_4480231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480231 prefixEnd_4480231 := by exact prefixLift 4480231
  have htrace : WordTrace (prefixWord ++ tailWord_4480231) baseStart_4480231 baseEnd_4480231 := by
    simpa [prefixWord, tailWord_4480231, baseEnd_4480231] using wordTrace_append hprefix tailTrace_4480231
  have hstable : (prefixWord ++ tailWord_4480231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480231).length < 2 ^ (prefixWord ++ tailWord_4480231).sum := by decide
  have hdescent : baseEnd_4480231 < baseStart_4480231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480257 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 1, 6]
def baseStart_4480257 : Nat := 118140960795 + 4480257 * 2 ^ 59
def prefixEnd_4480257 : Nat := 4983230072969 + 3 ^ 40 * 4480257 * 2
def baseEnd_4480257 : Nat := 766841765556927569194393

theorem tailTrace_4480257 : CollatzResearch.WordTrace tailWord_4480257 prefixEnd_4480257 766841765556927569194393 := by
  unfold tailWord_4480257
  simp only [CollatzResearch.WordTrace]
  refine ⟨163408397329801530822655025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108938931553201020548436683 163408397329801530822655025)
  ·
    refine ⟨122556297997351148116991269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163408397329801530822655025 122556297997351148116991269)
    ·
      refine ⟨22979305874503340271935863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122556297997351148116991269 22979305874503340271935863)
      ·
        refine ⟨34468958811755010407903795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22979305874503340271935863 34468958811755010407903795)
        ·
          refine ⟨51703438217632515611855693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34468958811755010407903795 51703438217632515611855693)
          ·
            refine ⟨19388789331612193354445885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51703438217632515611855693 19388789331612193354445885)
            ·
              refine ⟨7270795999354572507917207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19388789331612193354445885 7270795999354572507917207)
              ·
                refine ⟨10906193999031858761875811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270795999354572507917207 10906193999031858761875811)
                ·
                  refine ⟨16359290998547788142813717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10906193999031858761875811 16359290998547788142813717)
                  ·
                    refine ⟨766841765556927569194393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16359290998547788142813717 766841765556927569194393)
                    ·
                      rfl

theorem cell23_4480257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_4480257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480257 prefixEnd_4480257 := by exact prefixLift 4480257
  have htrace : WordTrace (prefixWord ++ tailWord_4480257) baseStart_4480257 baseEnd_4480257 := by
    simpa [prefixWord, tailWord_4480257, baseEnd_4480257] using wordTrace_append hprefix tailTrace_4480257
  have hstable : (prefixWord ++ tailWord_4480257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480257).length < 2 ^ (prefixWord ++ tailWord_4480257).sum := by decide
  have hdescent : baseEnd_4480257 < baseStart_4480257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480284 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_4480284 : Nat := 118140960795 + 4480284 * 2 ^ 59
def prefixEnd_4480284 : Nat := 4983230072969 + 3 ^ 40 * 4480284 * 2
def baseEnd_4480284 : Nat := 2300539160648454101945555

theorem tailTrace_4480284 : CollatzResearch.WordTrace tailWord_4480284 prefixEnd_4480284 2300539160648454101945555 := by
  unfold tailWord_4480284
  simp only [CollatzResearch.WordTrace]
  refine ⟨81704691050351857216943953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108939588067135809622591937 81704691050351857216943953)
  ·
    refine ⟨61278518287763892912707965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81704691050351857216943953 61278518287763892912707965)
    ·
      refine ⟨22979444357911459842265487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61278518287763892912707965 22979444357911459842265487)
      ·
        refine ⟨34469166536867189763398231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22979444357911459842265487 34469166536867189763398231)
        ·
          refine ⟨51703749805300784645097347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34469166536867189763398231 51703749805300784645097347)
          ·
            refine ⟨77555624707951176967646021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51703749805300784645097347 77555624707951176967646021)
            ·
              refine ⟨14541679632740845681433629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77555624707951176967646021 14541679632740845681433629)
              ·
                refine ⟨5453129862277817130537611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14541679632740845681433629 5453129862277817130537611)
                ·
                  refine ⟨8179694793416725695806417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5453129862277817130537611 8179694793416725695806417)
                  ·
                    refine ⟨6134771095062544271854813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8179694793416725695806417 6134771095062544271854813)
                    ·
                      refine ⟨2300539160648454101945555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6134771095062544271854813 2300539160648454101945555)
                      ·
                        rfl

theorem cell23_4480284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_4480284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480284 prefixEnd_4480284 := by exact prefixLift 4480284
  have htrace : WordTrace (prefixWord ++ tailWord_4480284) baseStart_4480284 baseEnd_4480284 := by
    simpa [prefixWord, tailWord_4480284, baseEnd_4480284] using wordTrace_append hprefix tailTrace_4480284
  have hstable : (prefixWord ++ tailWord_4480284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480284).length < 2 ^ (prefixWord ++ tailWord_4480284).sum := by decide
  have hdescent : baseEnd_4480284 < baseStart_4480284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480287 : List Nat := [1, 1, 2, 4, 4, 2, 9]
def baseStart_4480287 : Nat := 118140960795 + 4480287 * 2 ^ 59
def prefixEnd_4480287 : Nat := 4983230072969 + 3 ^ 40 * 4480287 * 2
def baseEnd_4480287 : Nat := 28401737050498982595161

theorem tailTrace_4480287 : CollatzResearch.WordTrace tailWord_4480287 prefixEnd_4480287 28401737050498982595161 := by
  unfold tailWord_4480287
  simp only [CollatzResearch.WordTrace]
  refine ⟨163409491519692845946247115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108939661013128563964164743 163409491519692845946247115)
  ·
    refine ⟨245114237279539268919370673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163409491519692845946247115 245114237279539268919370673)
    ·
      refine ⟨183835677959654451689528005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245114237279539268919370673 183835677959654451689528005)
      ·
        refine ⟨34469189617435209691786501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183835677959654451689528005 34469189617435209691786501)
        ·
          refine ⟨6462973053269101817209969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34469189617435209691786501 6462973053269101817209969)
          ·
            refine ⟨4847229789951826362907477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6462973053269101817209969 4847229789951826362907477)
            ·
              refine ⟨28401737050498982595161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4847229789951826362907477 28401737050498982595161)
              ·
                rfl

theorem cell23_4480287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 9].length) (baseStart_4480287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480287 prefixEnd_4480287 := by exact prefixLift 4480287
  have htrace : WordTrace (prefixWord ++ tailWord_4480287) baseStart_4480287 baseEnd_4480287 := by
    simpa [prefixWord, tailWord_4480287, baseEnd_4480287] using wordTrace_append hprefix tailTrace_4480287
  have hstable : (prefixWord ++ tailWord_4480287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480287).length < 2 ^ (prefixWord ++ tailWord_4480287).sum := by decide
  have hdescent : baseEnd_4480287 < baseStart_4480287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480298 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4480298 : Nat := 118140960795 + 4480298 * 2 ^ 59
def prefixEnd_4480298 : Nat := 4983230072969 + 3 ^ 40 * 4480298 * 2
def baseEnd_4480298 : Nat := 2300546349377617047170491

theorem tailTrace_4480298 : CollatzResearch.WordTrace tailWord_4480298 prefixEnd_4480298 2300546349377617047170491 := by
  unfold tailWord_4480298
  simp only [CollatzResearch.WordTrace]
  refine ⟨40852473180663248706224387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108939928481768663216598365 40852473180663248706224387)
  ·
    refine ⟨61278709770994873059336581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40852473180663248706224387 61278709770994873059336581)
    ·
      refine ⟨11489758082061538698625609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61278709770994873059336581 11489758082061538698625609)
      ·
        refine ⟨8617318561546154023969207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11489758082061538698625609 8617318561546154023969207)
        ·
          refine ⟨12925977842319231035953811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8617318561546154023969207 12925977842319231035953811)
          ·
            refine ⟨19388966763478846553930717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12925977842319231035953811 19388966763478846553930717)
            ·
              refine ⟨7270862536304567457724019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19388966763478846553930717 7270862536304567457724019)
              ·
                refine ⟨10906293804456851186586029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270862536304567457724019 10906293804456851186586029)
                ·
                  refine ⟨4089860176671319194969761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10906293804456851186586029 4089860176671319194969761)
                  ·
                    refine ⟨3067395132503489396227321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089860176671319194969761 3067395132503489396227321)
                    ·
                      refine ⟨2300546349377617047170491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067395132503489396227321 2300546349377617047170491)
                      ·
                        rfl

theorem cell23_4480298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4480298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480298 prefixEnd_4480298 := by exact prefixLift 4480298
  have htrace : WordTrace (prefixWord ++ tailWord_4480298) baseStart_4480298 baseEnd_4480298 := by
    simpa [prefixWord, tailWord_4480298, baseEnd_4480298] using wordTrace_append hprefix tailTrace_4480298
  have hstable : (prefixWord ++ tailWord_4480298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480298).length < 2 ^ (prefixWord ++ tailWord_4480298).sum := by decide
  have hdescent : baseEnd_4480298 < baseStart_4480298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480300 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_4480300 : Nat := 118140960795 + 4480300 * 2 ^ 59
def prefixEnd_4480300 : Nat := 4983230072969 + 3 ^ 40 * 4480300 * 2
def baseEnd_4480300 : Nat := 766849125446308679781827

theorem tailTrace_4480300 : CollatzResearch.WordTrace tailWord_4480300 prefixEnd_4480300 766849125446308679781827 := by
  unfold tailWord_4480300
  simp only [CollatzResearch.WordTrace]
  refine ⟨81704982834322874583235177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108939977112430499444313569 81704982834322874583235177)
  ·
    refine ⟨61278737125742155937426383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81704982834322874583235177 61278737125742155937426383)
    ·
      refine ⟨91918105688613233906139575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61278737125742155937426383 91918105688613233906139575)
      ·
        refine ⟨137877158532919850859209363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91918105688613233906139575 137877158532919850859209363)
        ·
          refine ⟨206815737799379776288814045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137877158532919850859209363 206815737799379776288814045)
          ·
            refine ⟨77555901674767416108305267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206815737799379776288814045 77555901674767416108305267)
            ·
              refine ⟨116333852512151124162457901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77555901674767416108305267 116333852512151124162457901)
              ·
                refine ⟨43625194692056671560921713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116333852512151124162457901 43625194692056671560921713)
                ·
                  refine ⟨32718896019042503670691285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43625194692056671560921713 32718896019042503670691285)
                  ·
                    refine ⟨766849125446308679781827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32718896019042503670691285 766849125446308679781827)
                    ·
                      rfl

theorem cell23_4480300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_4480300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480300 prefixEnd_4480300 := by exact prefixLift 4480300
  have htrace : WordTrace (prefixWord ++ tailWord_4480300) baseStart_4480300 baseEnd_4480300 := by
    simpa [prefixWord, tailWord_4480300, baseEnd_4480300] using wordTrace_append hprefix tailTrace_4480300
  have hstable : (prefixWord ++ tailWord_4480300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480300).length < 2 ^ (prefixWord ++ tailWord_4480300).sum := by decide
  have hdescent : baseEnd_4480300 < baseStart_4480300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480342 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4480342 : Nat := 118140960795 + 4480342 * 2 ^ 59
def prefixEnd_4480342 : Nat := 4983230072969 + 3 ^ 40 * 4480342 * 2
def baseEnd_4480342 : Nat := 766856314175471625006763

theorem tailTrace_4480342 : CollatzResearch.WordTrace tailWord_4480342 prefixEnd_4480342 766856314175471625006763 := by
  unfold tailWord_4480342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10213218595905849396218705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108940998356329060226332853 10213218595905849396218705)
  ·
    refine ⟨7659913946929387047164029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10213218595905849396218705 7659913946929387047164029)
    ·
      refine ⟨2872467730098520142686511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7659913946929387047164029 2872467730098520142686511)
      ·
        refine ⟨4308701595147780214029767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872467730098520142686511 4308701595147780214029767)
        ·
          refine ⟨6463052392721670321044651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4308701595147780214029767 6463052392721670321044651)
          ·
            refine ⟨9694578589082505481566977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6463052392721670321044651 9694578589082505481566977)
            ·
              refine ⟨7270933941811879111175233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9694578589082505481566977 7270933941811879111175233)
              ·
                refine ⟨5453200456358909333381425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7270933941811879111175233 5453200456358909333381425)
                ·
                  refine ⟨4089900342269182000036069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5453200456358909333381425 4089900342269182000036069)
                  ·
                    refine ⟨766856314175471625006763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4089900342269182000036069 766856314175471625006763)
                    ·
                      rfl

theorem cell23_4480342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4480342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480342 prefixEnd_4480342 := by exact prefixLift 4480342
  have htrace : WordTrace (prefixWord ++ tailWord_4480342) baseStart_4480342 baseEnd_4480342 := by
    simpa [prefixWord, tailWord_4480342, baseEnd_4480342] using wordTrace_append hprefix tailTrace_4480342
  have hstable : (prefixWord ++ tailWord_4480342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480342).length < 2 ^ (prefixWord ++ tailWord_4480342).sum := by decide
  have hdescent : baseEnd_4480342 < baseStart_4480342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480349 : List Nat := [1, 4, 5, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4480349 : Nat := 118140960795 + 4480349 * 2 ^ 59
def prefixEnd_4480349 : Nat := 4983230072969 + 3 ^ 40 * 4480349 * 2
def baseEnd_4480349 : Nat := 2300572536890996347632757

theorem tailTrace_4480349 : CollatzResearch.WordTrace tailWord_4480349 prefixEnd_4480349 2300572536890996347632757 := by
  unfold tailWord_4480349
  simp only [CollatzResearch.WordTrace]
  refine ⟨163411752845468230535004101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108941168563645487023336067 163411752845468230535004101)
  ·
    refine ⟨30639703658525293225313269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163411752845468230535004101 30639703658525293225313269)
    ·
      refine ⟨2872472217986746239873119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30639703658525293225313269 2872472217986746239873119)
      ·
        refine ⟨4308708326980119359809679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2872472217986746239873119 4308708326980119359809679)
        ·
          refine ⟨6463062490470179039714519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4308708326980119359809679 6463062490470179039714519)
          ·
            refine ⟨9694593735705268559571779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6463062490470179039714519 9694593735705268559571779)
            ·
              refine ⟨14541890603557902839357669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9694593735705268559571779 14541890603557902839357669)
              ·
                refine ⟨2726604488167106782379563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14541890603557902839357669 2726604488167106782379563)
                ·
                  refine ⟨4089906732250660173569345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726604488167106782379563 4089906732250660173569345)
                  ·
                    refine ⟨3067430049187995130177009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4089906732250660173569345 3067430049187995130177009)
                    ·
                      refine ⟨2300572536890996347632757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067430049187995130177009 2300572536890996347632757)
                      ·
                        rfl

theorem cell23_4480349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4480349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480349 prefixEnd_4480349 := by exact prefixLift 4480349
  have htrace : WordTrace (prefixWord ++ tailWord_4480349) baseStart_4480349 baseEnd_4480349 := by
    simpa [prefixWord, tailWord_4480349, baseEnd_4480349] using wordTrace_append hprefix tailTrace_4480349
  have hstable : (prefixWord ++ tailWord_4480349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480349).length < 2 ^ (prefixWord ++ tailWord_4480349).sum := by decide
  have hdescent : baseEnd_4480349 < baseStart_4480349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480357 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_4480357 : Nat := 118140960795 + 4480357 * 2 ^ 59
def prefixEnd_4480357 : Nat := 4983230072969 + 3 ^ 40 * 4480357 * 2
def baseEnd_4480357 : Nat := 2300576644736232316332719

theorem tailTrace_4480357 : CollatzResearch.WordTrace tailWord_4480357 prefixEnd_4480357 2300576644736232316332719 := by
  unfold tailWord_4480357
  simp only [CollatzResearch.WordTrace]
  refine ⟨163412044629439247901295325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108941363086292831934196883 163412044629439247901295325)
  ·
    refine ⟨61279516736039717962985747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163412044629439247901295325 61279516736039717962985747)
    ·
      refine ⟨91919275104059576944478621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61279516736039717962985747 91919275104059576944478621)
      ·
        refine ⟨34469728164022341354179483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91919275104059576944478621 34469728164022341354179483)
        ·
          refine ⟨51704592246033512031269225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34469728164022341354179483 51704592246033512031269225)
          ·
            refine ⟨38778444184525134023451919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51704592246033512031269225 38778444184525134023451919)
            ·
              refine ⟨58167666276787701035177879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38778444184525134023451919 58167666276787701035177879)
              ·
                refine ⟨87251499415181551552766819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58167666276787701035177879 87251499415181551552766819)
                ·
                  refine ⟨130877249122772327329150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87251499415181551552766819 130877249122772327329150229)
                  ·
                    refine ⟨6134871052629952843553917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 130877249122772327329150229 6134871052629952843553917)
                    ·
                      refine ⟨2300576644736232316332719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6134871052629952843553917 2300576644736232316332719)
                      ·
                        rfl

theorem cell23_4480357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_4480357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480357 prefixEnd_4480357 := by exact prefixLift 4480357
  have htrace : WordTrace (prefixWord ++ tailWord_4480357) baseStart_4480357 baseEnd_4480357 := by
    simpa [prefixWord, tailWord_4480357, baseEnd_4480357] using wordTrace_append hprefix tailTrace_4480357
  have hstable : (prefixWord ++ tailWord_4480357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480357).length < 2 ^ (prefixWord ++ tailWord_4480357).sum := by decide
  have hdescent : baseEnd_4480357 < baseStart_4480357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480367 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_4480367 : Nat := 118140960795 + 4480367 * 2 ^ 59
def prefixEnd_4480367 : Nat := 4983230072969 + 3 ^ 40 * 4480367 * 2
def baseEnd_4480367 : Nat := 2300581779542777277207673

theorem tailTrace_4480367 : CollatzResearch.WordTrace tailWord_4480367 prefixEnd_4480367 2300581779542777277207673 := by
  unfold tailWord_4480367
  simp only [CollatzResearch.WordTrace]
  refine ⟨163412409359403019609159355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108941606239602013072772903 163412409359403019609159355)
  ·
    refine ⟨245118614039104529413739033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163412409359403019609159355 245118614039104529413739033)
    ·
      refine ⟨183838960529328397060304275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245118614039104529413739033 183838960529328397060304275)
      ·
        refine ⟨275758440793992595590456413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183838960529328397060304275 275758440793992595590456413)
        ·
          refine ⟨103409415297747223346421155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275758440793992595590456413 103409415297747223346421155)
          ·
            refine ⟨155114122946620835019631733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103409415297747223346421155 155114122946620835019631733)
            ·
              refine ⟨14541949026245703283090475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155114122946620835019631733 14541949026245703283090475)
              ·
                refine ⟨21812923539368554924635713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14541949026245703283090475 21812923539368554924635713)
                ·
                  refine ⟨16359692654526416193476785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21812923539368554924635713 16359692654526416193476785)
                  ·
                    refine ⟨12269769490894812145107589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16359692654526416193476785 12269769490894812145107589)
                    ·
                      refine ⟨2300581779542777277207673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12269769490894812145107589 2300581779542777277207673)
                      ·
                        rfl

theorem cell23_4480367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_4480367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480367 prefixEnd_4480367 := by exact prefixLift 4480367
  have htrace : WordTrace (prefixWord ++ tailWord_4480367) baseStart_4480367 baseEnd_4480367 := by
    simpa [prefixWord, tailWord_4480367, baseEnd_4480367] using wordTrace_append hprefix tailTrace_4480367
  have hstable : (prefixWord ++ tailWord_4480367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480367).length < 2 ^ (prefixWord ++ tailWord_4480367).sum := by decide
  have hdescent : baseEnd_4480367 < baseStart_4480367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480407 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 4, 5]
def baseStart_4480407 : Nat := 118140960795 + 4480407 * 2 ^ 59
def prefixEnd_4480407 : Nat := 4983230072969 + 3 ^ 40 * 4480407 * 2
def baseEnd_4480407 : Nat := 766867439589652373569163

theorem tailTrace_4480407 : CollatzResearch.WordTrace tailWord_4480407 prefixEnd_4480407 766867439589652373569163 := by
  unfold tailWord_4480407
  simp only [CollatzResearch.WordTrace]
  refine ⟨163413868279258106440615475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108942578852838737627076983 163413868279258106440615475)
  ·
    refine ⟨245120802418887159660923213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163413868279258106440615475 245120802418887159660923213)
    ·
      refine ⟨91920300907082684872846205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245120802418887159660923213 91920300907082684872846205)
      ·
        refine ⟨34470112840156006827317327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91920300907082684872846205 34470112840156006827317327)
        ·
          refine ⟨51705169260234010240975991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34470112840156006827317327 51705169260234010240975991)
          ·
            refine ⟨77557753890351015361463987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51705169260234010240975991 77557753890351015361463987)
            ·
              refine ⟨116336630835526523042195981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77557753890351015361463987 116336630835526523042195981)
              ·
                refine ⟨43626236563322446140823493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116336630835526523042195981 43626236563322446140823493)
                ·
                  refine ⟨8179919355622958651404405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43626236563322446140823493 8179919355622958651404405)
                  ·
                    refine ⟨766867439589652373569163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8179919355622958651404405 766867439589652373569163)
                    ·
                      rfl

theorem cell23_4480407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_4480407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480407 prefixEnd_4480407 := by exact prefixLift 4480407
  have htrace : WordTrace (prefixWord ++ tailWord_4480407) baseStart_4480407 baseEnd_4480407 := by
    simpa [prefixWord, tailWord_4480407, baseEnd_4480407] using wordTrace_append hprefix tailTrace_4480407
  have hstable : (prefixWord ++ tailWord_4480407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480407).length < 2 ^ (prefixWord ++ tailWord_4480407).sum := by decide
  have hdescent : baseEnd_4480407 < baseStart_4480407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480464 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 3]
def baseStart_4480464 : Nat := 118140960795 + 4480464 * 2 ^ 59
def prefixEnd_4480464 : Nat := 4983230072969 + 3 ^ 40 * 4480464 * 2
def baseEnd_4480464 : Nat := 2300631587166263397694727

theorem tailTrace_4480464 : CollatzResearch.WordTrace tailWord_4480464 prefixEnd_4480464 2300631587166263397694727 := by
  unfold tailWord_4480464
  simp only [CollatzResearch.WordTrace]
  refine ⟨81707973620025802587720223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108943964826701070116960297 81707973620025802587720223)
  ·
    refine ⟨122561960430038703881580335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81707973620025802587720223 122561960430038703881580335)
    ·
      refine ⟨183842940645058055822370503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122561960430038703881580335 183842940645058055822370503)
      ·
        refine ⟨275764410967587083733555755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183842940645058055822370503 275764410967587083733555755)
        ·
          refine ⟨413646616451380625600333633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275764410967587083733555755 413646616451380625600333633)
          ·
            refine ⟨310234962338535469200250225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413646616451380625600333633 310234962338535469200250225)
            ·
              refine ⟨232676221753901601900187669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310234962338535469200250225 232676221753901601900187669)
              ·
                refine ⟨10906697894714137589071297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 232676221753901601900187669 10906697894714137589071297)
                ·
                  refine ⟨8180023421035603191803473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10906697894714137589071297 8180023421035603191803473)
                  ·
                    refine ⟨6135017565776702393852605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8180023421035603191803473 6135017565776702393852605)
                    ·
                      refine ⟨2300631587166263397694727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135017565776702393852605 2300631587166263397694727)
                      ·
                        rfl

theorem cell23_4480464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 3].length) (baseStart_4480464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480464 prefixEnd_4480464 := by exact prefixLift 4480464
  have htrace : WordTrace (prefixWord ++ tailWord_4480464) baseStart_4480464 baseEnd_4480464 := by
    simpa [prefixWord, tailWord_4480464, baseEnd_4480464] using wordTrace_append hprefix tailTrace_4480464
  have hstable : (prefixWord ++ tailWord_4480464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480464).length < 2 ^ (prefixWord ++ tailWord_4480464).sum := by decide
  have hdescent : baseEnd_4480464 < baseStart_4480464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480471 : List Nat := [1, 1, 3, 2, 1, 1, 1, 8, 1, 4]
def baseStart_4480471 : Nat := 118140960795 + 4480471 * 2 ^ 59
def prefixEnd_4480471 : Nat := 4983230072969 + 3 ^ 40 * 4480471 * 2
def baseEnd_4480471 : Nat := 766878393843614956769065

theorem tailTrace_4480471 : CollatzResearch.WordTrace tailWord_4480471 prefixEnd_4480471 766878393843614956769065 := by
  unfold tailWord_4480471
  simp only [CollatzResearch.WordTrace]
  refine ⟨163416202551026245370945267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108944135034017496913963511 163416202551026245370945267)
  ·
    refine ⟨245124303826539368056417901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163416202551026245370945267 245124303826539368056417901)
    ·
      refine ⟨91921613934952263021156713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245124303826539368056417901 91921613934952263021156713)
      ·
        refine ⟨68941210451214197265867535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91921613934952263021156713 68941210451214197265867535)
        ·
          refine ⟨103411815676821295898801303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68941210451214197265867535 103411815676821295898801303)
          ·
            refine ⟨155117723515231943848201955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103411815676821295898801303 155117723515231943848201955)
            ·
              refine ⟨232676585272847915772302933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155117723515231943848201955 232676585272847915772302933)
              ·
                refine ⟨2726678733666186512956675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 232676585272847915772302933 2726678733666186512956675)
                ·
                  refine ⟨4090018100499279769435013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726678733666186512956675 4090018100499279769435013)
                  ·
                    refine ⟨766878393843614956769065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4090018100499279769435013 766878393843614956769065)
                    ·
                      rfl

theorem cell23_4480471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_4480471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480471 prefixEnd_4480471 := by exact prefixLift 4480471
  have htrace : WordTrace (prefixWord ++ tailWord_4480471) baseStart_4480471 baseEnd_4480471 := by
    simpa [prefixWord, tailWord_4480471, baseEnd_4480471] using wordTrace_append hprefix tailTrace_4480471
  have hstable : (prefixWord ++ tailWord_4480471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480471).length < 2 ^ (prefixWord ++ tailWord_4480471).sum := by decide
  have hdescent : baseEnd_4480471 < baseStart_4480471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480498 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_4480498 : Nat := 118140960795 + 4480498 * 2 ^ 59
def prefixEnd_4480498 : Nat := 4983230072969 + 3 ^ 40 * 4480498 * 2
def baseEnd_4480498 : Nat := 2300649045508516264669571

theorem tailTrace_4480498 : CollatzResearch.WordTrace tailWord_4480498 prefixEnd_4480498 2300649045508516264669571 := by
  unfold tailWord_4480498
  simp only [CollatzResearch.WordTrace]
  refine ⟨40854296830482107245544537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108944791547952285988118765 40854296830482107245544537)
  ·
    refine ⟨30640722622861580434158403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40854296830482107245544537 30640722622861580434158403)
    ·
      refine ⟨45961083934292370651237605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30640722622861580434158403 45961083934292370651237605)
      ·
        refine ⟨8617703237679819497107051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45961083934292370651237605 8617703237679819497107051)
        ·
          refine ⟨12926554856519729245660577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8617703237679819497107051 12926554856519729245660577)
          ·
            refine ⟨9694916142389796934245433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12926554856519729245660577 9694916142389796934245433)
            ·
              refine ⟨7271187106792347700684075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9694916142389796934245433 7271187106792347700684075)
              ·
                refine ⟨10906780660188521551026113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7271187106792347700684075 10906780660188521551026113)
                ·
                  refine ⟨8180085495141391163269585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10906780660188521551026113 8180085495141391163269585)
                  ·
                    refine ⟨6135064121356043372452189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8180085495141391163269585 6135064121356043372452189)
                    ·
                      refine ⟨2300649045508516264669571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135064121356043372452189 2300649045508516264669571)
                      ·
                        rfl

theorem cell23_4480498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_4480498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480498 prefixEnd_4480498 := by exact prefixLift 4480498
  have htrace : WordTrace (prefixWord ++ tailWord_4480498) baseStart_4480498 baseEnd_4480498 := by
    simpa [prefixWord, tailWord_4480498, baseEnd_4480498] using wordTrace_append hprefix tailTrace_4480498
  have hstable : (prefixWord ++ tailWord_4480498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480498).length < 2 ^ (prefixWord ++ tailWord_4480498).sum := by decide
  have hdescent : baseEnd_4480498 < baseStart_4480498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480521 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 2, 3, 2]
def baseStart_4480521 : Nat := 118140960795 + 4480521 * 2 ^ 59
def prefixEnd_4480521 : Nat := 4983230072969 + 3 ^ 40 * 4480521 * 2
def baseEnd_4480521 : Nat := 2300660855563569674681965

theorem tailTrace_4480521 : CollatzResearch.WordTrace tailWord_4480521 prefixEnd_4480521 2300660855563569674681965 := by
  unfold tailWord_4480521
  simp only [CollatzResearch.WordTrace]
  refine ⟨163418026200845103910265417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108945350800563402606843611 163418026200845103910265417)
  ·
    refine ⟨122563519650633827932699063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163418026200845103910265417 122563519650633827932699063)
    ·
      refine ⟨183845279475950741899048595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122563519650633827932699063 183845279475950741899048595)
      ·
        refine ⟨275767919213926112848572893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183845279475950741899048595 275767919213926112848572893)
        ·
          refine ⟨103412969705222292318214835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275767919213926112848572893 103412969705222292318214835)
          ·
            refine ⟨155119454557833438477322253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103412969705222292318214835 155119454557833438477322253)
            ·
              refine ⟨58169795459187539428995845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155119454557833438477322253 58169795459187539428995845)
              ·
                refine ⟨10906836648597663642936721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58169795459187539428995845 10906836648597663642936721)
                ·
                  refine ⟨8180127486448247732202541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10906836648597663642936721 8180127486448247732202541)
                  ·
                    refine ⟨3067547807418092899575953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8180127486448247732202541 3067547807418092899575953)
                    ·
                      refine ⟨2300660855563569674681965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067547807418092899575953 2300660855563569674681965)
                      ·
                        rfl

theorem cell23_4480521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 3, 2].length) (baseStart_4480521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480521 prefixEnd_4480521 := by exact prefixLift 4480521
  have htrace : WordTrace (prefixWord ++ tailWord_4480521) baseStart_4480521 baseEnd_4480521 := by
    simpa [prefixWord, tailWord_4480521, baseEnd_4480521] using wordTrace_append hprefix tailTrace_4480521
  have hstable : (prefixWord ++ tailWord_4480521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480521).length < 2 ^ (prefixWord ++ tailWord_4480521).sum := by decide
  have hdescent : baseEnd_4480521 < baseStart_4480521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480568 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 1, 1, 4]
def baseStart_4480568 : Nat := 118140960795 + 4480568 * 2 ^ 59
def prefixEnd_4480568 : Nat := 4983230072969 + 3 ^ 40 * 4480568 * 2
def baseEnd_4480568 : Nat := 2300684989154330990794249

theorem tailTrace_4480568 : CollatzResearch.WordTrace tailWord_4480568 prefixEnd_4480568 2300684989154330990794249 := by
  unfold tailWord_4480568
  simp only [CollatzResearch.WordTrace]
  refine ⟨81709870215837415468613179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108946493621116553958150905 81709870215837415468613179)
  ·
    refine ⟨122564805323756123202919769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81709870215837415468613179 122564805323756123202919769)
    ·
      refine ⟨91923603992817092402189827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122564805323756123202919769 91923603992817092402189827)
      ·
        refine ⟨137885405989225638603284741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91923603992817092402189827 137885405989225638603284741)
        ·
          refine ⟨25853513622979807238115889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137885405989225638603284741 25853513622979807238115889)
          ·
            refine ⟨19390135217234855428586917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25853513622979807238115889 19390135217234855428586917)
            ·
              refine ⟨3635650353231535392860047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19390135217234855428586917 3635650353231535392860047)
              ·
                refine ⟨5453475529847303089290071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635650353231535392860047 5453475529847303089290071)
                ·
                  refine ⟨8180213294770954633935107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5453475529847303089290071 8180213294770954633935107)
                  ·
                    refine ⟨12270319942156431950902661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8180213294770954633935107 12270319942156431950902661)
                    ·
                      refine ⟨2300684989154330990794249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12270319942156431950902661 2300684989154330990794249)
                      ·
                        rfl

theorem cell23_4480568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_4480568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480568 prefixEnd_4480568 := by exact prefixLift 4480568
  have htrace : WordTrace (prefixWord ++ tailWord_4480568) baseStart_4480568 baseEnd_4480568 := by
    simpa [prefixWord, tailWord_4480568, baseEnd_4480568] using wordTrace_append hprefix tailTrace_4480568
  have hstable : (prefixWord ++ tailWord_4480568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480568).length < 2 ^ (prefixWord ++ tailWord_4480568).sum := by decide
  have hdescent : baseEnd_4480568 < baseStart_4480568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480584 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_4480584 : Nat := 118140960795 + 4480584 * 2 ^ 59
def prefixEnd_4480584 : Nat := 4983230072969 + 3 ^ 40 * 4480584 * 2
def baseEnd_4480584 : Nat := 2300693204844802928194175

theorem tailTrace_4480584 : CollatzResearch.WordTrace tailWord_4480584 prefixEnd_4480584 2300693204844802928194175 := by
  unfold tailWord_4480584
  simp only [CollatzResearch.WordTrace]
  refine ⟨81710161999808432834904403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108946882666411243779872537 81710161999808432834904403)
  ·
    refine ⟨122565242999712649252356605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81710161999808432834904403 122565242999712649252356605)
    ·
      refine ⟨45961966124892243469633727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122565242999712649252356605 45961966124892243469633727)
      ·
        refine ⟨68942949187338365204450591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45961966124892243469633727 68942949187338365204450591)
        ·
          refine ⟨103414423781007547806675887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68942949187338365204450591 103414423781007547806675887)
          ·
            refine ⟨155121635671511321710013831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103414423781007547806675887 155121635671511321710013831)
            ·
              refine ⟨232682453507266982565020747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155121635671511321710013831 232682453507266982565020747)
              ·
                refine ⟨349023680260900473847531121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232682453507266982565020747 349023680260900473847531121)
                ·
                  refine ⟨261767760195675355385648341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349023680260900473847531121 261767760195675355385648341)
                  ·
                    refine ⟨6135181879586141141851133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 261767760195675355385648341 6135181879586141141851133)
                    ·
                      refine ⟨2300693204844802928194175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135181879586141141851133 2300693204844802928194175)
                      ·
                        rfl

theorem cell23_4480584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_4480584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480584 prefixEnd_4480584 := by exact prefixLift 4480584
  have htrace : WordTrace (prefixWord ++ tailWord_4480584) baseStart_4480584 baseEnd_4480584 := by
    simpa [prefixWord, tailWord_4480584, baseEnd_4480584] using wordTrace_append hprefix tailTrace_4480584
  have hstable : (prefixWord ++ tailWord_4480584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480584).length < 2 ^ (prefixWord ++ tailWord_4480584).sum := by decide
  have hdescent : baseEnd_4480584 < baseStart_4480584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480618 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_4480618 : Nat := 118140960795 + 4480618 * 2 ^ 59
def prefixEnd_4480618 : Nat := 4983230072969 + 3 ^ 40 * 4480618 * 2
def baseEnd_4480618 : Nat := 2300710663187055795169019

theorem tailTrace_4480618 : CollatzResearch.WordTrace tailWord_4480618 prefixEnd_4480618 2300710663187055795169019 := by
  unfold tailWord_4480618
  simp only [CollatzResearch.WordTrace]
  refine ⟨40855391020373422369136627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108947709387662459651031005 40855391020373422369136627)
  ·
    refine ⟨61283086530560133553704941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40855391020373422369136627 61283086530560133553704941)
    ·
      refine ⟨22981157448960050082639353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61283086530560133553704941 22981157448960050082639353)
      ·
        refine ⟨17235868086720037561979515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22981157448960050082639353 17235868086720037561979515)
        ·
          refine ⟨25853802130080056342969273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17235868086720037561979515 25853802130080056342969273)
          ·
            refine ⟨19390351597560042257226955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25853802130080056342969273 19390351597560042257226955)
            ·
              refine ⟨29085527396340063385840433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19390351597560042257226955 29085527396340063385840433)
              ·
                refine ⟨21814145547255047539380325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29085527396340063385840433 21814145547255047539380325)
                ·
                  refine ⟨4090152290110321413633811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21814145547255047539380325 4090152290110321413633811)
                  ·
                    refine ⟨6135228435165482120450717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4090152290110321413633811 6135228435165482120450717)
                    ·
                      refine ⟨2300710663187055795169019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135228435165482120450717 2300710663187055795169019)
                      ·
                        rfl

theorem cell23_4480618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_4480618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480618 prefixEnd_4480618 := by exact prefixLift 4480618
  have htrace : WordTrace (prefixWord ++ tailWord_4480618) baseStart_4480618 baseEnd_4480618 := by
    simpa [prefixWord, tailWord_4480618, baseEnd_4480618] using wordTrace_append hprefix tailTrace_4480618
  have hstable : (prefixWord ++ tailWord_4480618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480618).length < 2 ^ (prefixWord ++ tailWord_4480618).sum := by decide
  have hdescent : baseEnd_4480618 < baseStart_4480618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480634 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_4480634 : Nat := 118140960795 + 4480634 * 2 ^ 59
def prefixEnd_4480634 : Nat := 4983230072969 + 3 ^ 40 * 4480634 * 2
def baseEnd_4480634 : Nat := 766906292959175910856315

theorem tailTrace_4480634 : CollatzResearch.WordTrace tailWord_4480634 prefixEnd_4480634 766906292959175910856315 := by
  unfold tailWord_4480634
  simp only [CollatzResearch.WordTrace]
  refine ⟨40855536912358931052282239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108948098432957149472752637 40855536912358931052282239)
  ·
    refine ⟨61283305368538396578423359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40855536912358931052282239 61283305368538396578423359)
    ·
      refine ⟨91924958052807594867635039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61283305368538396578423359 91924958052807594867635039)
      ·
        refine ⟨137887437079211392301452559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91924958052807594867635039 137887437079211392301452559)
        ·
          refine ⟨206831155618817088452178839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137887437079211392301452559 206831155618817088452178839)
          ·
            refine ⟨310246733428225632678268259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206831155618817088452178839 310246733428225632678268259)
            ·
              refine ⟨465370100142338449017402389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310246733428225632678268259 465370100142338449017402389)
              ·
                refine ⟨21814223444172114797690737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 465370100142338449017402389 21814223444172114797690737)
                ·
                  refine ⟨16360667583129086098268053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21814223444172114797690737 16360667583129086098268053)
                  ·
                    refine ⟨766906292959175910856315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16360667583129086098268053 766906292959175910856315)
                    ·
                      rfl

theorem cell23_4480634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_4480634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480634 prefixEnd_4480634 := by exact prefixLift 4480634
  have htrace : WordTrace (prefixWord ++ tailWord_4480634) baseStart_4480634 baseEnd_4480634 := by
    simpa [prefixWord, tailWord_4480634, baseEnd_4480634] using wordTrace_append hprefix tailTrace_4480634
  have hstable : (prefixWord ++ tailWord_4480634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480634).length < 2 ^ (prefixWord ++ tailWord_4480634).sum := by decide
  have hdescent : baseEnd_4480634 < baseStart_4480634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480691 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 3]
def baseStart_4480691 : Nat := 118140960795 + 4480691 * 2 ^ 59
def prefixEnd_4480691 : Nat := 4983230072969 + 3 ^ 40 * 4480691 * 2
def baseEnd_4480691 : Nat := 2300748147274834009556183

theorem tailTrace_4480691 : CollatzResearch.WordTrace tailWord_4480691 prefixEnd_4480691 2300748147274834009556183 := by
  unfold tailWord_4480691
  simp only [CollatzResearch.WordTrace]
  refine ⟨163424226610229222943953927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108949484406819481962635951 163424226610229222943953927)
  ·
    refine ⟨245136339915343834415930891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163424226610229222943953927 245136339915343834415930891)
    ·
      refine ⟨367704509873015751623896337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245136339915343834415930891 367704509873015751623896337)
      ·
        refine ⟨275778382404761813717922253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367704509873015751623896337 275778382404761813717922253)
        ·
          refine ⟨103416893401785680144220845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275778382404761813717922253 103416893401785680144220845)
          ·
            refine ⟨38781335025669630054082817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103416893401785680144220845 38781335025669630054082817)
            ·
              refine ⟨29086001269252222540562113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38781335025669630054082817 29086001269252222540562113)
              ·
                refine ⟨21814500951939166905421585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29086001269252222540562113 21814500951939166905421585)
                ·
                  refine ⟨16360875713954375179066189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21814500951939166905421585 16360875713954375179066189)
                  ·
                    refine ⟨6135328392732890692149821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16360875713954375179066189 6135328392732890692149821)
                    ·
                      refine ⟨2300748147274834009556183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135328392732890692149821 2300748147274834009556183)
                      ·
                        rfl

theorem cell23_4480691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_4480691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480691 prefixEnd_4480691 := by exact prefixLift 4480691
  have htrace : WordTrace (prefixWord ++ tailWord_4480691) baseStart_4480691 baseEnd_4480691 := by
    simpa [prefixWord, tailWord_4480691, baseEnd_4480691] using wordTrace_append hprefix tailTrace_4480691
  have hstable : (prefixWord ++ tailWord_4480691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480691).length < 2 ^ (prefixWord ++ tailWord_4480691).sum := by decide
  have hdescent : baseEnd_4480691 < baseStart_4480691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480698 : List Nat := [3, 1, 1, 1, 2, 5, 1, 4, 5]
def baseStart_4480698 : Nat := 118140960795 + 4480698 * 2 ^ 59
def prefixEnd_4480698 : Nat := 4983230072969 + 3 ^ 40 * 4480698 * 2
def baseEnd_4480698 : Nat := 255639082404379498018739

theorem tailTrace_4480698 : CollatzResearch.WordTrace tailWord_4480698 prefixEnd_4480698 255639082404379498018739 := by
  unfold tailWord_4480698
  simp only [CollatzResearch.WordTrace]
  refine ⟨40856120480300965784864687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108949654614135908759639165 40856120480300965784864687)
  ·
    refine ⟨61284180720451448677297031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40856120480300965784864687 61284180720451448677297031)
    ·
      refine ⟨91926271080677173015945547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61284180720451448677297031 91926271080677173015945547)
      ·
        refine ⟨137889406621015759523918321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91926271080677173015945547 137889406621015759523918321)
        ·
          refine ⟨103417054965761819642938741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137889406621015759523918321 103417054965761819642938741)
          ·
            refine ⟨9695348903040170591525507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103417054965761819642938741 9695348903040170591525507)
            ·
              refine ⟨14543023354560255887288261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9695348903040170591525507 14543023354560255887288261)
              ·
                refine ⟨2726816878980047978866549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14543023354560255887288261 2726816878980047978866549)
                ·
                  refine ⟨255639082404379498018739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2726816878980047978866549 255639082404379498018739)
                  ·
                    rfl

theorem cell23_4480698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_4480698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480698 prefixEnd_4480698 := by exact prefixLift 4480698
  have htrace : WordTrace (prefixWord ++ tailWord_4480698) baseStart_4480698 baseEnd_4480698 := by
    simpa [prefixWord, tailWord_4480698, baseEnd_4480698] using wordTrace_append hprefix tailTrace_4480698
  have hstable : (prefixWord ++ tailWord_4480698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480698).length < 2 ^ (prefixWord ++ tailWord_4480698).sum := by decide
  have hdescent : baseEnd_4480698 < baseStart_4480698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480708 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_4480708 : Nat := 118140960795 + 4480708 * 2 ^ 59
def prefixEnd_4480708 : Nat := 4983230072969 + 3 ^ 40 * 4480708 * 2
def baseEnd_4480708 : Nat := 2300756876445960443043605

theorem tailTrace_4480708 : CollatzResearch.WordTrace tailWord_4480708 prefixEnd_4480708 2300756876445960443043605 := by
  unfold tailWord_4480708
  simp only [CollatzResearch.WordTrace]
  refine ⟨81712423325583817423661389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108949897767445089898215185 81712423325583817423661389)
  ·
    refine ⟨30642158747093931533873021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81712423325583817423661389 30642158747093931533873021)
    ·
      refine ⟨11490809530160224325202383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30642158747093931533873021 11490809530160224325202383)
      ·
        refine ⟨17236214295240336487803575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11490809530160224325202383 17236214295240336487803575)
        ·
          refine ⟨25854321442860504731705363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17236214295240336487803575 25854321442860504731705363)
          ·
            refine ⟨38781482164290757097558045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25854321442860504731705363 38781482164290757097558045)
            ·
              refine ⟨14543055811609033911584267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38781482164290757097558045 14543055811609033911584267)
              ·
                refine ⟨21814583717413550867376401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14543055811609033911584267 21814583717413550867376401)
                ·
                  refine ⟨16360937788060163150532301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21814583717413550867376401 16360937788060163150532301)
                  ·
                    refine ⟨6135351670522561181449613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16360937788060163150532301 6135351670522561181449613)
                    ·
                      refine ⟨2300756876445960443043605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135351670522561181449613 2300756876445960443043605)
                      ·
                        rfl

theorem cell23_4480708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_4480708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480708 prefixEnd_4480708 := by exact prefixLift 4480708
  have htrace : WordTrace (prefixWord ++ tailWord_4480708) baseStart_4480708 baseEnd_4480708 := by
    simpa [prefixWord, tailWord_4480708, baseEnd_4480708] using wordTrace_append hprefix tailTrace_4480708
  have hstable : (prefixWord ++ tailWord_4480708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480708).length < 2 ^ (prefixWord ++ tailWord_4480708).sum := by decide
  have hdescent : baseEnd_4480708 < baseStart_4480708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480718 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_4480718 : Nat := 118140960795 + 4480718 * 2 ^ 59
def prefixEnd_4480718 : Nat := 4983230072969 + 3 ^ 40 * 4480718 * 2
def baseEnd_4480718 : Nat := 2300762011252505403918559

theorem tailTrace_4480718 : CollatzResearch.WordTrace tailWord_4480718 prefixEnd_4480718 2300762011252505403918559 := by
  unfold tailWord_4480718
  simp only [CollatzResearch.WordTrace]
  refine ⟨20428151422641425819398351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108950140920754271036791205 20428151422641425819398351)
  ·
    refine ⟨30642227133962138729097527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20428151422641425819398351 30642227133962138729097527)
    ·
      refine ⟨45963340700943208093646291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30642227133962138729097527 45963340700943208093646291)
      ·
        refine ⟨68945011051414812140469437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45963340700943208093646291 68945011051414812140469437)
        ·
          refine ⟨25854379144280554552676039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68945011051414812140469437 25854379144280554552676039)
          ·
            refine ⟨38781568716420831829014059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25854379144280554552676039 38781568716420831829014059)
            ·
              refine ⟨58172353074631247743521089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38781568716420831829014059 58172353074631247743521089)
              ·
                refine ⟨43629264805973435807640817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58172353074631247743521089 43629264805973435807640817)
                ·
                  refine ⟨32721948604480076855730613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43629264805973435807640817 32721948604480076855730613)
                  ·
                    refine ⟨3067682681670007205224745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32721948604480076855730613 3067682681670007205224745)
                    ·
                      refine ⟨2300762011252505403918559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067682681670007205224745 2300762011252505403918559)
                      ·
                        rfl

theorem cell23_4480718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_4480718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480718 prefixEnd_4480718 := by exact prefixLift 4480718
  have htrace : WordTrace (prefixWord ++ tailWord_4480718) baseStart_4480718 baseEnd_4480718 := by
    simpa [prefixWord, tailWord_4480718, baseEnd_4480718] using wordTrace_append hprefix tailTrace_4480718
  have hstable : (prefixWord ++ tailWord_4480718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480718).length < 2 ^ (prefixWord ++ tailWord_4480718).sum := by decide
  have hdescent : baseEnd_4480718 < baseStart_4480718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480732 : List Nat := [2, 2, 5, 1, 2, 1, 2, 3, 5]
def baseStart_4480732 : Nat := 118140960795 + 4480732 * 2 ^ 59
def prefixEnd_4480732 : Nat := 4983230072969 + 3 ^ 40 * 4480732 * 2
def baseEnd_4480732 : Nat := 255641022220185372127055

theorem tailTrace_4480732 : CollatzResearch.WordTrace tailWord_4480732 prefixEnd_4480732 255641022220185372127055 := by
  unfold tailWord_4480732
  simp only [CollatzResearch.WordTrace]
  refine ⟨81712861001540343473098225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108950481335387124630797633 81712861001540343473098225)
  ·
    refine ⟨61284645751155257604823669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81712861001540343473098225 61284645751155257604823669)
    ·
      refine ⟨5745435539170805400452219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61284645751155257604823669 5745435539170805400452219)
      ·
        refine ⟨8618153308756208100678329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5745435539170805400452219 8618153308756208100678329)
        ·
          refine ⟨6463614981567156075508747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8618153308756208100678329 6463614981567156075508747)
          ·
            refine ⟨9695422472350734113263121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6463614981567156075508747 9695422472350734113263121)
            ·
              refine ⟨7271566854263050584947341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9695422472350734113263121 7271566854263050584947341)
              ·
                refine ⟨2726837570348643969355253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7271566854263050584947341 2726837570348643969355253)
                ·
                  refine ⟨255641022220185372127055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2726837570348643969355253 255641022220185372127055)
                  ·
                    rfl

theorem cell23_4480732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_4480732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480732 prefixEnd_4480732 := by exact prefixLift 4480732
  have htrace : WordTrace (prefixWord ++ tailWord_4480732) baseStart_4480732 baseEnd_4480732 := by
    simpa [prefixWord, tailWord_4480732, baseEnd_4480732] using wordTrace_append hprefix tailTrace_4480732
  have hstable : (prefixWord ++ tailWord_4480732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480732).length < 2 ^ (prefixWord ++ tailWord_4480732).sum := by decide
  have hdescent : baseEnd_4480732 < baseStart_4480732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480748 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 2, 4, 2]
def baseStart_4480748 : Nat := 118140960795 + 4480748 * 2 ^ 59
def prefixEnd_4480748 : Nat := 4983230072969 + 3 ^ 40 * 4480748 * 2
def baseEnd_4480748 : Nat := 2300777415672140286543421

theorem tailTrace_4480748 : CollatzResearch.WordTrace tailWord_4480748 prefixEnd_4480748 2300777415672140286543421 := by
  unfold tailWord_4480748
  simp only [CollatzResearch.WordTrace]
  refine ⟨81713152785511360839389449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108950870380681814452519265 81713152785511360839389449)
  ·
    refine ⟨61284864589133520629542087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81713152785511360839389449 61284864589133520629542087)
    ·
      refine ⟨91927296883700280944313131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61284864589133520629542087 91927296883700280944313131)
      ·
        refine ⟨137890945325550421416469697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91927296883700280944313131 137890945325550421416469697)
        ·
          refine ⟨103418208994162816062352273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137890945325550421416469697 103418208994162816062352273)
          ·
            refine ⟨77563656745622112046764205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103418208994162816062352273 77563656745622112046764205)
            ·
              refine ⟨29086371279608292017536577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77563656745622112046764205 29086371279608292017536577)
              ·
                refine ⟨21814778459706219013152433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29086371279608292017536577 21814778459706219013152433)
                ·
                  refine ⟨16361083844779664259864325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21814778459706219013152433 16361083844779664259864325)
                  ·
                    refine ⟨3067703220896187048724561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16361083844779664259864325 3067703220896187048724561)
                    ·
                      refine ⟨2300777415672140286543421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067703220896187048724561 2300777415672140286543421)
                      ·
                        rfl

theorem cell23_4480748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_4480748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480748 prefixEnd_4480748 := by exact prefixLift 4480748
  have htrace : WordTrace (prefixWord ++ tailWord_4480748) baseStart_4480748 baseEnd_4480748 := by
    simpa [prefixWord, tailWord_4480748, baseEnd_4480748] using wordTrace_append hprefix tailTrace_4480748
  have hstable : (prefixWord ++ tailWord_4480748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480748).length < 2 ^ (prefixWord ++ tailWord_4480748).sum := by decide
  have hdescent : baseEnd_4480748 < baseStart_4480748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480771 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 6]
def baseStart_4480771 : Nat := 118140960795 + 4480771 * 2 ^ 59
def prefixEnd_4480771 : Nat := 4983230072969 + 3 ^ 40 * 4480771 * 2
def baseEnd_4480771 : Nat := 255643247303021521839535

theorem tailTrace_4480771 : CollatzResearch.WordTrace tailWord_4480771 prefixEnd_4480771 255643247303021521839535 := by
  unfold tailWord_4480771
  simp only [CollatzResearch.WordTrace]
  refine ⟨163427144449939396606866167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108951429633292931071244111 163427144449939396606866167)
  ·
    refine ⟨245140716674909094910299251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163427144449939396606866167 245140716674909094910299251)
    ·
      refine ⟨367711075012363642365448877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245140716674909094910299251 367711075012363642365448877)
      ·
        refine ⟨137891653129636365887043329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367711075012363642365448877 137891653129636365887043329)
        ·
          refine ⟨103418739847227274415282497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137891653129636365887043329 103418739847227274415282497)
          ·
            refine ⟨77564054885420455811461873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103418739847227274415282497 77564054885420455811461873)
            ·
              refine ⟨58173041164065341858596405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77564054885420455811461873 58173041164065341858596405)
              ·
                refine ⟨5453722609131125799243413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58173041164065341858596405 5453722609131125799243413)
                ·
                  refine ⟨255643247303021521839535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5453722609131125799243413 255643247303021521839535)
                  ·
                    rfl

theorem cell23_4480771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 6].length) (baseStart_4480771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480771 prefixEnd_4480771 := by exact prefixLift 4480771
  have htrace : WordTrace (prefixWord ++ tailWord_4480771) baseStart_4480771 baseEnd_4480771 := by
    simpa [prefixWord, tailWord_4480771, baseEnd_4480771] using wordTrace_append hprefix tailTrace_4480771
  have hstable : (prefixWord ++ tailWord_4480771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480771).length < 2 ^ (prefixWord ++ tailWord_4480771).sum := by decide
  have hdescent : baseEnd_4480771 < baseStart_4480771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480822 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_4480822 : Nat := 118140960795 + 4480822 * 2 ^ 59
def prefixEnd_4480822 : Nat := 4983230072969 + 3 ^ 40 * 4480822 * 2
def baseEnd_4480822 : Nat := 255646157026730333002009

theorem tailTrace_4480822 : CollatzResearch.WordTrace tailWord_4480822 prefixEnd_4480822 255646157026730333002009 := by
  unfold tailWord_4480822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214312785797164519810795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108952669715169754877981813 10214312785797164519810795)
  ·
    refine ⟨15321469178695746779716193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10214312785797164519810795 15321469178695746779716193)
    ·
      refine ⟨11491101884021810084787145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15321469178695746779716193 11491101884021810084787145)
      ·
        refine ⟨8618326413016357563590359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11491101884021810084787145 8618326413016357563590359)
        ·
          refine ⟨12927489619524536345385539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8618326413016357563590359 12927489619524536345385539)
          ·
            refine ⟨19391234429286804518078309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12927489619524536345385539 19391234429286804518078309)
            ·
              refine ⟨3635856455491275847139683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19391234429286804518078309 3635856455491275847139683)
              ·
                refine ⟨5453784683236913770709525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635856455491275847139683 5453784683236913770709525)
                ·
                  refine ⟨255646157026730333002009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5453784683236913770709525 255646157026730333002009)
                  ·
                    rfl

theorem cell23_4480822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_4480822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480822 prefixEnd_4480822 := by exact prefixLift 4480822
  have htrace : WordTrace (prefixWord ++ tailWord_4480822) baseStart_4480822 baseEnd_4480822 := by
    simpa [prefixWord, tailWord_4480822, baseEnd_4480822] using wordTrace_append hprefix tailTrace_4480822
  have hstable : (prefixWord ++ tailWord_4480822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480822).length < 2 ^ (prefixWord ++ tailWord_4480822).sum := by decide
  have hdescent : baseEnd_4480822 < baseStart_4480822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480835 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 1, 5]
def baseStart_4480835 : Nat := 118140960795 + 4480835 * 2 ^ 59
def prefixEnd_4480835 : Nat := 4983230072969 + 3 ^ 40 * 4480835 * 2
def baseEnd_4480835 : Nat := 766940696163027148718507

theorem tailTrace_4480835 : CollatzResearch.WordTrace tailWord_4480835 prefixEnd_4480835 766940696163027148718507 := by
  unfold tailWord_4480835
  simp only [CollatzResearch.WordTrace]
  refine ⟨163429478721707535537195959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108952985814471690358130639 163429478721707535537195959)
  ·
    refine ⟨245144218082561303305793939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163429478721707535537195959 245144218082561303305793939)
    ·
      refine ⟨367716327123841954958690909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245144218082561303305793939 367716327123841954958690909)
      ·
        refine ⟨137893622671440733109509091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367716327123841954958690909 137893622671440733109509091)
        ·
          refine ⟨206840434007161099664263637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137893622671440733109509091 206840434007161099664263637)
          ·
            refine ⟨4847822672042838273381179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 206840434007161099664263637 4847822672042838273381179)
            ·
              refine ⟨7271734008064257410071769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847822672042838273381179 7271734008064257410071769)
              ·
                refine ⟨5453800506048193057553827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7271734008064257410071769 5453800506048193057553827)
                ·
                  refine ⟨8180700759072289586330741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5453800506048193057553827 8180700759072289586330741)
                  ·
                    refine ⟨766940696163027148718507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8180700759072289586330741 766940696163027148718507)
                    ·
                      rfl

theorem cell23_4480835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 5].length) (baseStart_4480835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480835 prefixEnd_4480835 := by exact prefixLift 4480835
  have htrace : WordTrace (prefixWord ++ tailWord_4480835) baseStart_4480835 baseEnd_4480835 := by
    simpa [prefixWord, tailWord_4480835, baseEnd_4480835] using wordTrace_append hprefix tailTrace_4480835
  have hstable : (prefixWord ++ tailWord_4480835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480835).length < 2 ^ (prefixWord ++ tailWord_4480835).sum := by decide
  have hdescent : baseEnd_4480835 < baseStart_4480835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480852 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_4480852 : Nat := 118140960795 + 4480852 * 2 ^ 59
def prefixEnd_4480852 : Nat := 4983230072969 + 3 ^ 40 * 4480852 * 2
def baseEnd_4480852 : Nat := 766943605886735959880981

theorem tailTrace_4480852 : CollatzResearch.WordTrace tailWord_4480852 prefixEnd_4480852 766943605886735959880981 := by
  unfold tailWord_4480852
  simp only [CollatzResearch.WordTrace]
  refine ⟨81715049381322973720282405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108953399175097298293709873 81715049381322973720282405)
  ·
    refine ⟨15321571758998057572552951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81715049381322973720282405 15321571758998057572552951)
    ·
      refine ⟨22982357638497086358829427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15321571758998057572552951 22982357638497086358829427)
      ·
        refine ⟨34473536457745629538244141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22982357638497086358829427 34473536457745629538244141)
        ·
          refine ⟨12927576171654611076841553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34473536457745629538244141 12927576171654611076841553)
          ·
            refine ⟨9695682128740958307631165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12927576171654611076841553 9695682128740958307631165)
            ·
              refine ⟨3635880798277859365361687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9695682128740958307631165 3635880798277859365361687)
              ·
                refine ⟨5453821197416789048042531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635880798277859365361687 5453821197416789048042531)
                ·
                  refine ⟨8180731796125183572063797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5453821197416789048042531 8180731796125183572063797)
                  ·
                    refine ⟨766943605886735959880981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8180731796125183572063797 766943605886735959880981)
                    ·
                      rfl

theorem cell23_4480852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_4480852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480852 prefixEnd_4480852 := by exact prefixLift 4480852
  have htrace : WordTrace (prefixWord ++ tailWord_4480852) baseStart_4480852 baseEnd_4480852 := by
    simpa [prefixWord, tailWord_4480852, baseEnd_4480852] using wordTrace_append hprefix tailTrace_4480852
  have hstable : (prefixWord ++ tailWord_4480852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480852).length < 2 ^ (prefixWord ++ tailWord_4480852).sum := by decide
  have hdescent : baseEnd_4480852 < baseStart_4480852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480865 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 2, 4]
def baseStart_4480865 : Nat := 118140960795 + 4480865 * 2 ^ 59
def prefixEnd_4480865 : Nat := 4983230072969 + 3 ^ 40 * 4480865 * 2
def baseEnd_4480865 : Nat := 766945830969572109593461

theorem tailTrace_4480865 : CollatzResearch.WordTrace tailWord_4480865 prefixEnd_4480865 766945830969572109593461 := by
  unfold tailWord_4480865
  simp only [CollatzResearch.WordTrace]
  refine ⟨163430572911598850660788049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108953715274399233773858699 163430572911598850660788049)
  ·
    refine ⟨122572929683699137995591037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163430572911598850660788049 122572929683699137995591037)
    ·
      refine ⟨45964848631387176748346639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122572929683699137995591037 45964848631387176748346639)
      ·
        refine ⟨68947272947080765122519959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45964848631387176748346639 68947272947080765122519959)
        ·
          refine ⟨103420909420621147683779939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68947272947080765122519959 103420909420621147683779939)
          ·
            refine ⟨155131364130931721525669909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103420909420621147683779939 155131364130931721525669909)
            ·
              refine ⟨7271782693637424446515777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155131364130931721525669909 7271782693637424446515777)
              ·
                refine ⟨5453837020228068334886833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7271782693637424446515777 5453837020228068334886833)
                ·
                  refine ⟨4090377765171051251165125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5453837020228068334886833 4090377765171051251165125)
                  ·
                    refine ⟨766945830969572109593461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4090377765171051251165125 766945830969572109593461)
                    ·
                      rfl

theorem cell23_4480865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_4480865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480865 prefixEnd_4480865 := by exact prefixLift 4480865
  have htrace : WordTrace (prefixWord ++ tailWord_4480865) baseStart_4480865 baseEnd_4480865 := by
    simpa [prefixWord, tailWord_4480865, baseEnd_4480865] using wordTrace_append hprefix tailTrace_4480865
  have hstable : (prefixWord ++ tailWord_4480865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480865).length < 2 ^ (prefixWord ++ tailWord_4480865).sum := by decide
  have hdescent : baseEnd_4480865 < baseStart_4480865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480866 : List Nat := [3, 3, 2, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_4480866 : Nat := 118140960795 + 4480866 * 2 ^ 59
def prefixEnd_4480866 : Nat := 4983230072969 + 3 ^ 40 * 4480866 * 2
def baseEnd_4480866 : Nat := 2300838006389370824867879

theorem tailTrace_4480866 : CollatzResearch.WordTrace tailWord_4480866 prefixEnd_4480866 2300838006389370824867879 := by
  unfold tailWord_4480866
  simp only [CollatzResearch.WordTrace]
  refine ⟨40857652346148806957893613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108953739589730151887716301 40857652346148806957893613)
  ·
    refine ⟨15321619629805802609210105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40857652346148806957893613 15321619629805802609210105)
    ·
      refine ⟨11491214722354351956907579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15321619629805802609210105 11491214722354351956907579)
      ·
        refine ⟨17236822083531527935361369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11491214722354351956907579 17236822083531527935361369)
        ·
          refine ⟨12927616562648645951521027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17236822083531527935361369 12927616562648645951521027)
          ·
            refine ⟨19391424843972968927281541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12927616562648645951521027 19391424843972968927281541)
            ·
              refine ⟨3635892158244931673865289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19391424843972968927281541 3635892158244931673865289)
              ·
                refine ⟨2726919118683698755398967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635892158244931673865289 2726919118683698755398967)
                ·
                  refine ⟨4090378678025548133098451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726919118683698755398967 4090378678025548133098451)
                  ·
                    refine ⟨6135568017038322199647677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4090378678025548133098451 6135568017038322199647677)
                    ·
                      refine ⟨2300838006389370824867879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135568017038322199647677 2300838006389370824867879)
                      ·
                        rfl

theorem cell23_4480866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_4480866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480866 prefixEnd_4480866 := by exact prefixLift 4480866
  have htrace : WordTrace (prefixWord ++ tailWord_4480866) baseStart_4480866 baseEnd_4480866 := by
    simpa [prefixWord, tailWord_4480866, baseEnd_4480866] using wordTrace_append hprefix tailTrace_4480866
  have hstable : (prefixWord ++ tailWord_4480866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480866).length < 2 ^ (prefixWord ++ tailWord_4480866).sum := by decide
  have hdescent : baseEnd_4480866 < baseStart_4480866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480872 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_4480872 : Nat := 118140960795 + 4480872 * 2 ^ 59
def prefixEnd_4480872 : Nat := 4983230072969 + 3 ^ 40 * 4480872 * 2
def baseEnd_4480872 : Nat := 2300841087273297801392851

theorem tailTrace_4480872 : CollatzResearch.WordTrace tailWord_4480872 prefixEnd_4480872 2300841087273297801392851 := by
  unfold tailWord_4480872
  simp only [CollatzResearch.WordTrace]
  refine ⟨81715414111286745428146435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108953885481715660570861913 81715414111286745428146435)
  ·
    refine ⟨122573121166930118142219653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81715414111286745428146435 122573121166930118142219653)
    ·
      refine ⟨22982460218799397151666185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122573121166930118142219653 22982460218799397151666185)
      ·
        refine ⟨17236845164099547863749639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22982460218799397151666185 17236845164099547863749639)
        ·
          refine ⟨25855267746149321795624459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17236845164099547863749639 25855267746149321795624459)
          ·
            refine ⟨38782901619223982693436689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25855267746149321795624459 38782901619223982693436689)
            ·
              refine ⟨29087176214417987020077517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38782901619223982693436689 29087176214417987020077517)
              ·
                refine ⟨10907691080406745132529069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29087176214417987020077517 10907691080406745132529069)
                ·
                  refine ⟨4090384155152529424698401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10907691080406745132529069 4090384155152529424698401)
                  ·
                    refine ⟨3067788116364397068523801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4090384155152529424698401 3067788116364397068523801)
                    ·
                      refine ⟨2300841087273297801392851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067788116364397068523801 2300841087273297801392851)
                      ·
                        rfl

theorem cell23_4480872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_4480872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480872 prefixEnd_4480872 := by exact prefixLift 4480872
  have htrace : WordTrace (prefixWord ++ tailWord_4480872) baseStart_4480872 baseEnd_4480872 := by
    simpa [prefixWord, tailWord_4480872, baseEnd_4480872] using wordTrace_append hprefix tailTrace_4480872
  have hstable : (prefixWord ++ tailWord_4480872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480872).length < 2 ^ (prefixWord ++ tailWord_4480872).sum := by decide
  have hdescent : baseEnd_4480872 < baseStart_4480872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480885 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_4480885 : Nat := 118140960795 + 4480885 * 2 ^ 59
def prefixEnd_4480885 : Nat := 4983230072969 + 3 ^ 40 * 4480885 * 2
def baseEnd_4480885 : Nat := 2300847762521806250530291

theorem tailTrace_4480885 : CollatzResearch.WordTrace tailWord_4480885 prefixEnd_4480885 2300847762521806250530291 := by
  unfold tailWord_4480885
  simp only [CollatzResearch.WordTrace]
  refine ⟨163431302371526394076516109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108954201581017596051010739 163431302371526394076516109)
  ·
    refine ⟨61286738389322397778693541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163431302371526394076516109 61286738389322397778693541)
    ·
      refine ⟨11491263447997949583505039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61286738389322397778693541 11491263447997949583505039)
      ·
        refine ⟨17236895171996924375257559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11491263447997949583505039 17236895171996924375257559)
        ·
          refine ⟨25855342757995386562886339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17236895171996924375257559 25855342757995386562886339)
          ·
            refine ⟨38783014136993079844329509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25855342757995386562886339 38783014136993079844329509)
            ·
              refine ⟨7271815150686202470811783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38783014136993079844329509 7271815150686202470811783)
              ·
                refine ⟨10907722726029303706217675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7271815150686202470811783 10907722726029303706217675)
                ·
                  refine ⟨16361584089043955559326513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10907722726029303706217675 16361584089043955559326513)
                  ·
                    refine ⟨12271188066782966669494885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16361584089043955559326513 12271188066782966669494885)
                    ·
                      refine ⟨2300847762521806250530291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12271188066782966669494885 2300847762521806250530291)
                      ·
                        rfl

theorem cell23_4480885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_4480885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480885 prefixEnd_4480885 := by exact prefixLift 4480885
  have htrace : WordTrace (prefixWord ++ tailWord_4480885) baseStart_4480885 baseEnd_4480885 := by
    simpa [prefixWord, tailWord_4480885, baseEnd_4480885] using wordTrace_append hprefix tailTrace_4480885
  have hstable : (prefixWord ++ tailWord_4480885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480885).length < 2 ^ (prefixWord ++ tailWord_4480885).sum := by decide
  have hdescent : baseEnd_4480885 < baseStart_4480885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480891 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 4, 7]
def baseStart_4480891 : Nat := 118140960795 + 4480891 * 2 ^ 59
def prefixEnd_4480891 : Nat := 4983230072969 + 3 ^ 40 * 4480891 * 2
def baseEnd_4480891 : Nat := 766950281135244409018421

theorem tailTrace_4480891 : CollatzResearch.WordTrace tailWord_4480891 prefixEnd_4480891 766950281135244409018421 := by
  unfold tailWord_4480891
  simp only [CollatzResearch.WordTrace]
  refine ⟨163431521209504657101234527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108954347473003104734156351 163431521209504657101234527)
  ·
    refine ⟨245147281814256985651851791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163431521209504657101234527 245147281814256985651851791)
    ·
      refine ⟨367720922721385478477777687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245147281814256985651851791 367720922721385478477777687)
      ·
        refine ⟨551581384082078217716666531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367720922721385478477777687 551581384082078217716666531)
        ·
          refine ⟨827372076123117326574999797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551581384082078217716666531 827372076123117326574999797)
          ·
            refine ⟨77566132136542249366406231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 827372076123117326574999797 77566132136542249366406231)
            ·
              refine ⟨116349198204813374049609347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77566132136542249366406231 116349198204813374049609347)
              ·
                refine ⟨174523797307220061074414021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116349198204813374049609347 174523797307220061074414021)
                ·
                  refine ⟨32723211995103761451452629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174523797307220061074414021 32723211995103761451452629)
                  ·
                    refine ⟨766950281135244409018421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32723211995103761451452629 766950281135244409018421)
                    ·
                      rfl

theorem cell23_4480891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 7].length) (baseStart_4480891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480891 prefixEnd_4480891 := by exact prefixLift 4480891
  have htrace : WordTrace (prefixWord ++ tailWord_4480891) baseStart_4480891 baseEnd_4480891 := by
    simpa [prefixWord, tailWord_4480891, baseEnd_4480891] using wordTrace_append hprefix tailTrace_4480891
  have hstable : (prefixWord ++ tailWord_4480891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480891).length < 2 ^ (prefixWord ++ tailWord_4480891).sum := by decide
  have hdescent : baseEnd_4480891 < baseStart_4480891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480905 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 3]
def baseStart_4480905 : Nat := 118140960795 + 4480905 * 2 ^ 59
def prefixEnd_4480905 : Nat := 4983230072969 + 3 ^ 40 * 4480905 * 2
def baseEnd_4480905 : Nat := 2300858032134896172280199

theorem tailTrace_4480905 : CollatzResearch.WordTrace tailWord_4480905 prefixEnd_4480905 2300858032134896172280199 := by
  unfold tailWord_4480905
  simp only [CollatzResearch.WordTrace]
  refine ⟨163432031831453937492244169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108954687887635958328162779 163432031831453937492244169)
  ·
    refine ⟨122574023873590453119183127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163432031831453937492244169 122574023873590453119183127)
    ·
      refine ⟨183861035810385679678774691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122574023873590453119183127 183861035810385679678774691)
      ·
        refine ⟨275791553715578519518162037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183861035810385679678774691 275791553715578519518162037)
        ·
          refine ⟨25855458160835486204827691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 275791553715578519518162037 25855458160835486204827691)
          ·
            refine ⟨38783187241253229307241537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25855458160835486204827691 38783187241253229307241537)
            ·
              refine ⟨29087390430939921980431153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38783187241253229307241537 29087390430939921980431153)
              ·
                refine ⟨21815542823204941485323365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29087390430939921980431153 21815542823204941485323365)
                ·
                  refine ⟨4090414279350926528498131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21815542823204941485323365 4090414279350926528498131)
                  ·
                    refine ⟨6135621419026389792747197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4090414279350926528498131 6135621419026389792747197)
                    ·
                      refine ⟨2300858032134896172280199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135621419026389792747197 2300858032134896172280199)
                      ·
                        rfl

theorem cell23_4480905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 1, 3].length) (baseStart_4480905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480905 prefixEnd_4480905 := by exact prefixLift 4480905
  have htrace : WordTrace (prefixWord ++ tailWord_4480905) baseStart_4480905 baseEnd_4480905 := by
    simpa [prefixWord, tailWord_4480905, baseEnd_4480905] using wordTrace_append hprefix tailTrace_4480905
  have hstable : (prefixWord ++ tailWord_4480905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480905).length < 2 ^ (prefixWord ++ tailWord_4480905).sum := by decide
  have hdescent : baseEnd_4480905 < baseStart_4480905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480906 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_4480906 : Nat := 118140960795 + 4480906 * 2 ^ 59
def prefixEnd_4480906 : Nat := 4983230072969 + 3 ^ 40 * 4480906 * 2
def baseEnd_4480906 : Nat := 2300858545615550668367695

theorem tailTrace_4480906 : CollatzResearch.WordTrace tailWord_4480906 prefixEnd_4480906 2300858545615550668367695 := by
  unfold tailWord_4480906
  simp only [CollatzResearch.WordTrace]
  refine ⟨40858017076112578665757643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108954712202966876442020381 40858017076112578665757643)
  ·
    refine ⟨61287025614168867998636465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40858017076112578665757643 61287025614168867998636465)
    ·
      refine ⟨45965269210626650998977349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61287025614168867998636465 45965269210626650998977349)
      ·
        refine ⟨8618487976992497062308253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45965269210626650998977349 8618487976992497062308253)
        ·
          refine ⟨3231932991372186398365595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8618487976992497062308253 3231932991372186398365595)
          ·
            refine ⟨4847899487058279597548393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231932991372186398365595 4847899487058279597548393)
            ·
              refine ⟨3635924615293709698161295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4847899487058279597548393 3635924615293709698161295)
              ·
                refine ⟨5453886922940564547241943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635924615293709698161295 5453886922940564547241943)
                ·
                  refine ⟨8180830384410846820862915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5453886922940564547241943 8180830384410846820862915)
                  ·
                    refine ⟨12271245576616270231294373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8180830384410846820862915 12271245576616270231294373)
                    ·
                      refine ⟨2300858545615550668367695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12271245576616270231294373 2300858545615550668367695)
                      ·
                        rfl

theorem cell23_4480906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_4480906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480906 prefixEnd_4480906 := by exact prefixLift 4480906
  have htrace : WordTrace (prefixWord ++ tailWord_4480906) baseStart_4480906 baseEnd_4480906 := by
    simpa [prefixWord, tailWord_4480906, baseEnd_4480906] using wordTrace_append hprefix tailTrace_4480906
  have hstable : (prefixWord ++ tailWord_4480906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480906).length < 2 ^ (prefixWord ++ tailWord_4480906).sum := by decide
  have hdescent : baseEnd_4480906 < baseStart_4480906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480922 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_4480922 : Nat := 118140960795 + 4480922 * 2 ^ 59
def prefixEnd_4480922 : Nat := 4983230072969 + 3 ^ 40 * 4480922 * 2
def baseEnd_4480922 : Nat := 2300866761306022605767621

theorem tailTrace_4480922 : CollatzResearch.WordTrace tailWord_4480922 prefixEnd_4480922 2300866761306022605767621 := by
  unfold tailWord_4480922
  simp only [CollatzResearch.WordTrace]
  refine ⟨40858162968098087348903255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108955101248261566263742013 40858162968098087348903255)
  ·
    refine ⟨61287244452147131023354883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40858162968098087348903255 61287244452147131023354883)
    ·
      refine ⟨91930866678220696535032325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61287244452147131023354883 91930866678220696535032325)
      ·
        refine ⟨17237037502166380600318561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91930866678220696535032325 17237037502166380600318561)
        ·
          refine ⟨12927778126624785450238921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17237037502166380600318561 12927778126624785450238921)
          ·
            refine ⟨9695833594968589087679191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12927778126624785450238921 9695833594968589087679191)
            ·
              refine ⟨14543750392452883631518787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9695833594968589087679191 14543750392452883631518787)
              ·
                refine ⟨21815625588679325447278181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14543750392452883631518787 21815625588679325447278181)
                ·
                  refine ⟨4090429797877373521364659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21815625588679325447278181 4090429797877373521364659)
                  ·
                    refine ⟨6135644696816060282046989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4090429797877373521364659 6135644696816060282046989)
                    ·
                      refine ⟨2300866761306022605767621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135644696816060282046989 2300866761306022605767621)
                      ·
                        rfl

theorem cell23_4480922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_4480922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480922 prefixEnd_4480922 := by exact prefixLift 4480922
  have htrace : WordTrace (prefixWord ++ tailWord_4480922) baseStart_4480922 baseEnd_4480922 := by
    simpa [prefixWord, tailWord_4480922, baseEnd_4480922] using wordTrace_append hprefix tailTrace_4480922
  have hstable : (prefixWord ++ tailWord_4480922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480922).length < 2 ^ (prefixWord ++ tailWord_4480922).sum := by decide
  have hdescent : baseEnd_4480922 < baseStart_4480922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480936 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4480936 : Nat := 118140960795 + 4480936 * 2 ^ 59
def prefixEnd_4480936 : Nat := 4983230072969 + 3 ^ 40 * 4480936 * 2
def baseEnd_4480936 : Nat := 2300873950035185550992557

theorem tailTrace_4480936 : CollatzResearch.WordTrace tailWord_4480936 prefixEnd_4480936 2300873950035185550992557 := by
  unfold tailWord_4480936
  simp only [CollatzResearch.WordTrace]
  refine ⟨81716581247170814893311331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108955441662894419857748441 81716581247170814893311331)
  ·
    refine ⟨122574871870756222339966997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81716581247170814893311331 122574871870756222339966997)
    ·
      refine ⟨5745697118941697922185953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122574871870756222339966997 5745697118941697922185953)
      ·
        refine ⟨4309272839206273441639465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5745697118941697922185953 4309272839206273441639465)
        ·
          refine ⟨3231954629404705081229599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4309272839206273441639465 3231954629404705081229599)
          ·
            refine ⟨4847931944107057621844399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231954629404705081229599 4847931944107057621844399)
            ·
              refine ⟨7271897916160586432766599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847931944107057621844399 7271897916160586432766599)
              ·
                refine ⟨10907846874240879649149899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7271897916160586432766599 10907846874240879649149899)
                ·
                  refine ⟨16361770311361319473724849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10907846874240879649149899 16361770311361319473724849)
                  ·
                    refine ⟨12271327733520989605293637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16361770311361319473724849 12271327733520989605293637)
                    ·
                      refine ⟨2300873950035185550992557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12271327733520989605293637 2300873950035185550992557)
                      ·
                        rfl

theorem cell23_4480936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4480936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480936 prefixEnd_4480936 := by exact prefixLift 4480936
  have htrace : WordTrace (prefixWord ++ tailWord_4480936) baseStart_4480936 baseEnd_4480936 := by
    simpa [prefixWord, tailWord_4480936, baseEnd_4480936] using wordTrace_append hprefix tailTrace_4480936
  have hstable : (prefixWord ++ tailWord_4480936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480936).length < 2 ^ (prefixWord ++ tailWord_4480936).sum := by decide
  have hdescent : baseEnd_4480936 < baseStart_4480936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4480949 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_4480949 : Nat := 118140960795 + 4480949 * 2 ^ 59
def prefixEnd_4480949 : Nat := 4983230072969 + 3 ^ 40 * 4480949 * 2
def baseEnd_4480949 : Nat := 2300880625283694000129997

theorem tailTrace_4480949 : CollatzResearch.WordTrace tailWord_4480949 prefixEnd_4480949 2300880625283694000129997 := by
  unfold tailWord_4480949
  simp only [CollatzResearch.WordTrace]
  refine ⟨163433636643294533006845901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108955757762196355337897267 163433636643294533006845901)
  ·
    refine ⟨61287613741235449877567213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163433636643294533006845901 61287613741235449877567213)
    ·
      refine ⟨22982855152963293704087705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61287613741235449877567213 22982855152963293704087705)
      ·
        refine ⟨17237141364722470278065779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22982855152963293704087705 17237141364722470278065779)
        ·
          refine ⟨25855712047083705417098669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17237141364722470278065779 25855712047083705417098669)
          ·
            refine ⟨9695892017656389531412001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25855712047083705417098669 9695892017656389531412001)
            ·
              refine ⟨7271919013242292148559001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9695892017656389531412001 7271919013242292148559001)
              ·
                refine ⟨5453939259931719111419251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7271919013242292148559001 5453939259931719111419251)
                ·
                  refine ⟨8180908889897578667128877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5453939259931719111419251 8180908889897578667128877)
                  ·
                    refine ⟨3067840833711592000173329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8180908889897578667128877 3067840833711592000173329)
                    ·
                      refine ⟨2300880625283694000129997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067840833711592000173329 2300880625283694000129997)
                      ·
                        rfl

theorem cell23_4480949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_4480949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4480949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4480949 prefixEnd_4480949 := by exact prefixLift 4480949
  have htrace : WordTrace (prefixWord ++ tailWord_4480949) baseStart_4480949 baseEnd_4480949 := by
    simpa [prefixWord, tailWord_4480949, baseEnd_4480949] using wordTrace_append hprefix tailTrace_4480949
  have hstable : (prefixWord ++ tailWord_4480949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4480949).length < 2 ^ (prefixWord ++ tailWord_4480949).sum := by decide
  have hdescent : baseEnd_4480949 < baseStart_4480949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4480949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481035 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 4]
def baseStart_4481035 : Nat := 118140960795 + 4481035 * 2 ^ 59
def prefixEnd_4481035 : Nat := 4983230072969 + 3 ^ 40 * 4481035 * 2
def baseEnd_4481035 : Nat := 2300924784619980663654601

theorem tailTrace_4481035 : CollatzResearch.WordTrace tailWord_4481035 prefixEnd_4481035 2300924784619980663654601 := by
  unfold tailWord_4481035
  simp only [CollatzResearch.WordTrace]
  refine ⟨163436773320982969694476559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108957848880655313129651039 163436773320982969694476559)
  ·
    refine ⟨245155159981474454541714839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163436773320982969694476559 245155159981474454541714839)
    ·
      refine ⟨367732739972211681812572259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245155159981474454541714839 367732739972211681812572259)
      ·
        refine ⟨551599109958317522718858389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367732739972211681812572259 551599109958317522718858389)
        ·
          refine ⟨25856208279296133877446487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 551599109958317522718858389 25856208279296133877446487)
          ·
            refine ⟨38784312418944200816169731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25856208279296133877446487 38784312418944200816169731)
            ·
              refine ⟨58176468628416301224254597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38784312418944200816169731 58176468628416301224254597)
              ·
                refine ⟨10908087867828056479547737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58176468628416301224254597 10908087867828056479547737)
                ·
                  refine ⟨8181065900871042359660803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10908087867828056479547737 8181065900871042359660803)
                  ·
                    refine ⟨12271598851306563539491205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8181065900871042359660803 12271598851306563539491205)
                    ·
                      refine ⟨2300924784619980663654601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12271598851306563539491205 2300924784619980663654601)
                      ·
                        rfl

theorem cell23_4481035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 4].length) (baseStart_4481035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481035 prefixEnd_4481035 := by exact prefixLift 4481035
  have htrace : WordTrace (prefixWord ++ tailWord_4481035) baseStart_4481035 baseEnd_4481035 := by
    simpa [prefixWord, tailWord_4481035, baseEnd_4481035] using wordTrace_append hprefix tailTrace_4481035
  have hstable : (prefixWord ++ tailWord_4481035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481035).length < 2 ^ (prefixWord ++ tailWord_4481035).sum := by decide
  have hdescent : baseEnd_4481035 < baseStart_4481035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481052 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_4481052 : Nat := 118140960795 + 4481052 * 2 ^ 59
def prefixEnd_4481052 : Nat := 4983230072969 + 3 ^ 40 * 4481052 * 2
def baseEnd_4481052 : Nat := 2300933513791107097142023

theorem tailTrace_4481052 : CollatzResearch.WordTrace tailWord_4481052 prefixEnd_4481052 2300933513791107097142023 := by
  unfold tailWord_4481052
  simp only [CollatzResearch.WordTrace]
  refine ⟨81718696680960690798922705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108958262241280921065230273 81718696680960690798922705)
  ·
    refine ⟨61289022510720518099192029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81718696680960690798922705 61289022510720518099192029)
    ·
      refine ⟨22983383441520194287197011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61289022510720518099192029 22983383441520194287197011)
      ·
        refine ⟨34475075162280291430795517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22983383441520194287197011 34475075162280291430795517)
        ·
          refine ⟨12928153185855109286548319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34475075162280291430795517 12928153185855109286548319)
          ·
            refine ⟨19392229778782663929822479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12928153185855109286548319 19392229778782663929822479)
            ·
              refine ⟨29088344668173995894733719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19392229778782663929822479 29088344668173995894733719)
              ·
                refine ⟨43632517002260993842100579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29088344668173995894733719 43632517002260993842100579)
                ·
                  refine ⟨65448775503391490763150869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43632517002260993842100579 65448775503391490763150869)
                  ·
                    refine ⟨3067911351721476129522697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65448775503391490763150869 3067911351721476129522697)
                    ·
                      refine ⟨2300933513791107097142023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067911351721476129522697 2300933513791107097142023)
                      ·
                        rfl

theorem cell23_4481052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_4481052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481052 prefixEnd_4481052 := by exact prefixLift 4481052
  have htrace : WordTrace (prefixWord ++ tailWord_4481052) baseStart_4481052 baseEnd_4481052 := by
    simpa [prefixWord, tailWord_4481052, baseEnd_4481052] using wordTrace_append hprefix tailTrace_4481052
  have hstable : (prefixWord ++ tailWord_4481052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481052).length < 2 ^ (prefixWord ++ tailWord_4481052).sum := by decide
  have hdescent : baseEnd_4481052 < baseStart_4481052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481055 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 3]
def baseStart_4481055 : Nat := 118140960795 + 4481055 * 2 ^ 59
def prefixEnd_4481055 : Nat := 4983230072969 + 3 ^ 40 * 4481055 * 2
def baseEnd_4481055 : Nat := 2300935054233070585404509

theorem tailTrace_4481055 : CollatzResearch.WordTrace tailWord_4481055 prefixEnd_4481055 2300935054233070585404509 := by
  unfold tailWord_4481055
  simp only [CollatzResearch.WordTrace]
  refine ⟨163437502780910513110204619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108958335187273675406803079 163437502780910513110204619)
  ·
    refine ⟨245156254171365769665306929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163437502780910513110204619 245156254171365769665306929)
    ·
      refine ⟨183867190628524327248980197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245156254171365769665306929 183867190628524327248980197)
      ·
        refine ⟨34475098242848311359183787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183867190628524327248980197 34475098242848311359183787)
        ·
          refine ⟨51712647364272467038775681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34475098242848311359183787 51712647364272467038775681)
          ·
            refine ⟨38784485523204350279081761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51712647364272467038775681 38784485523204350279081761)
            ·
              refine ⟨29088364142403262709311321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38784485523204350279081761 29088364142403262709311321)
              ·
                refine ⟨21816273106802447031983491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29088364142403262709311321 21816273106802447031983491)
                ·
                  refine ⟨32724409660203670547975237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21816273106802447031983491 32724409660203670547975237)
                  ·
                    refine ⟨6135826811288188227745357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32724409660203670547975237 6135826811288188227745357)
                    ·
                      refine ⟨2300935054233070585404509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135826811288188227745357 2300935054233070585404509)
                      ·
                        rfl

theorem cell23_4481055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_4481055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481055 prefixEnd_4481055 := by exact prefixLift 4481055
  have htrace : WordTrace (prefixWord ++ tailWord_4481055) baseStart_4481055 baseEnd_4481055 := by
    simpa [prefixWord, tailWord_4481055, baseEnd_4481055] using wordTrace_append hprefix tailTrace_4481055
  have hstable : (prefixWord ++ tailWord_4481055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481055).length < 2 ^ (prefixWord ++ tailWord_4481055).sum := by decide
  have hdescent : baseEnd_4481055 < baseStart_4481055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481072 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 3]
def baseStart_4481072 : Nat := 118140960795 + 4481072 * 2 ^ 59
def prefixEnd_4481072 : Nat := 4983230072969 + 3 ^ 40 * 4481072 * 2
def baseEnd_4481072 : Nat := 2300943783404197018891931

theorem tailTrace_4481072 : CollatzResearch.WordTrace tailWord_4481072 prefixEnd_4481072 2300943783404197018891931 := by
  unfold tailWord_4481072
  simp only [CollatzResearch.WordTrace]
  refine ⟨81719061410924462506786735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108958748547899283342382313 81719061410924462506786735)
  ·
    refine ⟨122578592116386693760180103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81719061410924462506786735 122578592116386693760180103)
    ·
      refine ⟨183867888174580040640270155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122578592116386693760180103 183867888174580040640270155)
      ·
        refine ⟨275801832261870060960405233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183867888174580040640270155 275801832261870060960405233)
        ·
          refine ⟨206851374196402545720303925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275801832261870060960405233 206851374196402545720303925)
          ·
            refine ⟨19392316330912738661278493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206851374196402545720303925 19392316330912738661278493)
            ·
              refine ⟨7272118624092276997979435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19392316330912738661278493 7272118624092276997979435)
              ·
                refine ⟨10908177936138415496969153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7272118624092276997979435 10908177936138415496969153)
                ·
                  refine ⟨8181133452103811622726865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10908177936138415496969153 8181133452103811622726865)
                  ·
                    refine ⟨6135850089077858717045149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8181133452103811622726865 6135850089077858717045149)
                    ·
                      refine ⟨2300943783404197018891931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135850089077858717045149 2300943783404197018891931)
                      ·
                        rfl

theorem cell23_4481072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 3].length) (baseStart_4481072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481072 prefixEnd_4481072 := by exact prefixLift 4481072
  have htrace : WordTrace (prefixWord ++ tailWord_4481072) baseStart_4481072 baseEnd_4481072 := by
    simpa [prefixWord, tailWord_4481072, baseEnd_4481072] using wordTrace_append hprefix tailTrace_4481072
  have hstable : (prefixWord ++ tailWord_4481072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481072).length < 2 ^ (prefixWord ++ tailWord_4481072).sum := by decide
  have hdescent : baseEnd_4481072 < baseStart_4481072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481112 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 1, 5, 2]
def baseStart_4481112 : Nat := 118140960795 + 4481112 * 2 ^ 59
def prefixEnd_4481112 : Nat := 4983230072969 + 3 ^ 40 * 4481112 * 2
def baseEnd_4481112 : Nat := 2300964322630376862391747

theorem tailTrace_4481112 : CollatzResearch.WordTrace tailWord_4481112 prefixEnd_4481112 2300964322630376862391747 := by
  unfold tailWord_4481112
  simp only [CollatzResearch.WordTrace]
  refine ⟨81719790870852005922514795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108959721161136007896686393 81719790870852005922514795)
  ·
    refine ⟨122579686306278008883772193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81719790870852005922514795 122579686306278008883772193)
    ·
      refine ⟨91934764729708506662829145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122579686306278008883772193 91934764729708506662829145)
      ·
        refine ⟨68951073547281379997121859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91934764729708506662829145 68951073547281379997121859)
        ·
          refine ⟨103426610320922069995682789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68951073547281379997121859 103426610320922069995682789)
          ·
            refine ⟨19392489435172888124190523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103426610320922069995682789 19392489435172888124190523)
            ·
              refine ⟨29088734152759332186285785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19392489435172888124190523 29088734152759332186285785)
              ·
                refine ⟨21816550614569499139714339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29088734152759332186285785 21816550614569499139714339)
                ·
                  refine ⟨32724825921854248709571509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21816550614569499139714339 32724825921854248709571509)
                  ·
                    refine ⟨3067952430173835816522329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32724825921854248709571509 3067952430173835816522329)
                    ·
                      refine ⟨2300964322630376862391747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3067952430173835816522329 2300964322630376862391747)
                      ·
                        rfl

theorem cell23_4481112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_4481112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481112 prefixEnd_4481112 := by exact prefixLift 4481112
  have htrace : WordTrace (prefixWord ++ tailWord_4481112) baseStart_4481112 baseEnd_4481112 := by
    simpa [prefixWord, tailWord_4481112, baseEnd_4481112] using wordTrace_append hprefix tailTrace_4481112
  have hstable : (prefixWord ++ tailWord_4481112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481112).length < 2 ^ (prefixWord ++ tailWord_4481112).sum := by decide
  have hdescent : baseEnd_4481112 < baseStart_4481112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481136 : List Nat := [2, 1, 1, 1, 5, 2, 3, 3, 1, 1, 3]
def baseStart_4481136 : Nat := 118140960795 + 4481136 * 2 ^ 59
def prefixEnd_4481136 : Nat := 4983230072969 + 3 ^ 40 * 4481136 * 2
def baseEnd_4481136 : Nat := 2300976646166084768491637

theorem tailTrace_4481136 : CollatzResearch.WordTrace tailWord_4481136 prefixEnd_4481136 2300976646166084768491637 := by
  unfold tailWord_4481136
  simp only [CollatzResearch.WordTrace]
  refine ⟨81720228546808531971951631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108960304729078042629268841 81720228546808531971951631)
  ·
    refine ⟨122580342820212797957927447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81720228546808531971951631 122580342820212797957927447)
    ·
      refine ⟨183870514230319196936891171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122580342820212797957927447 183870514230319196936891171)
      ·
        refine ⟨275805771345478795405336757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183870514230319196936891171 275805771345478795405336757)
        ·
          refine ⟨25856791063638637069250321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 275805771345478795405336757 25856791063638637069250321)
          ·
            refine ⟨19392593297728977801937741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25856791063638637069250321 19392593297728977801937741)
            ·
              refine ⟨7272222486648366675726653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19392593297728977801937741 7272222486648366675726653)
              ·
                refine ⟨2727083432493137503397495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7272222486648366675726653 2727083432493137503397495)
                ·
                  refine ⟨4090625148739706255096243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727083432493137503397495 4090625148739706255096243)
                  ·
                    refine ⟨6135937723109559382644365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4090625148739706255096243 6135937723109559382644365)
                    ·
                      refine ⟨2300976646166084768491637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135937723109559382644365 2300976646166084768491637)
                      ·
                        rfl

theorem cell23_4481136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 1, 3].length) (baseStart_4481136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481136 prefixEnd_4481136 := by exact prefixLift 4481136
  have htrace : WordTrace (prefixWord ++ tailWord_4481136) baseStart_4481136 baseEnd_4481136 := by
    simpa [prefixWord, tailWord_4481136, baseEnd_4481136] using wordTrace_append hprefix tailTrace_4481136
  have hstable : (prefixWord ++ tailWord_4481136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481136).length < 2 ^ (prefixWord ++ tailWord_4481136).sum := by decide
  have hdescent : baseEnd_4481136 < baseStart_4481136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481152 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 2, 4]
def baseStart_4481152 : Nat := 118140960795 + 4481152 * 2 ^ 59
def prefixEnd_4481152 : Nat := 4983230072969 + 3 ^ 40 * 4481152 * 2
def baseEnd_4481152 : Nat := 766994953952185568630521

theorem tailTrace_4481152 : CollatzResearch.WordTrace tailWord_4481152 prefixEnd_4481152 766994953952185568630521 := by
  unfold tailWord_4481152
  simp only [CollatzResearch.WordTrace]
  refine ⟨81720520330779549338242855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108960693774372732450990473 81720520330779549338242855)
  ·
    refine ⟨122580780496169324007364283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81720520330779549338242855 122580780496169324007364283)
    ·
      refine ⟨183871170744253986011046425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122580780496169324007364283 183871170744253986011046425)
      ·
        refine ⟨137903378058190489508284819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183871170744253986011046425 137903378058190489508284819)
        ·
          refine ⟨206855067087285734262427229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137903378058190489508284819 206855067087285734262427229)
          ·
            refine ⟨77570650157732150348410211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206855067087285734262427229 77570650157732150348410211)
            ·
              refine ⟨116355975236598225522615317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77570650157732150348410211 116355975236598225522615317)
              ·
                refine ⟨5454186339215541821372593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116355975236598225522615317 5454186339215541821372593)
                ·
                  refine ⟨4090639754411656366029445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5454186339215541821372593 4090639754411656366029445)
                  ·
                    refine ⟨766994953952185568630521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4090639754411656366029445 766994953952185568630521)
                    ·
                      rfl

theorem cell23_4481152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 4].length) (baseStart_4481152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481152 prefixEnd_4481152 := by exact prefixLift 4481152
  have htrace : WordTrace (prefixWord ++ tailWord_4481152) baseStart_4481152 baseEnd_4481152 := by
    simpa [prefixWord, tailWord_4481152, baseEnd_4481152] using wordTrace_append hprefix tailTrace_4481152
  have hstable : (prefixWord ++ tailWord_4481152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481152).length < 2 ^ (prefixWord ++ tailWord_4481152).sum := by decide
  have hdescent : baseEnd_4481152 < baseStart_4481152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481153 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_4481153 : Nat := 118140960795 + 4481153 * 2 ^ 59
def prefixEnd_4481153 : Nat := 4983230072969 + 3 ^ 40 * 4481153 * 2
def baseEnd_4481153 : Nat := 2300985375337211201979059

theorem tailTrace_4481153 : CollatzResearch.WordTrace tailWord_4481153 prefixEnd_4481153 2300985375337211201979059 := by
  unfold tailWord_4481153
  simp only [CollatzResearch.WordTrace]
  refine ⟨163441077134555475847272113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108960718089703650564848075 163441077134555475847272113)
  ·
    refine ⟨122580807850916606885454085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163441077134555475847272113 122580807850916606885454085)
    ·
      refine ⟨22983901472046863791022641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122580807850916606885454085 22983901472046863791022641)
      ·
        refine ⟨17237926104035147843266981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22983901472046863791022641 17237926104035147843266981)
        ·
          refine ⟨3232111144506590220612559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17237926104035147843266981 3232111144506590220612559)
          ·
            refine ⟨4848166716759885330918839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232111144506590220612559 4848166716759885330918839)
            ·
              refine ⟨7272250075139827996378259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4848166716759885330918839 7272250075139827996378259)
              ·
                refine ⟨10908375112709741994567389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7272250075139827996378259 10908375112709741994567389)
                ·
                  refine ⟨4090640667266153247962771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10908375112709741994567389 4090640667266153247962771)
                  ·
                    refine ⟨6135961000899229871944157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4090640667266153247962771 6135961000899229871944157)
                    ·
                      refine ⟨2300985375337211201979059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6135961000899229871944157 2300985375337211201979059)
                      ·
                        rfl

theorem cell23_4481153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_4481153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481153 prefixEnd_4481153 := by exact prefixLift 4481153
  have htrace : WordTrace (prefixWord ++ tailWord_4481153) baseStart_4481153 baseEnd_4481153 := by
    simpa [prefixWord, tailWord_4481153, baseEnd_4481153] using wordTrace_append hprefix tailTrace_4481153
  have hstable : (prefixWord ++ tailWord_4481153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481153).length < 2 ^ (prefixWord ++ tailWord_4481153).sum := by decide
  have hdescent : baseEnd_4481153 < baseStart_4481153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481155 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 6]
def baseStart_4481155 : Nat := 118140960795 + 4481155 * 2 ^ 59
def prefixEnd_4481155 : Nat := 4983230072969 + 3 ^ 40 * 4481155 * 2
def baseEnd_4481155 : Nat := 2300986402298520194154049

theorem tailTrace_4481155 : CollatzResearch.WordTrace tailWord_4481155 prefixEnd_4481155 2300986402298520194154049 := by
  unfold tailWord_4481155
  simp only [CollatzResearch.WordTrace]
  refine ⟨163441150080548230188844919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108960766720365486792563279 163441150080548230188844919)
  ·
    refine ⟨245161725120822345283267379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163441150080548230188844919 245161725120822345283267379)
    ·
      refine ⟨367742587681233517924901069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245161725120822345283267379 367742587681233517924901069)
      ·
        refine ⟨137903470380462569221837901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367742587681233517924901069 137903470380462569221837901)
        ·
          refine ⟨51713801392673463458189213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137903470380462569221837901 51713801392673463458189213)
          ·
            refine ⟨19392675522252548796820955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51713801392673463458189213 19392675522252548796820955)
            ·
              refine ⟨29089013283378823195231433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19392675522252548796820955 29089013283378823195231433)
              ·
                refine ⟨21816759962534117396423575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29089013283378823195231433 21816759962534117396423575)
                ·
                  refine ⟨32725139943801176094635363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21816759962534117396423575 32725139943801176094635363)
                  ·
                    refine ⟨49087709915701764141953045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32725139943801176094635363 49087709915701764141953045)
                    ·
                      refine ⟨2300986402298520194154049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49087709915701764141953045 2300986402298520194154049)
                      ·
                        rfl

theorem cell23_4481155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_4481155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481155 prefixEnd_4481155 := by exact prefixLift 4481155
  have htrace : WordTrace (prefixWord ++ tailWord_4481155) baseStart_4481155 baseEnd_4481155 := by
    simpa [prefixWord, tailWord_4481155, baseEnd_4481155] using wordTrace_append hprefix tailTrace_4481155
  have hstable : (prefixWord ++ tailWord_4481155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481155).length < 2 ^ (prefixWord ++ tailWord_4481155).sum := by decide
  have hdescent : baseEnd_4481155 < baseStart_4481155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481162 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4481162 : Nat := 118140960795 + 4481162 * 2 ^ 59
def prefixEnd_4481162 : Nat := 4983230072969 + 3 ^ 40 * 4481162 * 2
def baseEnd_4481162 : Nat := 2300989996663101666766517

theorem tailTrace_4481162 : CollatzResearch.WordTrace tailWord_4481162 prefixEnd_4481162 2300989996663101666766517 := by
  unfold tailWord_4481162
  simp only [CollatzResearch.WordTrace]
  refine ⟨40860351347880717596087435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108960936927681913589566493 40860351347880717596087435)
  ·
    refine ⟨61290527021821076394131153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40860351347880717596087435 61290527021821076394131153)
    ·
      refine ⟨45967895266365807295598365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61290527021821076394131153 45967895266365807295598365)
      ·
        refine ⟨17237960724887177735849387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45967895266365807295598365 17237960724887177735849387)
        ·
          refine ⟨25856941087330766603774081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17237960724887177735849387 25856941087330766603774081)
          ·
            refine ⟨19392705815498074952830561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25856941087330766603774081 19392705815498074952830561)
            ·
              refine ⟨14544529361623556214622921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19392705815498074952830561 14544529361623556214622921)
              ·
                refine ⟨10908397021217667160967191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14544529361623556214622921 10908397021217667160967191)
                ·
                  refine ⟨16362595531826500741450787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10908397021217667160967191 16362595531826500741450787)
                  ·
                    refine ⟨24543893297739751112176181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16362595531826500741450787 24543893297739751112176181)
                    ·
                      refine ⟨2300989996663101666766517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24543893297739751112176181 2300989996663101666766517)
                      ·
                        rfl

theorem cell23_4481162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4481162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481162 prefixEnd_4481162 := by exact prefixLift 4481162
  have htrace : WordTrace (prefixWord ++ tailWord_4481162) baseStart_4481162 baseEnd_4481162 := by
    simpa [prefixWord, tailWord_4481162, baseEnd_4481162] using wordTrace_append hprefix tailTrace_4481162
  have hstable : (prefixWord ++ tailWord_4481162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481162).length < 2 ^ (prefixWord ++ tailWord_4481162).sum := by decide
  have hdescent : baseEnd_4481162 < baseStart_4481162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481176 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 1, 1, 4]
def baseStart_4481176 : Nat := 118140960795 + 4481176 * 2 ^ 59
def prefixEnd_4481176 : Nat := 4983230072969 + 3 ^ 40 * 4481176 * 2
def baseEnd_4481176 : Nat := 2300997185392264611991453

theorem tailTrace_4481176 : CollatzResearch.WordTrace tailWord_4481176 prefixEnd_4481176 2300997185392264611991453 := by
  unfold tailWord_4481176
  simp only [CollatzResearch.WordTrace]
  refine ⟨81720958006736075387679691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108961277342314767183572921 81720958006736075387679691)
  ·
    refine ⟨122581437010104113081519537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81720958006736075387679691 122581437010104113081519537)
    ·
      refine ⟨91936077757578084811139653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122581437010104113081519537 91936077757578084811139653)
      ·
        refine ⟨17238014579545890902088685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91936077757578084811139653 17238014579545890902088685)
        ·
          refine ⟨6464255467329709088283257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17238014579545890902088685 6464255467329709088283257)
          ·
            refine ⟨4848191600497281816212443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6464255467329709088283257 4848191600497281816212443)
            ·
              refine ⟨7272287400745922724318665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4848191600497281816212443 7272287400745922724318665)
              ·
                refine ⟨5454215550559442043238999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7272287400745922724318665 5454215550559442043238999)
                ·
                  refine ⟨8181323325839163064858499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5454215550559442043238999 8181323325839163064858499)
                  ·
                    refine ⟨12271984988758744597287749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8181323325839163064858499 12271984988758744597287749)
                    ·
                      refine ⟨2300997185392264611991453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12271984988758744597287749 2300997185392264611991453)
                      ·
                        rfl

theorem cell23_4481176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_4481176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481176 prefixEnd_4481176 := by exact prefixLift 4481176
  have htrace : WordTrace (prefixWord ++ tailWord_4481176) baseStart_4481176 baseEnd_4481176 := by
    simpa [prefixWord, tailWord_4481176, baseEnd_4481176] using wordTrace_append hprefix tailTrace_4481176
  have hstable : (prefixWord ++ tailWord_4481176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481176).length < 2 ^ (prefixWord ++ tailWord_4481176).sum := by decide
  have hdescent : baseEnd_4481176 < baseStart_4481176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481249 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_4481249 : Nat := 118140960795 + 4481249 * 2 ^ 59
def prefixEnd_4481249 : Nat := 4983230072969 + 3 ^ 40 * 4481249 * 2
def baseEnd_4481249 : Nat := 2301034669480042826378617

theorem tailTrace_4481249 : CollatzResearch.WordTrace tailWord_4481249 prefixEnd_4481249 2301034669480042826378617 := by
  unfold tailWord_4481249
  simp only [CollatzResearch.WordTrace]
  refine ⟨163444578542207684242766801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108963052361471789495177867 163444578542207684242766801)
  ·
    refine ⟨122583433906655763182075101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163444578542207684242766801 122583433906655763182075101)
    ·
      refine ⟨45968787714995911193278163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122583433906655763182075101 45968787714995911193278163)
      ·
        refine ⟨68953181572493866789917245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45968787714995911193278163 68953181572493866789917245)
        ·
          refine ⟨25857443089685200046218967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68953181572493866789917245 25857443089685200046218967)
          ·
            refine ⟨38786164634527800069328451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25857443089685200046218967 38786164634527800069328451)
            ·
              refine ⟨58179246951791700103992677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38786164634527800069328451 58179246951791700103992677)
              ·
                refine ⟨10908608803460943769498627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58179246951791700103992677 10908608803460943769498627)
                ·
                  refine ⟨16362913205191415654247941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10908608803460943769498627 16362913205191415654247941)
                  ·
                    refine ⟨3068046225973390435171489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16362913205191415654247941 3068046225973390435171489)
                    ·
                      refine ⟨2301034669480042826378617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068046225973390435171489 2301034669480042826378617)
                      ·
                        rfl

theorem cell23_4481249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_4481249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481249 prefixEnd_4481249 := by exact prefixLift 4481249
  have htrace : WordTrace (prefixWord ++ tailWord_4481249) baseStart_4481249 baseEnd_4481249 := by
    simpa [prefixWord, tailWord_4481249, baseEnd_4481249] using wordTrace_append hprefix tailTrace_4481249
  have hstable : (prefixWord ++ tailWord_4481249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481249).length < 2 ^ (prefixWord ++ tailWord_4481249).sum := by decide
  have hdescent : baseEnd_4481249 < baseStart_4481249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481253 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 1, 3, 2]
def baseStart_4481253 : Nat := 118140960795 + 4481253 * 2 ^ 59
def prefixEnd_4481253 : Nat := 4983230072969 + 3 ^ 40 * 4481253 * 2
def baseEnd_4481253 : Nat := 2301036723402660810728599

theorem tailTrace_4481253 : CollatzResearch.WordTrace tailWord_4481253 prefixEnd_4481253 2301036723402660810728599 := by
  unfold tailWord_4481253
  simp only [CollatzResearch.WordTrace]
  refine ⟨163444724434193192925912413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108963149622795461950608275 163444724434193192925912413)
  ·
    refine ⟨61291771662822447347217155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163444724434193192925912413 61291771662822447347217155)
    ·
      refine ⟨91937657494233671020825733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61291771662822447347217155 91937657494233671020825733)
      ·
        refine ⟨17238310780168813316404825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91937657494233671020825733 17238310780168813316404825)
        ·
          refine ⟨12928733085126609987303619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17238310780168813316404825 12928733085126609987303619)
          ·
            refine ⟨19393099627689914980955429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12928733085126609987303619 19393099627689914980955429)
            ·
              refine ⟨3636206180191859058929143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19393099627689914980955429 3636206180191859058929143)
              ·
                refine ⟨5454309270287788588393715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636206180191859058929143 5454309270287788588393715)
                ·
                  refine ⟨8181463905431682882590573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5454309270287788588393715 8181463905431682882590573)
                  ·
                    refine ⟨3068048964536881080971465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8181463905431682882590573 3068048964536881080971465)
                    ·
                      refine ⟨2301036723402660810728599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068048964536881080971465 2301036723402660810728599)
                      ·
                        rfl

theorem cell23_4481253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_4481253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481253 prefixEnd_4481253 := by exact prefixLift 4481253
  have htrace : WordTrace (prefixWord ++ tailWord_4481253) baseStart_4481253 baseEnd_4481253 := by
    simpa [prefixWord, tailWord_4481253, baseEnd_4481253] using wordTrace_append hprefix tailTrace_4481253
  have hstable : (prefixWord ++ tailWord_4481253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481253).length < 2 ^ (prefixWord ++ tailWord_4481253).sum := by decide
  have hdescent : baseEnd_4481253 < baseStart_4481253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481283 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 2, 2, 2]
def baseStart_4481283 : Nat := 118140960795 + 4481283 * 2 ^ 59
def prefixEnd_4481283 : Nat := 4983230072969 + 3 ^ 40 * 4481283 * 2
def baseEnd_4481283 : Nat := 2301052127822295693353461

theorem tailTrace_4481283 : CollatzResearch.WordTrace tailWord_4481283 prefixEnd_4481283 2301052127822295693353461 := by
  unfold tailWord_4481283
  simp only [CollatzResearch.WordTrace]
  refine ⟨163445818624084508049504503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108963879082723005366336335 163445818624084508049504503)
  ·
    refine ⟨245168727936126762074256755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163445818624084508049504503 245168727936126762074256755)
    ·
      refine ⟨367753091904190143111385133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245168727936126762074256755 367753091904190143111385133)
      ·
        refine ⟨137907409464071303666769425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367753091904190143111385133 137907409464071303666769425)
        ·
          refine ⟨103430557098053477750077069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137907409464071303666769425 103430557098053477750077069)
          ·
            refine ⟨38786458911770054156278901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103430557098053477750077069 38786458911770054156278901)
            ·
              refine ⟨3636230522978442577151147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38786458911770054156278901 3636230522978442577151147)
              ·
                refine ⟨5454345784467663865726721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636230522978442577151147 5454345784467663865726721)
                ·
                  refine ⟨4090759338350747899295041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5454345784467663865726721 4090759338350747899295041)
                  ·
                    refine ⟨3068069503763060924471281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4090759338350747899295041 3068069503763060924471281)
                    ·
                      refine ⟨2301052127822295693353461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068069503763060924471281 2301052127822295693353461)
                      ·
                        rfl

theorem cell23_4481283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_4481283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481283 prefixEnd_4481283 := by exact prefixLift 4481283
  have htrace : WordTrace (prefixWord ++ tailWord_4481283) baseStart_4481283 baseEnd_4481283 := by
    simpa [prefixWord, tailWord_4481283, baseEnd_4481283] using wordTrace_append hprefix tailTrace_4481283
  have hstable : (prefixWord ++ tailWord_4481283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481283).length < 2 ^ (prefixWord ++ tailWord_4481283).sum := by decide
  have hdescent : baseEnd_4481283 < baseStart_4481283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481329 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_4481329 : Nat := 118140960795 + 4481329 * 2 ^ 59
def prefixEnd_4481329 : Nat := 4983230072969 + 3 ^ 40 * 4481329 * 2
def baseEnd_4481329 : Nat := 2301075747932402513378249

theorem tailTrace_4481329 : CollatzResearch.WordTrace tailWord_4481329 prefixEnd_4481329 2301075747932402513378249 := by
  unfold tailWord_4481329
  simp only [CollatzResearch.WordTrace]
  refine ⟨163447496381917857905679041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108964997587945238603786027 163447496381917857905679041)
  ·
    refine ⟨122585622286438393429259281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163447496381917857905679041 122585622286438393429259281)
    ·
      refine ⟨91939216714828795071944461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122585622286438393429259281 91939216714828795071944461)
      ·
        refine ⟨34477206268060798151979173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91939216714828795071944461 34477206268060798151979173)
        ·
          refine ⟨6464476175261399653496095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34477206268060798151979173 6464476175261399653496095)
          ·
            refine ⟨9696714262892099480244143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6464476175261399653496095 9696714262892099480244143)
            ·
              refine ⟨14545071394338149220366215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9696714262892099480244143 14545071394338149220366215)
              ·
                refine ⟨21817607091507223830549323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14545071394338149220366215 21817607091507223830549323)
                ·
                  refine ⟨32726410637260835745823985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21817607091507223830549323 32726410637260835745823985)
                  ·
                    refine ⟨24544807977945626809367989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32726410637260835745823985 24544807977945626809367989)
                    ·
                      refine ⟨2301075747932402513378249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24544807977945626809367989 2301075747932402513378249)
                      ·
                        rfl

theorem cell23_4481329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_4481329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481329 prefixEnd_4481329 := by exact prefixLift 4481329
  have htrace : WordTrace (prefixWord ++ tailWord_4481329) baseStart_4481329 baseEnd_4481329 := by
    simpa [prefixWord, tailWord_4481329, baseEnd_4481329] using wordTrace_append hprefix tailTrace_4481329
  have hstable : (prefixWord ++ tailWord_4481329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481329).length < 2 ^ (prefixWord ++ tailWord_4481329).sum := by decide
  have hdescent : baseEnd_4481329 < baseStart_4481329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481352 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_4481352 : Nat := 118140960795 + 4481352 * 2 ^ 59
def prefixEnd_4481352 : Nat := 4983230072969 + 3 ^ 40 * 4481352 * 2
def baseEnd_4481352 : Nat := 2301087557987455923390643

theorem tailTrace_4481352 : CollatzResearch.WordTrace tailWord_4481352 prefixEnd_4481352 2301087557987455923390643 := by
  unfold tailWord_4481352
  simp only [CollatzResearch.WordTrace]
  refine ⟨81724167630417266416883155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108965556840556355222510873 81724167630417266416883155)
  ·
    refine ⟨122586251445625899625324733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81724167630417266416883155 122586251445625899625324733)
    ·
      refine ⟨45969844292109712359496775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122586251445625899625324733 45969844292109712359496775)
      ·
        refine ⟨68954766438164568539245163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45969844292109712359496775 68954766438164568539245163)
        ·
          refine ⟨103432149657246852808867745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68954766438164568539245163 103432149657246852808867745)
          ·
            refine ⟨77574112242935139606650809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103432149657246852808867745 77574112242935139606650809)
            ·
              refine ⟨58180584182201354704988107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77574112242935139606650809 58180584182201354704988107)
              ·
                refine ⟨87270876273302032057482161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58180584182201354704988107 87270876273302032057482161)
                ·
                  refine ⟨65453157204976524043111621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87270876273302032057482161 65453157204976524043111621)
                  ·
                    refine ⟨12272466975933098258083429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65453157204976524043111621 12272466975933098258083429)
                    ·
                      refine ⟨2301087557987455923390643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12272466975933098258083429 2301087557987455923390643)
                      ·
                        rfl

theorem cell23_4481352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_4481352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481352 prefixEnd_4481352 := by exact prefixLift 4481352
  have htrace : WordTrace (prefixWord ++ tailWord_4481352) baseStart_4481352 baseEnd_4481352 := by
    simpa [prefixWord, tailWord_4481352, baseEnd_4481352] using wordTrace_append hprefix tailTrace_4481352
  have hstable : (prefixWord ++ tailWord_4481352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481352).length < 2 ^ (prefixWord ++ tailWord_4481352).sum := by decide
  have hdescent : baseEnd_4481352 < baseStart_4481352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481362 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 10]
def baseStart_4481362 : Nat := 118140960795 + 4481362 * 2 ^ 59
def prefixEnd_4481362 : Nat := 4983230072969 + 3 ^ 40 * 4481362 * 2
def baseEnd_4481362 : Nat := 255676965866000098251733

theorem tailTrace_4481362 : CollatzResearch.WordTrace tailWord_4481362 prefixEnd_4481362 255676965866000098251733 := by
  unfold tailWord_4481362
  simp only [CollatzResearch.WordTrace]
  refine ⟨40862174997699576135407585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108965799993865536361086893 40862174997699576135407585)
  ·
    refine ⟨30646631248274682101555689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40862174997699576135407585 30646631248274682101555689)
    ·
      refine ⟨22984973436206011576166767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30646631248274682101555689 22984973436206011576166767)
      ·
        refine ⟨34477460154309017364250151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22984973436206011576166767 34477460154309017364250151)
        ·
          refine ⟨51716190231463526046375227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34477460154309017364250151 51716190231463526046375227)
          ·
            refine ⟨77574285347195289069562841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51716190231463526046375227 77574285347195289069562841)
            ·
              refine ⟨58180714010396466802172131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77574285347195289069562841 58180714010396466802172131)
              ·
                refine ⟨87271071015594700203258197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58180714010396466802172131 87271071015594700203258197)
                ·
                  refine ⟨255676965866000098251733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 87271071015594700203258197 255676965866000098251733)
                  ·
                    rfl

theorem cell23_4481362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_4481362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481362 prefixEnd_4481362 := by exact prefixLift 4481362
  have htrace : WordTrace (prefixWord ++ tailWord_4481362) baseStart_4481362 baseEnd_4481362 := by
    simpa [prefixWord, tailWord_4481362, baseEnd_4481362] using wordTrace_append hprefix tailTrace_4481362
  have hstable : (prefixWord ++ tailWord_4481362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481362).length < 2 ^ (prefixWord ++ tailWord_4481362).sum := by decide
  have hdescent : baseEnd_4481362 < baseStart_4481362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481379 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 6]
def baseStart_4481379 : Nat := 118140960795 + 4481379 * 2 ^ 59
def prefixEnd_4481379 : Nat := 4983230072969 + 3 ^ 40 * 4481379 * 2
def baseEnd_4481379 : Nat := 255677935773903035305891

theorem tailTrace_4481379 : CollatzResearch.WordTrace tailWord_4481379 prefixEnd_4481379 255677935773903035305891 := by
  unfold tailWord_4481379
  simp only [CollatzResearch.WordTrace]
  refine ⟨163449320031736716444999191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108966213354491144296666127 163449320031736716444999191)
  ·
    refine ⟨245173980047605074667498787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163449320031736716444999191 245173980047605074667498787)
    ·
      refine ⟨367760970071407612001248181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245173980047605074667498787 367760970071407612001248181)
      ·
        refine ⟨34477590944194463625117017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 367760970071407612001248181 34477590944194463625117017)
        ·
          refine ⟨25858193208145847718837763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34477590944194463625117017 25858193208145847718837763)
          ·
            refine ⟨38787289812218771578256645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25858193208145847718837763 38787289812218771578256645)
            ·
              refine ⟨7272616839791019670923121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38787289812218771578256645 7272616839791019670923121)
              ·
                refine ⟨5454462629843264753192341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7272616839791019670923121 5454462629843264753192341)
                ·
                  refine ⟨255677935773903035305891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5454462629843264753192341 255677935773903035305891)
                  ·
                    rfl

theorem cell23_4481379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 6].length) (baseStart_4481379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481379 prefixEnd_4481379 := by exact prefixLift 4481379
  have htrace : WordTrace (prefixWord ++ tailWord_4481379) baseStart_4481379 baseEnd_4481379 := by
    simpa [prefixWord, tailWord_4481379, baseEnd_4481379] using wordTrace_append hprefix tailTrace_4481379
  have hstable : (prefixWord ++ tailWord_4481379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481379).length < 2 ^ (prefixWord ++ tailWord_4481379).sum := by decide
  have hdescent : baseEnd_4481379 < baseStart_4481379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481383 : List Nat := [1, 1, 5, 1, 3, 2, 1, 4, 1, 4]
def baseStart_4481383 : Nat := 118140960795 + 4481383 * 2 ^ 59
def prefixEnd_4481383 : Nat := 4983230072969 + 3 ^ 40 * 4481383 * 2
def baseEnd_4481383 : Nat := 767034491962581767367667

theorem tailTrace_4481383 : CollatzResearch.WordTrace tailWord_4481383 prefixEnd_4481383 767034491962581767367667 := by
  unfold tailWord_4481383
  simp only [CollatzResearch.WordTrace]
  refine ⟨163449465923722225128144803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108966310615814816752096535 163449465923722225128144803)
  ·
    refine ⟨245174198885583337692217205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163449465923722225128144803 245174198885583337692217205)
    ·
      refine ⟨22985081145523437908645363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 245174198885583337692217205 22985081145523437908645363)
      ·
        refine ⟨34477621718285156862968045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22985081145523437908645363 34477621718285156862968045)
        ·
          refine ⟨12929108144356933823613017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34477621718285156862968045 12929108144356933823613017)
          ·
            refine ⟨9696831108267700367709763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12929108144356933823613017 9696831108267700367709763)
            ·
              refine ⟨14545246662401550551564645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9696831108267700367709763 14545246662401550551564645)
              ·
                refine ⟨2727233749200290728418371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14545246662401550551564645 2727233749200290728418371)
                ·
                  refine ⟨4090850623800436092627557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727233749200290728418371 4090850623800436092627557)
                  ·
                    refine ⟨767034491962581767367667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4090850623800436092627557 767034491962581767367667)
                    ·
                      rfl

theorem cell23_4481383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_4481383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481383 prefixEnd_4481383 := by exact prefixLift 4481383
  have htrace : WordTrace (prefixWord ++ tailWord_4481383) baseStart_4481383 baseEnd_4481383 := by
    simpa [prefixWord, tailWord_4481383, baseEnd_4481383] using wordTrace_append hprefix tailTrace_4481383
  have hstable : (prefixWord ++ tailWord_4481383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481383).length < 2 ^ (prefixWord ++ tailWord_4481383).sum := by decide
  have hdescent : baseEnd_4481383 < baseStart_4481383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481416 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_4481416 : Nat := 118140960795 + 4481416 * 2 ^ 59
def prefixEnd_4481416 : Nat := 4983230072969 + 3 ^ 40 * 4481416 * 2
def baseEnd_4481416 : Nat := 2301120420749343672990349

theorem tailTrace_4481416 : CollatzResearch.WordTrace tailWord_4481416 prefixEnd_4481416 2301120420749343672990349 := by
  unfold tailWord_4481416
  simp only [CollatzResearch.WordTrace]
  refine ⟨81725334766301335882048051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108967113021735114509397401 81725334766301335882048051)
  ·
    refine ⟨122588002149452003823072077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81725334766301335882048051 122588002149452003823072077)
    ·
      refine ⟨45970500806044501433652029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122588002149452003823072077 45970500806044501433652029)
      ·
        refine ⟨17238937802266688037619511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45970500806044501433652029 17238937802266688037619511)
        ·
          refine ⟨25858406703400032056429267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17238937802266688037619511 25858406703400032056429267)
          ·
            refine ⟨38787610055100048084643901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25858406703400032056429267 38787610055100048084643901)
            ·
              refine ⟨14545353770662518031741463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38787610055100048084643901 14545353770662518031741463)
              ·
                refine ⟨21818030655993777047612195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14545353770662518031741463 21818030655993777047612195)
                ·
                  refine ⟨32727045983990665571418293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21818030655993777047612195 32727045983990665571418293)
                  ·
                    refine ⟨3068160560999124897320465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32727045983990665571418293 3068160560999124897320465)
                    ·
                      refine ⟨2301120420749343672990349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068160560999124897320465 2301120420749343672990349)
                      ·
                        rfl

theorem cell23_4481416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_4481416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481416 prefixEnd_4481416 := by exact prefixLift 4481416
  have htrace : WordTrace (prefixWord ++ tailWord_4481416) baseStart_4481416 baseEnd_4481416 := by
    simpa [prefixWord, tailWord_4481416, baseEnd_4481416] using wordTrace_append hprefix tailTrace_4481416
  have hstable : (prefixWord ++ tailWord_4481416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481416).length < 2 ^ (prefixWord ++ tailWord_4481416).sum := by decide
  have hdescent : baseEnd_4481416 < baseStart_4481416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481430 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4481430 : Nat := 118140960795 + 4481430 * 2 ^ 59
def prefixEnd_4481430 : Nat := 4983230072969 + 3 ^ 40 * 4481430 * 2
def baseEnd_4481430 : Nat := 255680845497611846468365

theorem tailTrace_4481430 : CollatzResearch.WordTrace tailWord_4481430 prefixEnd_4481430 255680845497611846468365 := by
  unfold tailWord_4481430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10215698759659497009694109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108967453436367968103403829 10215698759659497009694109)
  ·
    refine ⟨3830887034872311378635291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10215698759659497009694109 3830887034872311378635291)
    ·
      refine ⟨5746330552308467067952937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3830887034872311378635291 5746330552308467067952937)
      ·
        refine ⟨4309747914231350300964703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5746330552308467067952937 4309747914231350300964703)
        ·
          refine ⟨6464621871347025451447055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4309747914231350300964703 6464621871347025451447055)
          ·
            refine ⟨9696932807020538177170583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6464621871347025451447055 9696932807020538177170583)
            ·
              refine ⟨14545399210530807265755875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9696932807020538177170583 14545399210530807265755875)
              ·
                refine ⟨21818098815796210898633813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14545399210530807265755875 21818098815796210898633813)
                ·
                  refine ⟨255680845497611846468365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21818098815796210898633813 255680845497611846468365)
                  ·
                    rfl

theorem cell23_4481430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4481430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481430 prefixEnd_4481430 := by exact prefixLift 4481430
  have htrace : WordTrace (prefixWord ++ tailWord_4481430) baseStart_4481430 baseEnd_4481430 := by
    simpa [prefixWord, tailWord_4481430, baseEnd_4481430] using wordTrace_append hprefix tailTrace_4481430
  have hstable : (prefixWord ++ tailWord_4481430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481430).length < 2 ^ (prefixWord ++ tailWord_4481430).sum := by decide
  have hdescent : baseEnd_4481430 < baseStart_4481430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481449 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 3]
def baseStart_4481449 : Nat := 118140960795 + 4481449 * 2 ^ 59
def prefixEnd_4481449 : Nat := 4983230072969 + 3 ^ 40 * 4481449 * 2
def baseEnd_4481449 : Nat := 2301137365610942043877697

theorem tailTrace_4481449 : CollatzResearch.WordTrace tailWord_4481449 prefixEnd_4481449 2301137365610942043877697 := by
  unfold tailWord_4481449
  simp only [CollatzResearch.WordTrace]
  refine ⟨163451873141483118400047401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108967915427655412266698267 163451873141483118400047401)
  ·
    refine ⟨122588904856112338800035551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163451873141483118400047401 122588904856112338800035551)
    ·
      refine ⟨183883357284168508200053327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122588904856112338800035551 183883357284168508200053327)
      ·
        refine ⟨275825035926252762300079991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183883357284168508200053327 275825035926252762300079991)
        ·
          refine ⟨413737553889379143450119987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275825035926252762300079991 413737553889379143450119987)
          ·
            refine ⟨620606330834068715175179981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413737553889379143450119987 620606330834068715175179981)
            ·
              refine ⟨232727374062775768190692493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 620606330834068715175179981 232727374062775768190692493)
              ·
                refine ⟨87272765273540913071509685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232727374062775768190692493 87272765273540913071509685)
                ·
                  refine ⟨8181821744394460600454033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87272765273540913071509685 8181821744394460600454033)
                  ·
                    refine ⟨6136366308295845450340525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8181821744394460600454033 6136366308295845450340525)
                    ·
                      refine ⟨2301137365610942043877697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6136366308295845450340525 2301137365610942043877697)
                      ·
                        rfl

theorem cell23_4481449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_4481449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481449 prefixEnd_4481449 := by exact prefixLift 4481449
  have htrace : WordTrace (prefixWord ++ tailWord_4481449) baseStart_4481449 baseEnd_4481449 := by
    simpa [prefixWord, tailWord_4481449, baseEnd_4481449] using wordTrace_append hprefix tailTrace_4481449
  have hstable : (prefixWord ++ tailWord_4481449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481449).length < 2 ^ (prefixWord ++ tailWord_4481449).sum := by decide
  have hdescent : baseEnd_4481449 < baseStart_4481449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481452 : List Nat := [2, 2, 1, 1, 1, 1, 3, 12]
def baseStart_4481452 : Nat := 118140960795 + 4481452 * 2 ^ 59
def prefixEnd_4481452 : Nat := 4983230072969 + 3 ^ 40 * 4481452 * 2
def baseEnd_4481452 : Nat := 85227366890848353042229

theorem tailTrace_4481452 : CollatzResearch.WordTrace tailWord_4481452 prefixEnd_4481452 85227366890848353042229 := by
  unfold tailWord_4481452
  simp only [CollatzResearch.WordTrace]
  refine ⟨81725991280236124956203305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108967988373648166608271073 81725991280236124956203305)
  ·
    refine ⟨61294493460177093717152479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81725991280236124956203305 61294493460177093717152479)
    ·
      refine ⟨91941740190265640575728719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61294493460177093717152479 91941740190265640575728719)
      ·
        refine ⟨137912610285398460863593079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91941740190265640575728719 137912610285398460863593079)
        ·
          refine ⟨206868915428097691295389619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137912610285398460863593079 206868915428097691295389619)
          ·
            refine ⟨310303373142146536943084429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206868915428097691295389619 310303373142146536943084429)
            ·
              refine ⟨116363764928304951353656661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 310303373142146536943084429 116363764928304951353656661)
              ·
                refine ⟨85227366890848353042229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 116363764928304951353656661 85227366890848353042229)
                ·
                  rfl

theorem cell23_4481452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 12].length) (baseStart_4481452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481452 prefixEnd_4481452 := by exact prefixLift 4481452
  have htrace : WordTrace (prefixWord ++ tailWord_4481452) baseStart_4481452 baseEnd_4481452 := by
    simpa [prefixWord, tailWord_4481452, baseEnd_4481452] using wordTrace_append hprefix tailTrace_4481452
  have hstable : (prefixWord ++ tailWord_4481452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481452).length < 2 ^ (prefixWord ++ tailWord_4481452).sum := by decide
  have hdescent : baseEnd_4481452 < baseStart_4481452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481463 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 3, 2, 2]
def baseStart_4481463 : Nat := 118140960795 + 4481463 * 2 ^ 59
def prefixEnd_4481463 : Nat := 4983230072969 + 3 ^ 40 * 4481463 * 2
def baseEnd_4481463 : Nat := 2301144554340104989102633

theorem tailTrace_4481463 : CollatzResearch.WordTrace tailWord_4481463 prefixEnd_4481463 2301144554340104989102633 := by
  unfold tailWord_4481463
  simp only [CollatzResearch.WordTrace]
  refine ⟨163452383763432398791057043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108968255842288265860704695 163452383763432398791057043)
  ·
    refine ⟨245178575645148598186585565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163452383763432398791057043 245178575645148598186585565)
    ·
      refine ⟨91941965866930724319969587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245178575645148598186585565 91941965866930724319969587)
      ·
        refine ⟨137912948800396086479954381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91941965866930724319969587 137912948800396086479954381)
        ·
          refine ⟨51717355800148532429982893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137912948800396086479954381 51717355800148532429982893)
          ·
            refine ⟨19394008425055699661243585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51717355800148532429982893 19394008425055699661243585)
            ·
              refine ⟨14545506318791774745932689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19394008425055699661243585 14545506318791774745932689)
              ·
                refine ⟨10909129739093831059449517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14545506318791774745932689 10909129739093831059449517)
                ·
                  refine ⟨4090923652160186647293569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10909129739093831059449517 4090923652160186647293569)
                  ·
                    refine ⟨3068192739120139985470177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4090923652160186647293569 3068192739120139985470177)
                    ·
                      refine ⟨2301144554340104989102633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068192739120139985470177 2301144554340104989102633)
                      ·
                        rfl

theorem cell23_4481463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_4481463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481463 prefixEnd_4481463 := by exact prefixLift 4481463
  have htrace : WordTrace (prefixWord ++ tailWord_4481463) baseStart_4481463 baseEnd_4481463 := by
    simpa [prefixWord, tailWord_4481463, baseEnd_4481463] using wordTrace_append hprefix tailTrace_4481463
  have hstable : (prefixWord ++ tailWord_4481463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481463).length < 2 ^ (prefixWord ++ tailWord_4481463).sum := by decide
  have hdescent : baseEnd_4481463 < baseStart_4481463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481469 : List Nat := [1, 4, 1, 2, 2, 3, 1, 9]
def baseStart_4481469 : Nat := 118140960795 + 4481469 * 2 ^ 59
def prefixEnd_4481469 : Nat := 4983230072969 + 3 ^ 40 * 4481469 * 2
def baseEnd_4481469 : Nat := 85227690193482665393615

theorem tailTrace_4481469 : CollatzResearch.WordTrace tailWord_4481469 prefixEnd_4481469 85227690193482665393615 := by
  unfold tailWord_4481469
  simp only [CollatzResearch.WordTrace]
  refine ⟨163452602601410661815775461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108968401734273774543850307 163452602601410661815775461)
  ·
    refine ⟨30647362987764499090457899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163452602601410661815775461 30647362987764499090457899)
    ·
      refine ⟨45971044481646748635686849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30647362987764499090457899 45971044481646748635686849)
      ·
        refine ⟨34478283361235061476765137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45971044481646748635686849 34478283361235061476765137)
        ·
          refine ⟨25858712520926296107573853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34478283361235061476765137 25858712520926296107573853)
          ·
            refine ⟨9697017195347361040340195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25858712520926296107573853 9697017195347361040340195)
            ·
              refine ⟨14545525793021041560510293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9697017195347361040340195 14545525793021041560510293)
              ·
                refine ⟨85227690193482665393615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14545525793021041560510293 85227690193482665393615)
                ·
                  rfl

theorem cell23_4481469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 9].length) (baseStart_4481469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481469 prefixEnd_4481469 := by exact prefixLift 4481469
  have htrace : WordTrace (prefixWord ++ tailWord_4481469) baseStart_4481469 baseEnd_4481469 := by
    simpa [prefixWord, tailWord_4481469, baseEnd_4481469] using wordTrace_append hprefix tailTrace_4481469
  have hstable : (prefixWord ++ tailWord_4481469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481469).length < 2 ^ (prefixWord ++ tailWord_4481469).sum := by decide
  have hdescent : baseEnd_4481469 < baseStart_4481469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481497 : List Nat := [1, 2, 1, 2, 4, 1, 5, 2, 1, 2, 2]
def baseStart_4481497 : Nat := 118140960795 + 4481497 * 2 ^ 59
def prefixEnd_4481497 : Nat := 4983230072969 + 3 ^ 40 * 4481497 * 2
def baseEnd_4481497 : Nat := 2301162012682357856077477

theorem tailTrace_4481497 : CollatzResearch.WordTrace tailWord_4481497 prefixEnd_4481497 2301162012682357856077477 := by
  unfold tailWord_4481497
  simp only [CollatzResearch.WordTrace]
  refine ⟨163453623845309222597794745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108969082563539481731863163 163453623845309222597794745)
  ·
    refine ⟨122590217883981916948346059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163453623845309222597794745 122590217883981916948346059)
    ·
      refine ⟨183885326825972875422519089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122590217883981916948346059 183885326825972875422519089)
      ·
        refine ⟨137913995119479656566889317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183885326825972875422519089 137913995119479656566889317)
        ·
          refine ⟨25858874084902435606291747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137913995119479656566889317 25858874084902435606291747)
          ·
            refine ⟨38788311127353653409437621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25858874084902435606291747 38788311127353653409437621)
            ·
              refine ⟨3636404168189405007134777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38788311127353653409437621 3636404168189405007134777)
              ·
                refine ⟨2727303126142053755351083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3636404168189405007134777 2727303126142053755351083)
                ·
                  refine ⟨4090954689213080633026625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727303126142053755351083 4090954689213080633026625)
                  ·
                    refine ⟨3068216016909810474769969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4090954689213080633026625 3068216016909810474769969)
                    ·
                      refine ⟨2301162012682357856077477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068216016909810474769969 2301162012682357856077477)
                      ·
                        rfl

theorem cell23_4481497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_4481497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481497 prefixEnd_4481497 := by exact prefixLift 4481497
  have htrace : WordTrace (prefixWord ++ tailWord_4481497) baseStart_4481497 baseEnd_4481497 := by
    simpa [prefixWord, tailWord_4481497, baseEnd_4481497] using wordTrace_append hprefix tailTrace_4481497
  have hstable : (prefixWord ++ tailWord_4481497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481497).length < 2 ^ (prefixWord ++ tailWord_4481497).sum := by decide
  have hdescent : baseEnd_4481497 < baseStart_4481497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481507 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 2, 4]
def baseStart_4481507 : Nat := 118140960795 + 4481507 * 2 ^ 59
def prefixEnd_4481507 : Nat := 4983230072969 + 3 ^ 40 * 4481507 * 2
def baseEnd_4481507 : Nat := 767055715829634272317477

theorem tailTrace_4481507 : CollatzResearch.WordTrace tailWord_4481507 prefixEnd_4481507 767055715829634272317477 := by
  unfold tailWord_4481507
  simp only [CollatzResearch.WordTrace]
  refine ⟨163453988575272994305658775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108969325716848662870439183 163453988575272994305658775)
  ·
    refine ⟨245180982862909491458488163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163453988575272994305658775 245180982862909491458488163)
    ·
      refine ⟨367771474294364237187732245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245180982862909491458488163 367771474294364237187732245)
      ·
        refine ⟨17239287857548323618174949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 367771474294364237187732245 17239287857548323618174949)
        ·
          refine ⟨3232366473290310678407803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17239287857548323618174949 3232366473290310678407803)
          ·
            refine ⟨4848549709935466017611705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232366473290310678407803 4848549709935466017611705)
            ·
              refine ⟨3636412282451599513208779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4848549709935466017611705 3636412282451599513208779)
              ·
                refine ⟨5454618423677399269813169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636412282451599513208779 5454618423677399269813169)
                ·
                  refine ⟨4090963817758049452359877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5454618423677399269813169 4090963817758049452359877)
                  ·
                    refine ⟨767055715829634272317477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4090963817758049452359877 767055715829634272317477)
                    ·
                      rfl

theorem cell23_4481507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 4].length) (baseStart_4481507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481507 prefixEnd_4481507 := by exact prefixLift 4481507
  have htrace : WordTrace (prefixWord ++ tailWord_4481507) baseStart_4481507 baseEnd_4481507 := by
    simpa [prefixWord, tailWord_4481507, baseEnd_4481507] using wordTrace_append hprefix tailTrace_4481507
  have hstable : (prefixWord ++ tailWord_4481507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481507).length < 2 ^ (prefixWord ++ tailWord_4481507).sum := by decide
  have hdescent : baseEnd_4481507 < baseStart_4481507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481539 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 5]
def baseStart_4481539 : Nat := 118140960795 + 4481539 * 2 ^ 59
def prefixEnd_4481539 : Nat := 4983230072969 + 3 ^ 40 * 4481539 * 2
def baseEnd_4481539 : Nat := 2301183578869846691752283

theorem tailTrace_4481539 : CollatzResearch.WordTrace tailWord_4481539 prefixEnd_4481539 2301183578869846691752283 := by
  unfold tailWord_4481539
  simp only [CollatzResearch.WordTrace]
  refine ⟨163455155711157063770823671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108970103807438042513882447 163455155711157063770823671)
  ·
    refine ⟨245182733566735595656235507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163455155711157063770823671 245182733566735595656235507)
    ·
      refine ⟨367774100350103393484353261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245182733566735595656235507 367774100350103393484353261)
      ·
        refine ⟨137915287631288772556632473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367774100350103393484353261 137915287631288772556632473)
        ·
          refine ⟨103436465723466579417474355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137915287631288772556632473 103436465723466579417474355)
          ·
            refine ⟨155154698585199869126211533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103436465723466579417474355 155154698585199869126211533)
            ·
              refine ⟨58183011969449950922329325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155154698585199869126211533 58183011969449950922329325)
              ·
                refine ⟨21818629488543731595873497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58183011969449950922329325 21818629488543731595873497)
                ·
                  refine ⟨16363972116407798696905123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21818629488543731595873497 16363972116407798696905123)
                  ·
                    refine ⟨24545958174611698045357685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16363972116407798696905123 24545958174611698045357685)
                    ·
                      refine ⟨2301183578869846691752283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24545958174611698045357685 2301183578869846691752283)
                      ·
                        rfl

theorem cell23_4481539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_4481539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481539 prefixEnd_4481539 := by exact prefixLift 4481539
  have htrace : WordTrace (prefixWord ++ tailWord_4481539) baseStart_4481539 baseEnd_4481539 := by
    simpa [prefixWord, tailWord_4481539, baseEnd_4481539] using wordTrace_append hprefix tailTrace_4481539
  have hstable : (prefixWord ++ tailWord_4481539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481539).length < 2 ^ (prefixWord ++ tailWord_4481539).sum := by decide
  have hdescent : baseEnd_4481539 < baseStart_4481539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481576 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 9]
def baseStart_4481576 : Nat := 118140960795 + 4481576 * 2 ^ 59
def prefixEnd_4481576 : Nat := 4983230072969 + 3 ^ 40 * 4481576 * 2
def baseEnd_4481576 : Nat := 255689175294895894109957

theorem tailTrace_4481576 : CollatzResearch.WordTrace tailWord_4481576 prefixEnd_4481576 255689175294895894109957 := by
  unfold tailWord_4481576
  simp only [CollatzResearch.WordTrace]
  refine ⟨81728252606011509544960291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108971003474682012726613721 81728252606011509544960291)
  ·
    refine ⟨122592378909017264317440437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81728252606011509544960291 122592378909017264317440437)
    ·
      refine ⟨11493035522720368529760041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122592378909017264317440437 11493035522720368529760041)
      ·
        refine ⟨8619776642040276397320031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11493035522720368529760041 8619776642040276397320031)
        ·
          refine ⟨12929664963060414595980047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8619776642040276397320031 12929664963060414595980047)
          ·
            refine ⟨19394497444590621893970071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12929664963060414595980047 19394497444590621893970071)
            ·
              refine ⟨29091746166885932840955107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19394497444590621893970071 29091746166885932840955107)
              ·
                refine ⟨43637619250328899261432661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29091746166885932840955107 43637619250328899261432661)
                ·
                  refine ⟨255689175294895894109957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43637619250328899261432661 255689175294895894109957)
                  ·
                    rfl

theorem cell23_4481576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 9].length) (baseStart_4481576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481576 prefixEnd_4481576 := by exact prefixLift 4481576
  have htrace : WordTrace (prefixWord ++ tailWord_4481576) baseStart_4481576 baseEnd_4481576 := by
    simpa [prefixWord, tailWord_4481576, baseEnd_4481576] using wordTrace_append hprefix tailTrace_4481576
  have hstable : (prefixWord ++ tailWord_4481576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481576).length < 2 ^ (prefixWord ++ tailWord_4481576).sum := by decide
  have hdescent : baseEnd_4481576 < baseStart_4481576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481593 : List Nat := [1, 2, 1, 5, 1, 1, 4, 3, 5]
def baseStart_4481593 : Nat := 118140960795 + 4481593 * 2 ^ 59
def prefixEnd_4481593 : Nat := 4983230072969 + 3 ^ 40 * 4481593 * 2
def baseEnd_4481593 : Nat := 255690145202798831164115

theorem tailTrace_4481593 : CollatzResearch.WordTrace tailWord_4481593 prefixEnd_4481593 255690145202798831164115 := by
  unfold tailWord_4481593
  simp only [CollatzResearch.WordTrace]
  refine ⟨163457125252961430993289433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108971416835307620662192955 163457125252961430993289433)
  ·
    refine ⟨122592843939721073244967075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163457125252961430993289433 122592843939721073244967075)
    ·
      refine ⟨183889265909581609867450613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122592843939721073244967075 183889265909581609867450613)
      ·
        refine ⟨17239618679023275925073495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183889265909581609867450613 17239618679023275925073495)
        ·
          refine ⟨25859428018534913887610243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17239618679023275925073495 25859428018534913887610243)
          ·
            refine ⟨38789142027802370831415365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25859428018534913887610243 38789142027802370831415365)
            ·
              refine ⟨7272964130212944530890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38789142027802370831415365 7272964130212944530890381)
              ·
                refine ⟨2727361548829854199083893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7272964130212944530890381 2727361548829854199083893)
                ·
                  refine ⟨255690145202798831164115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2727361548829854199083893 255690145202798831164115)
                  ·
                    rfl

theorem cell23_4481593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 5].length) (baseStart_4481593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481593 prefixEnd_4481593 := by exact prefixLift 4481593
  have htrace : WordTrace (prefixWord ++ tailWord_4481593) baseStart_4481593 baseEnd_4481593 := by
    simpa [prefixWord, tailWord_4481593, baseEnd_4481593] using wordTrace_append hprefix tailTrace_4481593
  have hstable : (prefixWord ++ tailWord_4481593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481593).length < 2 ^ (prefixWord ++ tailWord_4481593).sum := by decide
  have hdescent : baseEnd_4481593 < baseStart_4481593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481676 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_4481676 : Nat := 118140960795 + 4481676 * 2 ^ 59
def prefixEnd_4481676 : Nat := 4983230072969 + 3 ^ 40 * 4481676 * 2
def baseEnd_4481676 : Nat := 2301253925719512655739153

theorem tailTrace_4481676 : CollatzResearch.WordTrace tailWord_4481676 prefixEnd_4481676 2301253925719512655739153 := by
  unfold tailWord_4481676
  simp only [CollatzResearch.WordTrace]
  refine ⟨81730076255830368084280441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108973435007773824112373921 81730076255830368084280441)
  ·
    refine ⟨61297557191872776063210331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81730076255830368084280441 61297557191872776063210331)
    ·
      refine ⟨91946335787809164094815497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61297557191872776063210331 91946335787809164094815497)
      ·
        refine ⟨68959751840856873071111623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91946335787809164094815497 68959751840856873071111623)
        ·
          refine ⟨103439627761285309606667435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68959751840856873071111623 103439627761285309606667435)
          ·
            refine ⟨155159441641927964410001153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103439627761285309606667435 155159441641927964410001153)
            ·
              refine ⟨116369581231445973307500865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155159441641927964410001153 116369581231445973307500865)
              ·
                refine ⟨87277185923584479980625649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116369581231445973307500865 87277185923584479980625649)
                ·
                  refine ⟨65457889442688359985469237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87277185923584479980625649 65457889442688359985469237)
                  ·
                    refine ⟨6136677135252033748637741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65457889442688359985469237 6136677135252033748637741)
                    ·
                      refine ⟨2301253925719512655739153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6136677135252033748637741 2301253925719512655739153)
                      ·
                        rfl

theorem cell23_4481676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_4481676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481676 prefixEnd_4481676 := by exact prefixLift 4481676
  have htrace : WordTrace (prefixWord ++ tailWord_4481676) baseStart_4481676 baseEnd_4481676 := by
    simpa [prefixWord, tailWord_4481676, baseEnd_4481676] using wordTrace_append hprefix tailTrace_4481676
  have hstable : (prefixWord ++ tailWord_4481676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481676).length < 2 ^ (prefixWord ++ tailWord_4481676).sum := by decide
  have hdescent : baseEnd_4481676 < baseStart_4481676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481727 : List Nat := [1, 1, 2, 2, 2, 5, 1, 4, 1, 1, 3]
def baseStart_4481727 : Nat := 118140960795 + 4481727 * 2 ^ 59
def prefixEnd_4481727 : Nat := 4983230072969 + 3 ^ 40 * 4481727 * 2
def baseEnd_4481727 : Nat := 2301280113232891956201419

theorem tailTrace_4481727 : CollatzResearch.WordTrace tailWord_4481727 prefixEnd_4481727 2301280113232891956201419 := by
  unfold tailWord_4481727
  simp only [CollatzResearch.WordTrace]
  refine ⟨163462012634475971878667435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108974675089650647919111623 163462012634475971878667435)
  ·
    refine ⟨245193018951713957818001153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163462012634475971878667435 245193018951713957818001153)
    ·
      refine ⟨183894764213785468363500865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245193018951713957818001153 183894764213785468363500865)
      ·
        refine ⟨137921073160339101272625649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183894764213785468363500865 137921073160339101272625649)
        ·
          refine ⟨103440804870254325954469237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137921073160339101272625649 103440804870254325954469237)
          ·
            refine ⟨9697575456586343058231491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103440804870254325954469237 9697575456586343058231491)
            ·
              refine ⟨14546363184879514587347237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9697575456586343058231491 14546363184879514587347237)
              ·
                refine ⟨2727443097164908985127607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14546363184879514587347237 2727443097164908985127607)
                ·
                  refine ⟨4091164645747363477691411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727443097164908985127607 4091164645747363477691411)
                  ·
                    refine ⟨6136746968621045216537117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4091164645747363477691411 6136746968621045216537117)
                    ·
                      refine ⟨2301280113232891956201419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6136746968621045216537117 2301280113232891956201419)
                      ·
                        rfl

theorem cell23_4481727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_4481727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481727 prefixEnd_4481727 := by exact prefixLift 4481727
  have htrace : WordTrace (prefixWord ++ tailWord_4481727) baseStart_4481727 baseEnd_4481727 := by
    simpa [prefixWord, tailWord_4481727, baseEnd_4481727] using wordTrace_append hprefix tailTrace_4481727
  have hstable : (prefixWord ++ tailWord_4481727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481727).length < 2 ^ (prefixWord ++ tailWord_4481727).sum := by decide
  have hdescent : baseEnd_4481727 < baseStart_4481727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481753 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 3]
def baseStart_4481753 : Nat := 118140960795 + 4481753 * 2 ^ 59
def prefixEnd_4481753 : Nat := 4983230072969 + 3 ^ 40 * 4481753 * 2
def baseEnd_4481753 : Nat := 2301293463729908854476299

theorem tailTrace_4481753 : CollatzResearch.WordTrace tailWord_4481753 prefixEnd_4481753 2301293463729908854476299 := by
  unfold tailWord_4481753
  simp only [CollatzResearch.WordTrace]
  refine ⟨163462960932381778319113913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108975307288254518879409275 163462960932381778319113913)
  ·
    refine ⟨122597220699286333739335435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163462960932381778319113913 122597220699286333739335435)
    ·
      refine ⟨183895831048929500609003153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122597220699286333739335435 183895831048929500609003153)
      ·
        refine ⟨137921873286697125456752365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183895831048929500609003153 137921873286697125456752365)
        ·
          refine ⟨51720702482511422046282137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137921873286697125456752365 51720702482511422046282137)
          ·
            refine ⟨38790526861883566534711603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51720702482511422046282137 38790526861883566534711603)
            ·
              refine ⟨58185790292825349802067405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38790526861883566534711603 58185790292825349802067405)
              ·
                refine ⟨21819671359809506175775277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58185790292825349802067405 21819671359809506175775277)
                ·
                  refine ⟨8182376759928564815915729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21819671359809506175775277 8182376759928564815915729)
                  ·
                    refine ⟨6136782569946423611936797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8182376759928564815915729 6136782569946423611936797)
                    ·
                      refine ⟨2301293463729908854476299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6136782569946423611936797 2301293463729908854476299)
                      ·
                        rfl

theorem cell23_4481753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_4481753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481753 prefixEnd_4481753 := by exact prefixLift 4481753
  have htrace : WordTrace (prefixWord ++ tailWord_4481753) baseStart_4481753 baseEnd_4481753 := by
    simpa [prefixWord, tailWord_4481753, baseEnd_4481753] using wordTrace_append hprefix tailTrace_4481753
  have hstable : (prefixWord ++ tailWord_4481753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481753).length < 2 ^ (prefixWord ++ tailWord_4481753).sum := by decide
  have hdescent : baseEnd_4481753 < baseStart_4481753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481786 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_4481786 : Nat := 118140960795 + 4481786 * 2 ^ 59
def prefixEnd_4481786 : Nat := 4983230072969 + 3 ^ 40 * 4481786 * 2
def baseEnd_4481786 : Nat := 767103469530502408454549

theorem tailTrace_4481786 : CollatzResearch.WordTrace tailWord_4481786 prefixEnd_4481786 767103469530502408454549 := by
  unfold tailWord_4481786
  simp only [CollatzResearch.WordTrace]
  refine ⟨40866041135315556238766303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108976109694174816636710141 40866041135315556238766303)
  ·
    refine ⟨61299061702973334358149455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40866041135315556238766303 61299061702973334358149455)
    ·
      refine ⟨91948592554460001537224183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61299061702973334358149455 91948592554460001537224183)
      ·
        refine ⟨137922888831690002305836275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91948592554460001537224183 137922888831690002305836275)
        ·
          refine ⟨206884333247535003458754413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137922888831690002305836275 206884333247535003458754413)
          ·
            refine ⟨77581624967825626297032905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206884333247535003458754413 77581624967825626297032905)
            ·
              refine ⟨58186218725869219722774679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77581624967825626297032905 58186218725869219722774679)
              ·
                refine ⟨87279328088803829584162019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58186218725869219722774679 87279328088803829584162019)
                ·
                  refine ⟨130918992133205744376243029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87279328088803829584162019 130918992133205744376243029)
                  ·
                    refine ⟨767103469530502408454549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 130918992133205744376243029 767103469530502408454549)
                    ·
                      rfl

theorem cell23_4481786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_4481786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481786 prefixEnd_4481786 := by exact prefixLift 4481786
  have htrace : WordTrace (prefixWord ++ tailWord_4481786) baseStart_4481786 baseEnd_4481786 := by
    simpa [prefixWord, tailWord_4481786, baseEnd_4481786] using wordTrace_append hprefix tailTrace_4481786
  have hstable : (prefixWord ++ tailWord_4481786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481786).length < 2 ^ (prefixWord ++ tailWord_4481786).sum := by decide
  have hdescent : baseEnd_4481786 < baseStart_4481786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481794 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_4481794 : Nat := 118140960795 + 4481794 * 2 ^ 59
def prefixEnd_4481794 : Nat := 4983230072969 + 3 ^ 40 * 4481794 * 2
def baseEnd_4481794 : Nat := 767104838812247731354537

theorem tailTrace_4481794 : CollatzResearch.WordTrace tailWord_4481794 prefixEnd_4481794 767104838812247731354537 := by
  unfold tailWord_4481794
  simp only [CollatzResearch.WordTrace]
  refine ⟨40866114081308310580339109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108976304216822161547570957 40866114081308310580339109)
  ·
    refine ⟨7662396390245308233813583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40866114081308310580339109 7662396390245308233813583)
    ·
      refine ⟨11493594585367962350720375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7662396390245308233813583 11493594585367962350720375)
      ·
        refine ⟨17240391878051943526080563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11493594585367962350720375 17240391878051943526080563)
        ·
          refine ⟨25860587817077915289120845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17240391878051943526080563 25860587817077915289120845)
          ·
            refine ⟨9697720431404218233420317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25860587817077915289120845 9697720431404218233420317)
            ·
              refine ⟨3636645161776581837532619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9697720431404218233420317 3636645161776581837532619)
              ·
                refine ⟨5454967742664872756298929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636645161776581837532619 5454967742664872756298929)
                ·
                  refine ⟨4091225806998654567224197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5454967742664872756298929 4091225806998654567224197)
                  ·
                    refine ⟨767104838812247731354537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4091225806998654567224197 767104838812247731354537)
                    ·
                      rfl

theorem cell23_4481794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_4481794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481794 prefixEnd_4481794 := by exact prefixLift 4481794
  have htrace : WordTrace (prefixWord ++ tailWord_4481794) baseStart_4481794 baseEnd_4481794 := by
    simpa [prefixWord, tailWord_4481794, baseEnd_4481794] using wordTrace_append hprefix tailTrace_4481794
  have hstable : (prefixWord ++ tailWord_4481794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481794).length < 2 ^ (prefixWord ++ tailWord_4481794).sum := by decide
  have hdescent : baseEnd_4481794 < baseStart_4481794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481800 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_4481800 : Nat := 118140960795 + 4481800 * 2 ^ 59
def prefixEnd_4481800 : Nat := 4983230072969 + 3 ^ 40 * 4481800 * 2
def baseEnd_4481800 : Nat := 2301317597320670170588583

theorem tailTrace_4481800 : CollatzResearch.WordTrace tailWord_4481800 prefixEnd_4481800 2301317597320670170588583 := by
  unfold tailWord_4481800
  simp only [CollatzResearch.WordTrace]
  refine ⟨81732337581605752673037427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108976450108807670230716569 81732337581605752673037427)
  ·
    refine ⟨122598506372408629009556141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81732337581605752673037427 122598506372408629009556141)
    ·
      refine ⟨45974439889653235878583553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122598506372408629009556141 45974439889653235878583553)
      ·
        refine ⟨34480829917239926908937665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45974439889653235878583553 34480829917239926908937665)
        ·
          refine ⟨25860622437929945181703249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34480829917239926908937665 25860622437929945181703249)
          ·
            refine ⟨19395466828447458886277437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25860622437929945181703249 19395466828447458886277437)
            ·
              refine ⟨7273300060667797082354039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19395466828447458886277437 7273300060667797082354039)
              ·
                refine ⟨10909950091001695623531059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7273300060667797082354039 10909950091001695623531059)
                ·
                  refine ⟨16364925136502543435296589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10909950091001695623531059 16364925136502543435296589)
                  ·
                    refine ⟨6136846926188453788236221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16364925136502543435296589 6136846926188453788236221)
                    ·
                      refine ⟨2301317597320670170588583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6136846926188453788236221 2301317597320670170588583)
                      ·
                        rfl

theorem cell23_4481800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_4481800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481800 prefixEnd_4481800 := by exact prefixLift 4481800
  have htrace : WordTrace (prefixWord ++ tailWord_4481800) baseStart_4481800 baseEnd_4481800 := by
    simpa [prefixWord, tailWord_4481800, baseEnd_4481800] using wordTrace_append hprefix tailTrace_4481800
  have hstable : (prefixWord ++ tailWord_4481800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481800).length < 2 ^ (prefixWord ++ tailWord_4481800).sum := by decide
  have hdescent : baseEnd_4481800 < baseStart_4481800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481900 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 1, 7, 2]
def baseStart_4481900 : Nat := 118140960795 + 4481900 * 2 ^ 59
def prefixEnd_4481900 : Nat := 4983230072969 + 3 ^ 40 * 4481900 * 2
def baseEnd_4481900 : Nat := 2301368945386119779338123

theorem tailTrace_4481900 : CollatzResearch.WordTrace tailWord_4481900 prefixEnd_4481900 2301368945386119779338123 := by
  unfold tailWord_4481900
  simp only [CollatzResearch.WordTrace]
  refine ⟨81734161231424611212357577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108978881641899481616476769 81734161231424611212357577)
  ·
    refine ⟨61300620923568458409268183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81734161231424611212357577 61300620923568458409268183)
    ·
      refine ⟨91950931385352687613902275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61300620923568458409268183 91950931385352687613902275)
      ·
        refine ⟨137926397078029031420853413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91950931385352687613902275 137926397078029031420853413)
        ·
          refine ⟨25861199452130443391410015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137926397078029031420853413 25861199452130443391410015)
          ·
            refine ⟨38791799178195665087115023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25861199452130443391410015 38791799178195665087115023)
            ·
              refine ⟨58187698767293497630672535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38791799178195665087115023 58187698767293497630672535)
              ·
                refine ⟨87281548150940246446008803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58187698767293497630672535 87281548150940246446008803)
                ·
                  refine ⟨130922322226410369669013205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87281548150940246446008803 130922322226410369669013205)
                  ·
                    refine ⟨3068491927181493039117497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 130922322226410369669013205 3068491927181493039117497)
                    ·
                      refine ⟨2301368945386119779338123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068491927181493039117497 2301368945386119779338123)
                      ·
                        rfl

theorem cell23_4481900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_4481900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481900 prefixEnd_4481900 := by exact prefixLift 4481900
  have htrace : WordTrace (prefixWord ++ tailWord_4481900) baseStart_4481900 baseEnd_4481900 := by
    simpa [prefixWord, tailWord_4481900, baseEnd_4481900] using wordTrace_append hprefix tailTrace_4481900
  have hstable : (prefixWord ++ tailWord_4481900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481900).length < 2 ^ (prefixWord ++ tailWord_4481900).sum := by decide
  have hdescent : baseEnd_4481900 < baseStart_4481900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481927 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 2, 5]
def baseStart_4481927 : Nat := 118140960795 + 4481927 * 2 ^ 59
def prefixEnd_4481927 : Nat := 4983230072969 + 3 ^ 40 * 4481927 * 2
def baseEnd_4481927 : Nat := 767127603121263724566833

theorem tailTrace_4481927 : CollatzResearch.WordTrace tailWord_4481927 prefixEnd_4481927 767127603121263724566833 := by
  unfold tailWord_4481927
  simp only [CollatzResearch.WordTrace]
  refine ⟨163469307233751406035948035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108979538155834270690632023 163469307233751406035948035)
  ·
    refine ⟨245203960850627109053922053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163469307233751406035948035 245203960850627109053922053)
    ·
      refine ⟨45975742659492582947610385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 245203960850627109053922053 45975742659492582947610385)
      ·
        refine ⟨34481806994619437210707789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45975742659492582947610385 34481806994619437210707789)
        ·
          refine ⟨12930677622982288954015421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34481806994619437210707789 12930677622982288954015421)
          ·
            refine ⟨4849004108618358357755783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12930677622982288954015421 4849004108618358357755783)
            ·
              refine ⟨7273506162927537536633675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4849004108618358357755783 7273506162927537536633675)
              ·
                refine ⟨10910259244391306304950513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7273506162927537536633675 10910259244391306304950513)
                ·
                  refine ⟨8182694433293479728712885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10910259244391306304950513 8182694433293479728712885)
                  ·
                    refine ⟨767127603121263724566833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8182694433293479728712885 767127603121263724566833)
                    ·
                      rfl

theorem cell23_4481927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_4481927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481927 prefixEnd_4481927 := by exact prefixLift 4481927
  have htrace : WordTrace (prefixWord ++ tailWord_4481927) baseStart_4481927 baseEnd_4481927 := by
    simpa [prefixWord, tailWord_4481927, baseEnd_4481927] using wordTrace_append hprefix tailTrace_4481927
  have hstable : (prefixWord ++ tailWord_4481927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481927).length < 2 ^ (prefixWord ++ tailWord_4481927).sum := by decide
  have hdescent : baseEnd_4481927 < baseStart_4481927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481943 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_4481943 : Nat := 118140960795 + 4481943 * 2 ^ 59
def prefixEnd_4481943 : Nat := 4983230072969 + 3 ^ 40 * 4481943 * 2
def baseEnd_4481943 : Nat := 2301391025054263111100425

theorem tailTrace_4481943 : CollatzResearch.WordTrace tailWord_4481943 prefixEnd_4481943 2301391025054263111100425 := by
  unfold tailWord_4481943
  simp only [CollatzResearch.WordTrace]
  refine ⟨163469890801693440768530483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108979927201128960512353655 163469890801693440768530483)
  ·
    refine ⟨245204836202540161152795725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163469890801693440768530483 245204836202540161152795725)
    ·
      refine ⟨91951813575952560432298397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245204836202540161152795725 91951813575952560432298397)
      ·
        refine ⟨34481930090982210162111899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91951813575952560432298397 34481930090982210162111899)
        ·
          refine ⟨51722895136473315243167849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34481930090982210162111899 51722895136473315243167849)
          ·
            refine ⟨38792171352354986432375887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51722895136473315243167849 38792171352354986432375887)
            ·
              refine ⟨58188257028532479648563831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38792171352354986432375887 58188257028532479648563831)
              ·
                refine ⟨87282385542798719472845747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58188257028532479648563831 87282385542798719472845747)
                ·
                  refine ⟨130923578314198079209268621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87282385542798719472845747 130923578314198079209268621)
                  ·
                    refine ⟨49096341867824279703475733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130923578314198079209268621 49096341867824279703475733)
                    ·
                      refine ⟨2301391025054263111100425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49096341867824279703475733 2301391025054263111100425)
                      ·
                        rfl

theorem cell23_4481943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_4481943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481943 prefixEnd_4481943 := by exact prefixLift 4481943
  have htrace : WordTrace (prefixWord ++ tailWord_4481943) baseStart_4481943 baseEnd_4481943 := by
    simpa [prefixWord, tailWord_4481943, baseEnd_4481943] using wordTrace_append hprefix tailTrace_4481943
  have hstable : (prefixWord ++ tailWord_4481943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481943).length < 2 ^ (prefixWord ++ tailWord_4481943).sum := by decide
  have hdescent : baseEnd_4481943 < baseStart_4481943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4481993 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_4481993 : Nat := 118140960795 + 4481993 * 2 ^ 59
def prefixEnd_4481993 : Nat := 4983230072969 + 3 ^ 40 * 4481993 * 2
def baseEnd_4481993 : Nat := 2301416699086987915475195

theorem tailTrace_4481993 : CollatzResearch.WordTrace tailWord_4481993 prefixEnd_4481993 2301416699086987915475195 := by
  unfold tailWord_4481993
  simp only [CollatzResearch.WordTrace]
  refine ⟨163471714451512299307850633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108981142967674866205233755 163471714451512299307850633)
  ·
    refine ⟨122603785838634224480887975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163471714451512299307850633 122603785838634224480887975)
    ·
      refine ⟨183905678757951336721331963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122603785838634224480887975 183905678757951336721331963)
      ·
        refine ⟨275858518136927005081997945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183905678757951336721331963 275858518136927005081997945)
        ·
          refine ⟨206893888602695253811498459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275858518136927005081997945 206893888602695253811498459)
          ·
            refine ⟨310340832904042880717247689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206893888602695253811498459 310340832904042880717247689)
            ·
              refine ⟨232755624678032160537935767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 310340832904042880717247689 232755624678032160537935767)
              ·
                refine ⟨349133437017048240806903651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232755624678032160537935767 349133437017048240806903651)
                ·
                  refine ⟨523700155525572361210355477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 349133437017048240806903651 523700155525572361210355477)
                  ·
                    refine ⟨24548444790261204431735413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 523700155525572361210355477 24548444790261204431735413)
                    ·
                      refine ⟨2301416699086987915475195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24548444790261204431735413 2301416699086987915475195)
                      ·
                        rfl

theorem cell23_4481993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_4481993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4481993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4481993 prefixEnd_4481993 := by exact prefixLift 4481993
  have htrace : WordTrace (prefixWord ++ tailWord_4481993) baseStart_4481993 baseEnd_4481993 := by
    simpa [prefixWord, tailWord_4481993, baseEnd_4481993] using wordTrace_append hprefix tailTrace_4481993
  have hstable : (prefixWord ++ tailWord_4481993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4481993).length < 2 ^ (prefixWord ++ tailWord_4481993).sum := by decide
  have hdescent : baseEnd_4481993 < baseStart_4481993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4481993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482021 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 6]
def baseStart_4482021 : Nat := 118140960795 + 4482021 * 2 ^ 59
def prefixEnd_4482021 : Nat := 4983230072969 + 3 ^ 40 * 4482021 * 2
def baseEnd_4482021 : Nat := 255714564060590422880563

theorem tailTrace_4482021 : CollatzResearch.WordTrace tailWord_4482021 prefixEnd_4482021 255714564060590422880563 := by
  unfold tailWord_4482021
  simp only [CollatzResearch.WordTrace]
  refine ⟨163472735695410860089869917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108981823796940573393246611 163472735695410860089869917)
  ·
    refine ⟨61302275885779072533701219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163472735695410860089869917 61302275885779072533701219)
    ·
      refine ⟨91953413828668608800551829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61302275885779072533701219 91953413828668608800551829)
      ·
        refine ⟨4310316273218841037525867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91953413828668608800551829 4310316273218841037525867)
        ·
          refine ⟨6465474409828261556288801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4310316273218841037525867 6465474409828261556288801)
          ·
            refine ⟨4849105807371196167216601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6465474409828261556288801 4849105807371196167216601)
            ·
              refine ⟨3636829355528397125412451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4849105807371196167216601 3636829355528397125412451)
              ·
                refine ⟨5455244033292595688118677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636829355528397125412451 5455244033292595688118677)
                ·
                  refine ⟨255714564060590422880563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5455244033292595688118677 255714564060590422880563)
                  ·
                    rfl

theorem cell23_4482021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_4482021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482021 prefixEnd_4482021 := by exact prefixLift 4482021
  have htrace : WordTrace (prefixWord ++ tailWord_4482021) baseStart_4482021 baseEnd_4482021 := by
    simpa [prefixWord, tailWord_4482021, baseEnd_4482021] using wordTrace_append hprefix tailTrace_4482021
  have hstable : (prefixWord ++ tailWord_4482021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482021).length < 2 ^ (prefixWord ++ tailWord_4482021).sum := by decide
  have hdescent : baseEnd_4482021 < baseStart_4482021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482034 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_4482034 : Nat := 118140960795 + 4482034 * 2 ^ 59
def prefixEnd_4482034 : Nat := 4983230072969 + 3 ^ 40 * 4482034 * 2
def baseEnd_4482034 : Nat := 767145917264607418354169

theorem tailTrace_4482034 : CollatzResearch.WordTrace tailWord_4482034 prefixEnd_4482034 767145917264607418354169 := by
  unfold tailWord_4482034
  simp only [CollatzResearch.WordTrace]
  refine ⟨40868302461090940827523289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108982139896242508873395437 40868302461090940827523289)
  ·
    refine ⟨30651226845818205620642467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40868302461090940827523289 30651226845818205620642467)
    ·
      refine ⟨45976840268727308430963701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30651226845818205620642467 45976840268727308430963701)
      ·
        refine ⟨4310328775193185165402847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45976840268727308430963701 4310328775193185165402847)
        ·
          refine ⟨6465493162789777748104271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4310328775193185165402847 6465493162789777748104271)
          ·
            refine ⟨9698239744184666622156407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6465493162789777748104271 9698239744184666622156407)
            ·
              refine ⟨14547359616276999933234611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9698239744184666622156407 14547359616276999933234611)
              ·
                refine ⟨21821039424415499899851917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14547359616276999933234611 21821039424415499899851917)
                ·
                  refine ⟨8182889784155812462444469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21821039424415499899851917 8182889784155812462444469)
                  ·
                    refine ⟨767145917264607418354169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8182889784155812462444469 767145917264607418354169)
                    ·
                      rfl

theorem cell23_4482034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_4482034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482034 prefixEnd_4482034 := by exact prefixLift 4482034
  have htrace : WordTrace (prefixWord ++ tailWord_4482034) baseStart_4482034 baseEnd_4482034 := by
    simpa [prefixWord, tailWord_4482034, baseEnd_4482034] using wordTrace_append hprefix tailTrace_4482034
  have hstable : (prefixWord ++ tailWord_4482034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482034).length < 2 ^ (prefixWord ++ tailWord_4482034).sum := by decide
  have hdescent : baseEnd_4482034 < baseStart_4482034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482057 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 3]
def baseStart_4482057 : Nat := 118140960795 + 4482057 * 2 ^ 59
def prefixEnd_4482057 : Nat := 4983230072969 + 3 ^ 40 * 4482057 * 2
def baseEnd_4482057 : Nat := 2301449561848875665074901

theorem tailTrace_4482057 : CollatzResearch.WordTrace tailWord_4482057 prefixEnd_4482057 2301449561848875665074901 := by
  unfold tailWord_4482057
  simp only [CollatzResearch.WordTrace]
  refine ⟨163474048723280438238180425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108982699148853625492120283 163474048723280438238180425)
  ·
    refine ⟨122605536542460328678635319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163474048723280438238180425 122605536542460328678635319)
    ·
      refine ⟨183908304813690493017952979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122605536542460328678635319 183908304813690493017952979)
      ·
        refine ⟨275862457220535739526929469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183908304813690493017952979 275862457220535739526929469)
        ·
          refine ⟨103448421457700902322598551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275862457220535739526929469 103448421457700902322598551)
          ·
            refine ⟨155172632186551353483897827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103448421457700902322598551 155172632186551353483897827)
            ·
              refine ⟨232758948279827030225846741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155172632186551353483897827 232758948279827030225846741)
              ·
                refine ⟨5455287850308446020918283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 232758948279827030225846741 5455287850308446020918283)
                ·
                  refine ⟨8182931775462669031377425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5455287850308446020918283 8182931775462669031377425)
                  ·
                    refine ⟨6137198831597001773533069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8182931775462669031377425 6137198831597001773533069)
                    ·
                      refine ⟨2301449561848875665074901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6137198831597001773533069 2301449561848875665074901)
                      ·
                        rfl

theorem cell23_4482057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 2, 3].length) (baseStart_4482057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482057 prefixEnd_4482057 := by exact prefixLift 4482057
  have htrace : WordTrace (prefixWord ++ tailWord_4482057) baseStart_4482057 baseEnd_4482057 := by
    simpa [prefixWord, tailWord_4482057, baseEnd_4482057] using wordTrace_append hprefix tailTrace_4482057
  have hstable : (prefixWord ++ tailWord_4482057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482057).length < 2 ^ (prefixWord ++ tailWord_4482057).sum := by decide
  have hdescent : baseEnd_4482057 < baseStart_4482057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482084 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4482084 : Nat := 118140960795 + 4482084 * 2 ^ 59
def prefixEnd_4482084 : Nat := 4983230072969 + 3 ^ 40 * 4482084 * 2
def baseEnd_4482084 : Nat := 2301463425826547059437277

theorem tailTrace_4482084 : CollatzResearch.WordTrace tailWord_4482084 prefixEnd_4482084 2301463425826547059437277 := by
  unfold tailWord_4482084
  simp only [CollatzResearch.WordTrace]
  refine ⟨81737516747091310924706653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108983355662788414566275537 81737516747091310924706653)
  ·
    refine ⟨30651568780159241596764995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81737516747091310924706653 30651568780159241596764995)
    ·
      refine ⟨45977353170238862395147493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30651568780159241596764995 45977353170238862395147493)
      ·
        refine ⟨8620753719419786699090155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45977353170238862395147493 8620753719419786699090155)
        ·
          refine ⟨12931130579129680048635233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8620753719419786699090155 12931130579129680048635233)
          ·
            refine ⟨9698347934347260036476425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12931130579129680048635233 9698347934347260036476425)
            ·
              refine ⟨7273760950760445027357319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9698347934347260036476425 7273760950760445027357319)
              ·
                refine ⟨10910641426140667541035979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7273760950760445027357319 10910641426140667541035979)
                ·
                  refine ⟨16365962139211001311553969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10910641426140667541035979 16365962139211001311553969)
                  ·
                    refine ⟨12274471604408250983665477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16365962139211001311553969 12274471604408250983665477)
                    ·
                      refine ⟨2301463425826547059437277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12274471604408250983665477 2301463425826547059437277)
                      ·
                        rfl

theorem cell23_4482084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4482084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482084 prefixEnd_4482084 := by exact prefixLift 4482084
  have htrace : WordTrace (prefixWord ++ tailWord_4482084) baseStart_4482084 baseEnd_4482084 := by
    simpa [prefixWord, tailWord_4482084, baseEnd_4482084] using wordTrace_append hprefix tailTrace_4482084
  have hstable : (prefixWord ++ tailWord_4482084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482084).length < 2 ^ (prefixWord ++ tailWord_4482084).sum := by decide
  have hdescent : baseEnd_4482084 < baseStart_4482084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482120 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 4, 6]
def baseStart_4482120 : Nat := 118140960795 + 4482120 * 2 ^ 59
def prefixEnd_4482120 : Nat := 4983230072969 + 3 ^ 40 * 4482120 * 2
def baseEnd_4482120 : Nat := 767160637043369639529037

theorem tailTrace_4482120 : CollatzResearch.WordTrace tailWord_4482120 prefixEnd_4482120 767160637043369639529037 := by
  unfold tailWord_4482120
  simp only [CollatzResearch.WordTrace]
  refine ⟨81738173261026099998861907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108984231014701466665149209 81738173261026099998861907)
  ·
    refine ⟨122607259891539149998292861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81738173261026099998861907 122607259891539149998292861)
    ·
      refine ⟨45977722459327181249359823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122607259891539149998292861 45977722459327181249359823)
      ·
        refine ⟨68966583688990771874039735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45977722459327181249359823 68966583688990771874039735)
        ·
          refine ⟨103449875533486157811059603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68966583688990771874039735 103449875533486157811059603)
          ·
            refine ⟨155174813300229236716589405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103449875533486157811059603 155174813300229236716589405)
            ·
              refine ⟨58190554987585963768721027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155174813300229236716589405 58190554987585963768721027)
              ·
                refine ⟨87285832481378945653081541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58190554987585963768721027 87285832481378945653081541)
                ·
                  refine ⟨16366093590258552309952789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87285832481378945653081541 16366093590258552309952789)
                  ·
                    refine ⟨767160637043369639529037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16366093590258552309952789 767160637043369639529037)
                    ·
                      rfl

theorem cell23_4482120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_4482120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482120 prefixEnd_4482120 := by exact prefixLift 4482120
  have htrace : WordTrace (prefixWord ++ tailWord_4482120) baseStart_4482120 baseEnd_4482120 := by
    simpa [prefixWord, tailWord_4482120, baseEnd_4482120] using wordTrace_append hprefix tailTrace_4482120
  have hstable : (prefixWord ++ tailWord_4482120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482120).length < 2 ^ (prefixWord ++ tailWord_4482120).sum := by decide
  have hdescent : baseEnd_4482120 < baseStart_4482120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482170 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_4482170 : Nat := 118140960795 + 4482170 * 2 ^ 59
def prefixEnd_4482170 : Nat := 4983230072969 + 3 ^ 40 * 4482170 * 2
def baseEnd_4482170 : Nat := 2301507585162833722961881

theorem tailTrace_4482170 : CollatzResearch.WordTrace tailWord_4482170 prefixEnd_4482170 2301507585162833722961881 := by
  unfold tailWord_4482170
  simp only [CollatzResearch.WordTrace]
  refine ⟨40869542542967764634260991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108985446781247372358029309 40869542542967764634260991)
  ·
    refine ⟨61304313814451646951391487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40869542542967764634260991 61304313814451646951391487)
    ·
      refine ⟨91956470721677470427087231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61304313814451646951391487 91956470721677470427087231)
      ·
        refine ⟨137934706082516205640630847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91956470721677470427087231 137934706082516205640630847)
        ·
          refine ⟨206902059123774308460946271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137934706082516205640630847 206902059123774308460946271)
          ·
            refine ⟨310353088685661462691419407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206902059123774308460946271 310353088685661462691419407)
            ·
              refine ⟨465529633028492194037129111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 310353088685661462691419407 465529633028492194037129111)
              ·
                refine ⟨698294449542738291055693667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465529633028492194037129111 698294449542738291055693667)
                ·
                  refine ⟨1047441674314107436583540501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698294449542738291055693667 1047441674314107436583540501)
                  ·
                    refine ⟨49098828483473786089853461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1047441674314107436583540501 49098828483473786089853461)
                    ·
                      refine ⟨2301507585162833722961881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49098828483473786089853461 2301507585162833722961881)
                      ·
                        rfl

theorem cell23_4482170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_4482170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482170 prefixEnd_4482170 := by exact prefixLift 4482170
  have htrace : WordTrace (prefixWord ++ tailWord_4482170) baseStart_4482170 baseEnd_4482170 := by
    simpa [prefixWord, tailWord_4482170, baseEnd_4482170] using wordTrace_append hprefix tailTrace_4482170
  have hstable : (prefixWord ++ tailWord_4482170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482170).length < 2 ^ (prefixWord ++ tailWord_4482170).sum := by decide
  have hdescent : baseEnd_4482170 < baseStart_4482170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482234 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2]
def baseStart_4482234 : Nat := 118140960795 + 4482234 * 2 ^ 59
def prefixEnd_4482234 : Nat := 4983230072969 + 3 ^ 40 * 4482234 * 2
def baseEnd_4482234 : Nat := 2301540447924721472561587

theorem tailTrace_4482234 : CollatzResearch.WordTrace tailWord_4482234 prefixEnd_4482234 2301540447924721472561587 := by
  unfold tailWord_4482234
  simp only [CollatzResearch.WordTrace]
  refine ⟨40870126110909799366843439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108987002962426131644915837 40870126110909799366843439)
  ·
    refine ⟨61305189166364699050265159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40870126110909799366843439 61305189166364699050265159)
    ·
      refine ⟨91957783749547048575397739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61305189166364699050265159 91957783749547048575397739)
      ·
        refine ⟨137936675624320572863096609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91957783749547048575397739 137936675624320572863096609)
        ·
          refine ⟨103452506718240429647322457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137936675624320572863096609 103452506718240429647322457)
          ·
            refine ⟨77589380038680322235491843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103452506718240429647322457 77589380038680322235491843)
            ·
              refine ⟨116384070058020483353237765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77589380038680322235491843 116384070058020483353237765)
              ·
                refine ⟨21822013135878840628732081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116384070058020483353237765 21822013135878840628732081)
                ·
                  refine ⟨16366509851909130471549061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21822013135878840628732081 16366509851909130471549061)
                  ·
                    refine ⟨3068720597232961963415449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16366509851909130471549061 3068720597232961963415449)
                    ·
                      refine ⟨2301540447924721472561587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068720597232961963415449 2301540447924721472561587)
                      ·
                        rfl

theorem cell23_4482234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_4482234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482234 prefixEnd_4482234 := by exact prefixLift 4482234
  have htrace : WordTrace (prefixWord ++ tailWord_4482234) baseStart_4482234 baseEnd_4482234 := by
    simpa [prefixWord, tailWord_4482234, baseEnd_4482234] using wordTrace_append hprefix tailTrace_4482234
  have hstable : (prefixWord ++ tailWord_4482234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482234).length < 2 ^ (prefixWord ++ tailWord_4482234).sum := by decide
  have hdescent : baseEnd_4482234 < baseStart_4482234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482261 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_4482261 : Nat := 118140960795 + 4482261 * 2 ^ 59
def prefixEnd_4482261 : Nat := 4983230072969 + 3 ^ 40 * 4482261 * 2
def baseEnd_4482261 : Nat := 767184770634130955641321

theorem tailTrace_4482261 : CollatzResearch.WordTrace tailWord_4482261 prefixEnd_4482261 767184770634130955641321 := by
  unfold tailWord_4482261
  simp only [CollatzResearch.WordTrace]
  refine ⟨163481489214541381078606637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108987659476360920719071091 163481489214541381078606637)
  ·
    refine ⟨61305558455453017904477489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163481489214541381078606637 61305558455453017904477489)
    ·
      refine ⟨45979168841589763428358117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61305558455453017904477489 45979168841589763428358117)
      ·
        refine ⟨8621094157798080642817147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45979168841589763428358117 8621094157798080642817147)
        ·
          refine ⟨12931641236697120964225721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8621094157798080642817147 12931641236697120964225721)
          ·
            refine ⟨9698730927522840723169291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12931641236697120964225721 9698730927522840723169291)
            ·
              refine ⟨14548096391284261084753937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9698730927522840723169291 14548096391284261084753937)
              ·
                refine ⟨10911072293463195813565453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14548096391284261084753937 10911072293463195813565453)
                ·
                  refine ⟨4091652110048698430087045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10911072293463195813565453 4091652110048698430087045)
                  ·
                    refine ⟨767184770634130955641321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4091652110048698430087045 767184770634130955641321)
                    ·
                      rfl

theorem cell23_4482261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_4482261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482261 prefixEnd_4482261 := by exact prefixLift 4482261
  have htrace : WordTrace (prefixWord ++ tailWord_4482261) baseStart_4482261 baseEnd_4482261 := by
    simpa [prefixWord, tailWord_4482261, baseEnd_4482261] using wordTrace_append hprefix tailTrace_4482261
  have hstable : (prefixWord ++ tailWord_4482261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482261).length < 2 ^ (prefixWord ++ tailWord_4482261).sum := by decide
  have hdescent : baseEnd_4482261 < baseStart_4482261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482341 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_4482341 : Nat := 118140960795 + 4482341 * 2 ^ 59
def prefixEnd_4482341 : Nat := 4983230072969 + 3 ^ 40 * 4482341 * 2
def baseEnd_4482341 : Nat := 2301595390354752553923595

theorem tailTrace_4482341 : CollatzResearch.WordTrace tailWord_4482341 prefixEnd_4482341 2301595390354752553923595 := by
  unfold tailWord_4482341
  simp only [CollatzResearch.WordTrace]
  refine ⟨163484407054251554741518877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108989604702834369827679251 163484407054251554741518877)
  ·
    refine ⟨61306652645344333028069579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163484407054251554741518877 61306652645344333028069579)
    ·
      refine ⟨91959978968016499542104369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61306652645344333028069579 91959978968016499542104369)
      ·
        refine ⟨68969984226012374656578277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91959978968016499542104369 68969984226012374656578277)
        ·
          refine ⟨12931872042377320248108427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68969984226012374656578277 12931872042377320248108427)
          ·
            refine ⟨19397808063565980372162641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12931872042377320248108427 19397808063565980372162641)
            ·
              refine ⟨14548356047674485279121981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19397808063565980372162641 14548356047674485279121981)
              ·
                refine ⟨5455633517877931979670743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14548356047674485279121981 5455633517877931979670743)
                ·
                  refine ⟨8183450276816897969506115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5455633517877931979670743 8183450276816897969506115)
                  ·
                    refine ⟨12275175415225346954259173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8183450276816897969506115 12275175415225346954259173)
                    ·
                      refine ⟨2301595390354752553923595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12275175415225346954259173 2301595390354752553923595)
                      ·
                        rfl

theorem cell23_4482341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_4482341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482341 prefixEnd_4482341 := by exact prefixLift 4482341
  have htrace : WordTrace (prefixWord ++ tailWord_4482341) baseStart_4482341 baseEnd_4482341 := by
    simpa [prefixWord, tailWord_4482341, baseEnd_4482341] using wordTrace_append hprefix tailTrace_4482341
  have hstable : (prefixWord ++ tailWord_4482341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482341).length < 2 ^ (prefixWord ++ tailWord_4482341).sum := by decide
  have hdescent : baseEnd_4482341 < baseStart_4482341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482354 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_4482354 : Nat := 118140960795 + 4482354 * 2 ^ 59
def prefixEnd_4482354 : Nat := 4983230072969 + 3 ^ 40 * 4482354 * 2
def baseEnd_4482354 : Nat := 2301602065603261003061035

theorem tailTrace_4482354 : CollatzResearch.WordTrace tailWord_4482354 prefixEnd_4482354 2301602065603261003061035 := by
  unfold tailWord_4482354
  simp only [CollatzResearch.WordTrace]
  refine ⟨40871220300801114490435529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108989920802136305307828077 40871220300801114490435529)
  ·
    refine ⟨30653415225600835867826647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40871220300801114490435529 30653415225600835867826647)
    ·
      refine ⟨45980122838401253801739971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30653415225600835867826647 45980122838401253801739971)
      ·
        refine ⟨68970184257601880702609957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45980122838401253801739971 68970184257601880702609957)
        ·
          refine ⟨12931909548300352631739367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68970184257601880702609957 12931909548300352631739367)
          ·
            refine ⟨19397864322450528947609051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12931909548300352631739367 19397864322450528947609051)
            ·
              refine ⟨29096796483675793421413577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19397864322450528947609051 29096796483675793421413577)
              ·
                refine ⟨21822597362756845066060183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29096796483675793421413577 21822597362756845066060183)
                ·
                  refine ⟨32733896044135267599090275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21822597362756845066060183 32733896044135267599090275)
                  ·
                    refine ⟨49100844066202901398635413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32733896044135267599090275 49100844066202901398635413)
                    ·
                      refine ⟨2301602065603261003061035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49100844066202901398635413 2301602065603261003061035)
                      ·
                        rfl

theorem cell23_4482354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_4482354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482354 prefixEnd_4482354 := by exact prefixLift 4482354
  have htrace : WordTrace (prefixWord ++ tailWord_4482354) baseStart_4482354 baseEnd_4482354 := by
    simpa [prefixWord, tailWord_4482354, baseEnd_4482354] using wordTrace_append hprefix tailTrace_4482354
  have hstable : (prefixWord ++ tailWord_4482354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482354).length < 2 ^ (prefixWord ++ tailWord_4482354).sum := by decide
  have hdescent : baseEnd_4482354 < baseStart_4482354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482364 : List Nat := [2, 2, 2, 2, 1, 4, 2, 8]
def baseStart_4482364 : Nat := 118140960795 + 4482364 * 2 ^ 59
def prefixEnd_4482364 : Nat := 4983230072969 + 3 ^ 40 * 4482364 * 2
def baseEnd_4482364 : Nat := 85244711126289109775407

theorem tailTrace_4482364 : CollatzResearch.WordTrace tailWord_4482364 prefixEnd_4482364 85244711126289109775407 := by
  unfold tailWord_4482364
  simp only [CollatzResearch.WordTrace]
  refine ⟨81742622966584114834803073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108990163955445486446404097 81742622966584114834803073)
  ·
    refine ⟨61306967224938086126102305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81742622966584114834803073 61306967224938086126102305)
    ·
      refine ⟨45980225418703564594576729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61306967224938086126102305 45980225418703564594576729)
      ·
        refine ⟨34485169064027673445932547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45980225418703564594576729 34485169064027673445932547)
        ·
          refine ⟨51727753596041510168898821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34485169064027673445932547 51727753596041510168898821)
          ·
            refine ⟨9698953799257783156668529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51727753596041510168898821 9698953799257783156668529)
            ·
              refine ⟨7274215349443337367501397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9698953799257783156668529 7274215349443337367501397)
              ·
                refine ⟨85244711126289109775407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7274215349443337367501397 85244711126289109775407)
                ·
                  rfl

theorem cell23_4482364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 8].length) (baseStart_4482364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482364 prefixEnd_4482364 := by exact prefixLift 4482364
  have htrace : WordTrace (prefixWord ++ tailWord_4482364) baseStart_4482364 baseEnd_4482364 := by
    simpa [prefixWord, tailWord_4482364, baseEnd_4482364] using wordTrace_append hprefix tailTrace_4482364
  have hstable : (prefixWord ++ tailWord_4482364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482364).length < 2 ^ (prefixWord ++ tailWord_4482364).sum := by decide
  have hdescent : baseEnd_4482364 < baseStart_4482364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482391 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_4482391 : Nat := 118140960795 + 4482391 * 2 ^ 59
def prefixEnd_4482391 : Nat := 4983230072969 + 3 ^ 40 * 4482391 * 2
def baseEnd_4482391 : Nat := 2301621064387477358298365

theorem tailTrace_4482391 : CollatzResearch.WordTrace tailWord_4482391 prefixEnd_4482391 2301621064387477358298365 := by
  unfold tailWord_4482391
  simp only [CollatzResearch.WordTrace]
  refine ⟨163486230704070413280839027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108990820469380275520559351 163486230704070413280839027)
  ·
    refine ⟨245229346056105619921258541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163486230704070413280839027 245229346056105619921258541)
    ·
      refine ⟨91961004771039607470471953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 245229346056105619921258541 91961004771039607470471953)
      ·
        refine ⟨68970753578279705602853965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91961004771039607470471953 68970753578279705602853965)
        ·
          refine ⟨25864032591854889601070237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68970753578279705602853965 25864032591854889601070237)
          ·
            refine ⟨9699012221945583600401339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25864032591854889601070237 9699012221945583600401339)
            ·
              refine ⟨14548518332918375400602009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9699012221945583600401339 14548518332918375400602009)
              ·
                refine ⟨10911388749688781550451507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14548518332918375400602009 10911388749688781550451507)
                ·
                  refine ⟨16367083124533172325677261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10911388749688781550451507 16367083124533172325677261)
                  ·
                    refine ⟨6137656171699939622128973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16367083124533172325677261 6137656171699939622128973)
                    ·
                      refine ⟨2301621064387477358298365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6137656171699939622128973 2301621064387477358298365)
                      ·
                        rfl

theorem cell23_4482391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_4482391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482391 prefixEnd_4482391 := by exact prefixLift 4482391
  have htrace : WordTrace (prefixWord ++ tailWord_4482391) baseStart_4482391 baseEnd_4482391 := by
    simpa [prefixWord, tailWord_4482391, baseEnd_4482391] using wordTrace_append hprefix tailTrace_4482391
  have hstable : (prefixWord ++ tailWord_4482391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482391).length < 2 ^ (prefixWord ++ tailWord_4482391).sum := by decide
  have hdescent : baseEnd_4482391 < baseStart_4482391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482444 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_4482444 : Nat := 118140960795 + 4482444 * 2 ^ 59
def prefixEnd_4482444 : Nat := 4983230072969 + 3 ^ 40 * 4482444 * 2
def baseEnd_4482444 : Nat := 2301648278862165650935621

theorem tailTrace_4482444 : CollatzResearch.WordTrace tailWord_4482444 prefixEnd_4482444 2301648278862165650935621 := by
  unfold tailWord_4482444
  simp only [CollatzResearch.WordTrace]
  refine ⟨81744081886439201666259193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108992109181918935555012257 81744081886439201666259193)
  ·
    refine ⟨61308061414829401249694395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81744081886439201666259193 61308061414829401249694395)
    ·
      refine ⟨91962092122244101874541593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61308061414829401249694395 91962092122244101874541593)
      ·
        refine ⟨68971569091683076405906195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91962092122244101874541593 68971569091683076405906195)
        ·
          refine ⟨103457353637524614608859293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68971569091683076405906195 103457353637524614608859293)
          ·
            refine ⟨38796507614071730478322235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103457353637524614608859293 38796507614071730478322235)
            ·
              refine ⟨58194761421107595717483353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38796507614071730478322235 58194761421107595717483353)
              ·
                refine ⟨43646071065830696788112515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58194761421107595717483353 43646071065830696788112515)
                ·
                  refine ⟨65469106598746045182168773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43646071065830696788112515 65469106598746045182168773)
                  ·
                    refine ⟨12275457487264883471656645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65469106598746045182168773 12275457487264883471656645)
                    ·
                      refine ⟨2301648278862165650935621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12275457487264883471656645 2301648278862165650935621)
                      ·
                        rfl

theorem cell23_4482444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_4482444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482444 prefixEnd_4482444 := by exact prefixLift 4482444
  have htrace : WordTrace (prefixWord ++ tailWord_4482444) baseStart_4482444 baseEnd_4482444 := by
    simpa [prefixWord, tailWord_4482444, baseEnd_4482444] using wordTrace_append hprefix tailTrace_4482444
  have hstable : (prefixWord ++ tailWord_4482444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482444).length < 2 ^ (prefixWord ++ tailWord_4482444).sum := by decide
  have hdescent : baseEnd_4482444 < baseStart_4482444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482452 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_4482452 : Nat := 118140960795 + 4482452 * 2 ^ 59
def prefixEnd_4482452 : Nat := 4983230072969 + 3 ^ 40 * 4482452 * 2
def baseEnd_4482452 : Nat := 2301652386707401619635585

theorem tailTrace_4482452 : CollatzResearch.WordTrace tailWord_4482452 prefixEnd_4482452 2301652386707401619635585 := by
  unfold tailWord_4482452
  simp only [CollatzResearch.WordTrace]
  refine ⟨81744227778424710349404805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108992303704566280465873073 81744227778424710349404805)
  ·
    refine ⟨15327042708454633190513401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81744227778424710349404805 15327042708454633190513401)
    ·
      refine ⟨11495282031340974892885051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15327042708454633190513401 11495282031340974892885051)
      ·
        refine ⟨17242923047011462339327577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11495282031340974892885051 17242923047011462339327577)
        ·
          refine ⟨12932192285258596754495683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17242923047011462339327577 12932192285258596754495683)
          ·
            refine ⟨19398288427887895131743525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12932192285258596754495683 19398288427887895131743525)
            ·
              refine ⟨3637179080228980337201911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19398288427887895131743525 3637179080228980337201911)
              ·
                refine ⟨5455768620343470505802867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3637179080228980337201911 5455768620343470505802867)
                ·
                  refine ⟨8183652930515205758704301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5455768620343470505802867 8183652930515205758704301)
                  ·
                    refine ⟨3068869848943202159514113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8183652930515205758704301 3068869848943202159514113)
                    ·
                      refine ⟨2301652386707401619635585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3068869848943202159514113 2301652386707401619635585)
                      ·
                        rfl

theorem cell23_4482452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_4482452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482452 prefixEnd_4482452 := by exact prefixLift 4482452
  have htrace : WordTrace (prefixWord ++ tailWord_4482452) baseStart_4482452 baseEnd_4482452 := by
    simpa [prefixWord, tailWord_4482452, baseEnd_4482452] using wordTrace_append hprefix tailTrace_4482452
  have hstable : (prefixWord ++ tailWord_4482452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482452).length < 2 ^ (prefixWord ++ tailWord_4482452).sum := by decide
  have hdescent : baseEnd_4482452 < baseStart_4482452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482461 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4482461 : Nat := 118140960795 + 4482461 * 2 ^ 59
def prefixEnd_4482461 : Nat := 4983230072969 + 3 ^ 40 * 4482461 * 2
def baseEnd_4482461 : Nat := 2301657008033292084423043

theorem tailTrace_4482461 : CollatzResearch.WordTrace tailWord_4482461 prefixEnd_4482461 2301657008033292084423043 := by
  unfold tailWord_4482461
  simp only [CollatzResearch.WordTrace]
  refine ⟨163488783813816815235887237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108992522542544543490591491 163488783813816815235887237)
  ·
    refine ⟨30654146965090652856728857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163488783813816815235887237 30654146965090652856728857)
    ·
      refine ⟨22990610223817989642546643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30654146965090652856728857 22990610223817989642546643)
      ·
        refine ⟨34485915335726984463819965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22990610223817989642546643 34485915335726984463819965)
        ·
          refine ⟨12932218250897619173932487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34485915335726984463819965 12932218250897619173932487)
          ·
            refine ⟨19398327376346428760898731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12932218250897619173932487 19398327376346428760898731)
            ·
              refine ⟨29097491064519643141348097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19398327376346428760898731 29097491064519643141348097)
              ·
                refine ⟨21823118298389732356011073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29097491064519643141348097 21823118298389732356011073)
                ·
                  refine ⟨16367338723792299267008305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21823118298389732356011073 16367338723792299267008305)
                  ·
                    refine ⟨12275504042844224450256229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16367338723792299267008305 12275504042844224450256229)
                    ·
                      refine ⟨2301657008033292084423043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12275504042844224450256229 2301657008033292084423043)
                      ·
                        rfl

theorem cell23_4482461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4482461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482461 prefixEnd_4482461 := by exact prefixLift 4482461
  have htrace : WordTrace (prefixWord ++ tailWord_4482461) baseStart_4482461 baseEnd_4482461 := by
    simpa [prefixWord, tailWord_4482461, baseEnd_4482461] using wordTrace_append hprefix tailTrace_4482461
  have hstable : (prefixWord ++ tailWord_4482461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482461).length < 2 ^ (prefixWord ++ tailWord_4482461).sum := by decide
  have hdescent : baseEnd_4482461 < baseStart_4482461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4482471 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 7]
def baseStart_4482471 : Nat := 118140960795 + 4482471 * 2 ^ 59
def prefixEnd_4482471 : Nat := 4983230072969 + 3 ^ 40 * 4482471 * 2
def baseEnd_4482471 : Nat := 255740238093315227255333

theorem tailTrace_4482471 : CollatzResearch.WordTrace tailWord_4482471 prefixEnd_4482471 255740238093315227255333 := by
  unfold tailWord_4482471
  simp only [CollatzResearch.WordTrace]
  refine ⟨163489148543780586943751267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108992765695853724629167511 163489148543780586943751267)
  ·
    refine ⟨245233722815670880415626901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163489148543780586943751267 245233722815670880415626901)
    ·
      refine ⟨11495330756984572519482511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 245233722815670880415626901 11495330756984572519482511)
      ·
        refine ⟨17242996135476858779223767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11495330756984572519482511 17242996135476858779223767)
        ·
          refine ⟨25864494203215288168835651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17242996135476858779223767 25864494203215288168835651)
          ·
            refine ⟨38796741304822932253253477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25864494203215288168835651 38796741304822932253253477)
            ·
              refine ⟨7274388994654299797485027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38796741304822932253253477 7274388994654299797485027)
              ·
                refine ⟨10911583491981449696227541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7274388994654299797485027 10911583491981449696227541)
                ·
                  refine ⟨255740238093315227255333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10911583491981449696227541 255740238093315227255333)
                  ·
                    rfl

theorem cell23_4482471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 7].length) (baseStart_4482471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4482471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4482471 prefixEnd_4482471 := by exact prefixLift 4482471
  have htrace : WordTrace (prefixWord ++ tailWord_4482471) baseStart_4482471 baseEnd_4482471 := by
    simpa [prefixWord, tailWord_4482471, baseEnd_4482471] using wordTrace_append hprefix tailTrace_4482471
  have hstable : (prefixWord ++ tailWord_4482471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4482471).length < 2 ^ (prefixWord ++ tailWord_4482471).sum := by decide
  have hdescent : baseEnd_4482471 < baseStart_4482471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4482471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
