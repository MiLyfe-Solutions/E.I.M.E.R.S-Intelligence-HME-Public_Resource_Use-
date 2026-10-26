import V185TrunkScan22Chunk279

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2495640 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_2495640 : Nat := 118140960795 + 2495640 * 2 ^ 59
def prefixEnd_2495640 : Nat := 4983230072969 + 3 ^ 40 * 2495640 * 2
def baseEnd_2495640 : Nat := 854308573724480687148511

theorem tailTrace_2495640 : CollatzResearch.WordTrace tailWord_2495640 prefixEnd_2495640 854308573724480687148511 := by
  unfold tailWord_2495640
  simp only [CollatzResearch.WordTrace]
  refine ⟨45511734339364988111946187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60682312452486650815928249 45511734339364988111946187)
  ·
    refine ⟨68267601509047482167919281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45511734339364988111946187 68267601509047482167919281)
    ·
      refine ⟨51200701131785611625939461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68267601509047482167919281 51200701131785611625939461)
      ·
        refine ⟨9600131462209802179863649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51200701131785611625939461 9600131462209802179863649)
        ·
          refine ⟨7200098596657351634897737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9600131462209802179863649 7200098596657351634897737)
          ·
            refine ⟨5400073947493013726173303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7200098596657351634897737 5400073947493013726173303)
            ·
              refine ⟨8100110921239520589259955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5400073947493013726173303 8100110921239520589259955)
              ·
                refine ⟨12150166381859280883889933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8100110921239520589259955 12150166381859280883889933)
                ·
                  refine ⟨4556312393197230331458725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12150166381859280883889933 4556312393197230331458725)
                  ·
                    refine ⟨854308573724480687148511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4556312393197230331458725 854308573724480687148511)
                    ·
                      rfl

theorem cell22_2495640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_2495640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495640 prefixEnd_2495640 := by exact prefixLift 2495640
  have htrace : WordTrace (prefixWord ++ tailWord_2495640) baseStart_2495640 baseEnd_2495640 := by
    simpa [prefixWord, tailWord_2495640, baseEnd_2495640] using wordTrace_append hprefix tailTrace_2495640
  have hstable : (prefixWord ++ tailWord_2495640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495640).length < 2 ^ (prefixWord ++ tailWord_2495640).sum := by decide
  have hdescent : baseEnd_2495640 < baseStart_2495640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495653 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_2495653 : Nat := 118140960795 + 2495653 * 2 ^ 59
def prefixEnd_2495653 : Nat := 4983230072969 + 3 ^ 40 * 2495653 * 2
def baseEnd_2495653 : Nat := 854313023890152986573471

theorem tailTrace_2495653 : CollatzResearch.WordTrace tailWord_2495653 prefixEnd_2495653 854313023890152986573471 := by
  unfold tailWord_2495653
  simp only [CollatzResearch.WordTrace]
  refine ⟨91023942827682879444115613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60682628551788586296077075 91023942827682879444115613)
  ·
    refine ⟨34133978560381079791543355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91023942827682879444115613 34133978560381079791543355)
    ·
      refine ⟨51200967840571619687315033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34133978560381079791543355 51200967840571619687315033)
      ·
        refine ⟨38400725880428714765486275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51200967840571619687315033 38400725880428714765486275)
        ·
          refine ⟨57601088820643072148229413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38400725880428714765486275 57601088820643072148229413)
          ·
            refine ⟨10800204153870576027793015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57601088820643072148229413 10800204153870576027793015)
            ·
              refine ⟨16200306230805864041689523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10800204153870576027793015 16200306230805864041689523)
              ·
                refine ⟨24300459346208796062534285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16200306230805864041689523 24300459346208796062534285)
                ·
                  refine ⟨9112672254828298523450357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24300459346208796062534285 9112672254828298523450357)
                  ·
                    refine ⟨854313023890152986573471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9112672254828298523450357 854313023890152986573471)
                    ·
                      rfl

theorem cell22_2495653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_2495653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495653 prefixEnd_2495653 := by exact prefixLift 2495653
  have htrace : WordTrace (prefixWord ++ tailWord_2495653) baseStart_2495653 baseEnd_2495653 := by
    simpa [prefixWord, tailWord_2495653, baseEnd_2495653] using wordTrace_append hprefix tailTrace_2495653
  have hstable : (prefixWord ++ tailWord_2495653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495653).length < 2 ^ (prefixWord ++ tailWord_2495653).sum := by decide
  have hdescent : baseEnd_2495653 < baseStart_2495653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495809 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2495809 : Nat := 118140960795 + 2495809 * 2 ^ 59
def prefixEnd_2495809 : Nat := 4983230072969 + 3 ^ 40 * 2495809 * 2
def baseEnd_2495809 : Nat := 854366425878220579672993

theorem tailTrace_2495809 : CollatzResearch.WordTrace tailWord_2495809 prefixEnd_2495809 854366425878220579672993 := by
  unfold tailWord_2495809
  simp only [CollatzResearch.WordTrace]
  refine ⟨91029632615117718086794481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60686421743411812057862987 91029632615117718086794481)
  ·
    refine ⟨68272224461338288565095861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91029632615117718086794481 68272224461338288565095861)
    ·
      refine ⟨6400521043250464552977737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68272224461338288565095861 6400521043250464552977737)
      ·
        refine ⟨4800390782437848414733303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6400521043250464552977737 4800390782437848414733303)
        ·
          refine ⟨7200586173656772622099955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800390782437848414733303 7200586173656772622099955)
          ·
            refine ⟨10800879260485158933149933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7200586173656772622099955 10800879260485158933149933)
            ·
              refine ⟨4050329722681934599931225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10800879260485158933149933 4050329722681934599931225)
              ·
                refine ⟨3037747292011450949948419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050329722681934599931225 3037747292011450949948419)
                ·
                  refine ⟨4556620938017176424922629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037747292011450949948419 4556620938017176424922629)
                  ·
                    refine ⟨854366425878220579672993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4556620938017176424922629 854366425878220579672993)
                    ·
                      rfl

theorem cell22_2495809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2495809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495809 prefixEnd_2495809 := by exact prefixLift 2495809
  have htrace : WordTrace (prefixWord ++ tailWord_2495809) baseStart_2495809 baseEnd_2495809 := by
    simpa [prefixWord, tailWord_2495809, baseEnd_2495809] using wordTrace_append hprefix tailTrace_2495809
  have hstable : (prefixWord ++ tailWord_2495809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495809).length < 2 ^ (prefixWord ++ tailWord_2495809).sum := by decide
  have hdescent : baseEnd_2495809 < baseStart_2495809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495852 : List Nat := [2, 2, 1, 1, 5, 3, 1, 7]
def baseStart_2495852 : Nat := 118140960795 + 2495852 * 2 ^ 59
def prefixEnd_2495852 : Nat := 4983230072969 + 3 ^ 40 * 2495852 * 2
def baseEnd_2495852 : Nat := 94931238406331422316429

theorem tailTrace_2495852 : CollatzResearch.WordTrace tailWord_2495852 prefixEnd_2495852 94931238406331422316429 := by
  unfold tailWord_2495852
  simp only [CollatzResearch.WordTrace]
  refine ⟨45515600476980968215304905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60687467302641290953739873 45515600476980968215304905)
  ·
    refine ⟨34136700357735726161478679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45515600476980968215304905 34136700357735726161478679)
    ·
      refine ⟨51205050536603589242218019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34136700357735726161478679 51205050536603589242218019)
      ·
        refine ⟨76807575804905383863327029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51205050536603589242218019 76807575804905383863327029)
        ·
          refine ⟨7200710231709879737186909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76807575804905383863327029 7200710231709879737186909)
          ·
            refine ⟨2700266336891204901445091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7200710231709879737186909 2700266336891204901445091)
            ·
              refine ⟨4050399505336807352167637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700266336891204901445091 4050399505336807352167637)
              ·
                refine ⟨94931238406331422316429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4050399505336807352167637 94931238406331422316429)
                ·
                  rfl

theorem cell22_2495852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 7].length) (baseStart_2495852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495852 prefixEnd_2495852 := by exact prefixLift 2495852
  have htrace : WordTrace (prefixWord ++ tailWord_2495852) baseStart_2495852 baseEnd_2495852 := by
    simpa [prefixWord, tailWord_2495852, baseEnd_2495852] using wordTrace_append hprefix tailTrace_2495852
  have hstable : (prefixWord ++ tailWord_2495852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495852).length < 2 ^ (prefixWord ++ tailWord_2495852).sum := by decide
  have hdescent : baseEnd_2495852 < baseStart_2495852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495867 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 3, 3]
def baseStart_2495867 : Nat := 118140960795 + 2495867 * 2 ^ 59
def prefixEnd_2495867 : Nat := 4983230072969 + 3 ^ 40 * 2495867 * 2
def baseEnd_2495867 : Nat := 854386280463527761722815

theorem tailTrace_2495867 : CollatzResearch.WordTrace tailWord_2495867 prefixEnd_2495867 854386280463527761722815 := by
  unfold tailWord_2495867
  simp only [CollatzResearch.WordTrace]
  refine ⟨91031748048907593992405855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60687832032605062661603903 91031748048907593992405855)
  ·
    refine ⟨136547622073361390988608783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91031748048907593992405855 136547622073361390988608783)
    ·
      refine ⟨204821433110042086482913175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136547622073361390988608783 204821433110042086482913175)
      ·
        refine ⟨307232149665063129724369763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204821433110042086482913175 307232149665063129724369763)
        ·
          refine ⟨460848224497594694586554645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307232149665063129724369763 460848224497594694586554645)
          ·
            refine ⟨21602260523324751308744749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 460848224497594694586554645 21602260523324751308744749)
            ·
              refine ⟨8100847696246781740779281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21602260523324751308744749 8100847696246781740779281)
              ·
                refine ⟨6075635772185086305584461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8100847696246781740779281 6075635772185086305584461)
                ·
                  refine ⟨2278363414569407364594173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6075635772185086305584461 2278363414569407364594173)
                  ·
                    refine ⟨854386280463527761722815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2278363414569407364594173 854386280463527761722815)
                    ·
                      rfl

theorem cell22_2495867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 3].length) (baseStart_2495867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495867 prefixEnd_2495867 := by exact prefixLift 2495867
  have htrace : WordTrace (prefixWord ++ tailWord_2495867) baseStart_2495867 baseEnd_2495867 := by
    simpa [prefixWord, tailWord_2495867, baseEnd_2495867] using wordTrace_append hprefix tailTrace_2495867
  have hstable : (prefixWord ++ tailWord_2495867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495867).length < 2 ^ (prefixWord ++ tailWord_2495867).sum := by decide
  have hdescent : baseEnd_2495867 < baseStart_2495867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495890 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2495890 : Nat := 118140960795 + 2495890 * 2 ^ 59
def prefixEnd_2495890 : Nat := 4983230072969 + 3 ^ 40 * 2495890 * 2
def baseEnd_2495890 : Nat := 854394153833563368397745

theorem tailTrace_2495890 : CollatzResearch.WordTrace tailWord_2495890 prefixEnd_2495890 854394153833563368397745 := by
  unfold tailWord_2495890
  simp only [CollatzResearch.WordTrace]
  refine ⟨22758146731956067230123281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60688391285216179280328749 22758146731956067230123281)
  ·
    refine ⟨17068610048967050422592461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22758146731956067230123281 17068610048967050422592461)
    ·
      refine ⟨6400728768362643908472173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17068610048967050422592461 6400728768362643908472173)
      ·
        refine ⟨2400273288135991465677065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6400728768362643908472173 2400273288135991465677065)
        ·
          refine ⟨1800204966101993599257799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2400273288135991465677065 1800204966101993599257799)
          ·
            refine ⟨2700307449152990398886699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800204966101993599257799 2700307449152990398886699)
            ·
              refine ⟨4050461173729485598330049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700307449152990398886699 4050461173729485598330049)
              ·
                refine ⟨3037845880297114198747537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050461173729485598330049 3037845880297114198747537)
                ·
                  refine ⟨2278384410222835649060653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037845880297114198747537 2278384410222835649060653)
                  ·
                    refine ⟨854394153833563368397745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2278384410222835649060653 854394153833563368397745)
                    ·
                      rfl

theorem cell22_2495890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2495890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495890 prefixEnd_2495890 := by exact prefixLift 2495890
  have htrace : WordTrace (prefixWord ++ tailWord_2495890) baseStart_2495890 baseEnd_2495890 := by
    simpa [prefixWord, tailWord_2495890, baseEnd_2495890] using wordTrace_append hprefix tailTrace_2495890
  have hstable : (prefixWord ++ tailWord_2495890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495890).length < 2 ^ (prefixWord ++ tailWord_2495890).sum := by decide
  have hdescent : baseEnd_2495890 < baseStart_2495890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495897 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 5]
def baseStart_2495897 : Nat := 118140960795 + 2495897 * 2 ^ 59
def prefixEnd_2495897 : Nat := 4983230072969 + 3 ^ 40 * 2495897 * 2
def baseEnd_2495897 : Nat := 284798850025539227824241

theorem tailTrace_2495897 : CollatzResearch.WordTrace tailWord_2495897 prefixEnd_2495897 284798850025539227824241 := by
  unfold tailWord_2495897
  simp only [CollatzResearch.WordTrace]
  refine ⟨91032842238798909115997945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60688561492532606077331963 91032842238798909115997945)
  ·
    refine ⟨68274631679099181836998459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91032842238798909115997945 68274631679099181836998459)
    ·
      refine ⟨102411947518648772755497689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68274631679099181836998459 102411947518648772755497689)
      ·
        refine ⟨76808960638986579566623267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102411947518648772755497689 76808960638986579566623267)
        ·
          refine ⟨115213440958479869349934901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76808960638986579566623267 115213440958479869349934901)
          ·
            refine ⟨10801260089857487751556397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115213440958479869349934901 10801260089857487751556397)
            ·
              refine ⟨4050472533696557906833649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10801260089857487751556397 4050472533696557906833649)
              ·
                refine ⟨3037854400272418430125237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050472533696557906833649 3037854400272418430125237)
                ·
                  refine ⟨284798850025539227824241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3037854400272418430125237 284798850025539227824241)
                  ·
                    rfl

theorem cell22_2495897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_2495897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495897 prefixEnd_2495897 := by exact prefixLift 2495897
  have htrace : WordTrace (prefixWord ++ tailWord_2495897) baseStart_2495897 baseEnd_2495897 := by
    simpa [prefixWord, tailWord_2495897, baseEnd_2495897] using wordTrace_append hprefix tailTrace_2495897
  have hstable : (prefixWord ++ tailWord_2495897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495897).length < 2 ^ (prefixWord ++ tailWord_2495897).sum := by decide
  have hdescent : baseEnd_2495897 < baseStart_2495897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495901 : List Nat := [1, 4, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2495901 : Nat := 118140960795 + 2495901 * 2 ^ 59
def prefixEnd_2495901 : Nat := 4983230072969 + 3 ^ 40 * 2495901 * 2
def baseEnd_2495901 : Nat := 854397919358363006372711

theorem tailTrace_2495901 : CollatzResearch.WordTrace tailWord_2495901 prefixEnd_2495901 854397919358363006372711 := by
  unfold tailWord_2495901
  simp only [CollatzResearch.WordTrace]
  refine ⟨91032988130784417799143557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60688658753856278532762371 91032988130784417799143557)
  ·
    refine ⟨17068685274522078337339417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91032988130784417799143557 17068685274522078337339417)
    ·
      refine ⟨12801513955891558753004563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17068685274522078337339417 12801513955891558753004563)
      ·
        refine ⟨19202270933837338129506845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12801513955891558753004563 19202270933837338129506845)
        ·
          refine ⟨7200851600189001798565067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19202270933837338129506845 7200851600189001798565067)
          ·
            refine ⟨10801277400283502697847601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7200851600189001798565067 10801277400283502697847601)
            ·
              refine ⟨8100958050212627023385701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10801277400283502697847601 8100958050212627023385701)
              ·
                refine ⟨1518929634414867566884819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8100958050212627023385701 1518929634414867566884819)
                ·
                  refine ⟨2278394451622301350327229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518929634414867566884819 2278394451622301350327229)
                  ·
                    refine ⟨854397919358363006372711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2278394451622301350327229 854397919358363006372711)
                    ·
                      rfl

theorem cell22_2495901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2495901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495901 prefixEnd_2495901 := by exact prefixLift 2495901
  have htrace : WordTrace (prefixWord ++ tailWord_2495901) baseStart_2495901 baseEnd_2495901 := by
    simpa [prefixWord, tailWord_2495901, baseEnd_2495901] using wordTrace_append hprefix tailTrace_2495901
  have hstable : (prefixWord ++ tailWord_2495901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495901).length < 2 ^ (prefixWord ++ tailWord_2495901).sum := by decide
  have hdescent : baseEnd_2495901 < baseStart_2495901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2495978 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_2495978 : Nat := 118140960795 + 2495978 * 2 ^ 59
def prefixEnd_2495978 : Nat := 4983230072969 + 3 ^ 40 * 2495978 * 2
def baseEnd_2495978 : Nat := 854424278031960472197475

theorem tailTrace_2495978 : CollatzResearch.WordTrace tailWord_2495978 prefixEnd_2495978 854424278031960472197475 := by
  unfold tailWord_2495978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22758949137876364987424147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60690531034336973299797725 22758949137876364987424147)
  ·
    refine ⟨34138423706814547481136221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22758949137876364987424147 34138423706814547481136221)
    ·
      refine ⟨12801908890055455305426083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34138423706814547481136221 12801908890055455305426083)
      ·
        refine ⟨19202863335083182958139125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12801908890055455305426083 19202863335083182958139125)
        ·
          refine ⟨1800268437664048402325543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19202863335083182958139125 1800268437664048402325543)
          ·
            refine ⟨2700402656496072603488315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800268437664048402325543 2700402656496072603488315)
            ·
              refine ⟨4050603984744108905232473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700402656496072603488315 4050603984744108905232473)
              ·
                refine ⟨3037952988558081678924355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050603984744108905232473 3037952988558081678924355)
                ·
                  refine ⟨4556929482837122518386533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037952988558081678924355 4556929482837122518386533)
                  ·
                    refine ⟨854424278031960472197475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4556929482837122518386533 854424278031960472197475)
                    ·
                      rfl

theorem cell22_2495978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_2495978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2495978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2495978 prefixEnd_2495978 := by exact prefixLift 2495978
  have htrace : WordTrace (prefixWord ++ tailWord_2495978) baseStart_2495978 baseEnd_2495978 := by
    simpa [prefixWord, tailWord_2495978, baseEnd_2495978] using wordTrace_append hprefix tailTrace_2495978
  have hstable : (prefixWord ++ tailWord_2495978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2495978).length < 2 ^ (prefixWord ++ tailWord_2495978).sum := by decide
  have hdescent : baseEnd_2495978 < baseStart_2495978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2495978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496004 : List Nat := [2, 3, 2, 3, 3, 9]
def baseStart_2496004 : Nat := 118140960795 + 2496004 * 2 ^ 59
def prefixEnd_2496004 : Nat := 4983230072969 + 3 ^ 40 * 2496004 * 2
def baseEnd_2496004 : Nat := 10548557757571667543795

theorem tailTrace_2496004 : CollatzResearch.WordTrace tailWord_2496004 prefixEnd_2496004 10548557757571667543795 := by
  unfold tailWord_2496004
  simp only [CollatzResearch.WordTrace]
  refine ⟨45518372424705633195071533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60691163232940844260095377 45518372424705633195071533)
  ·
    refine ⟨17069389659264612448151825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45518372424705633195071533 17069389659264612448151825)
    ·
      refine ⟨12802042244448459336113869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17069389659264612448151825 12802042244448459336113869)
      ·
        refine ⟨4800765841668172251042701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12802042244448459336113869 4800765841668172251042701)
        ·
          refine ⟨1800287190625564594141013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4800765841668172251042701 1800287190625564594141013)
          ·
            refine ⟨10548557757571667543795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1800287190625564594141013 10548557757571667543795)
            ·
              rfl

theorem cell22_2496004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 9].length) (baseStart_2496004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496004 prefixEnd_2496004 := by exact prefixLift 2496004
  have htrace : WordTrace (prefixWord ++ tailWord_2496004) baseStart_2496004 baseEnd_2496004 := by
    simpa [prefixWord, tailWord_2496004, baseEnd_2496004] using wordTrace_append hprefix tailTrace_2496004
  have hstable : (prefixWord ++ tailWord_2496004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496004).length < 2 ^ (prefixWord ++ tailWord_2496004).sum := by decide
  have hdescent : baseEnd_2496004 < baseStart_2496004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496053 : List Nat := [1, 3, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2496053 : Nat := 118140960795 + 2496053 * 2 ^ 59
def prefixEnd_2496053 : Nat := 4983230072969 + 3 ^ 40 * 2496053 * 2
def baseEnd_2496053 : Nat := 854449952064685276572245

theorem tailTrace_2496053 : CollatzResearch.WordTrace tailWord_2496053 prefixEnd_2496053 854449952064685276572245 := by
  unfold tailWord_2496053
  simp only [CollatzResearch.WordTrace]
  refine ⟨91038532026233747758676813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60692354684155831839117875 91038532026233747758676813)
  ·
    refine ⟨34139449509837655409503805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91038532026233747758676813 34139449509837655409503805)
    ·
      refine ⟨12802293566189120778563927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34139449509837655409503805 12802293566189120778563927)
      ·
        refine ⟨19203440349283681167845891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12802293566189120778563927 19203440349283681167845891)
        ·
          refine ⟨28805160523925521751768837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19203440349283681167845891 28805160523925521751768837)
          ·
            refine ⟨5400967598236035328456657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28805160523925521751768837 5400967598236035328456657)
            ·
              refine ⟨4050725698677026496342493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5400967598236035328456657 4050725698677026496342493)
              ·
                refine ⟨1519022137003884936128435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4050725698677026496342493 1519022137003884936128435)
                ·
                  refine ⟨2278533205505827404192653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519022137003884936128435 2278533205505827404192653)
                  ·
                    refine ⟨854449952064685276572245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2278533205505827404192653 854449952064685276572245)
                    ·
                      rfl

theorem cell22_2496053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2496053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496053 prefixEnd_2496053 := by exact prefixLift 2496053
  have htrace : WordTrace (prefixWord ++ tailWord_2496053) baseStart_2496053 baseEnd_2496053 := by
    simpa [prefixWord, tailWord_2496053, baseEnd_2496053] using wordTrace_append hprefix tailTrace_2496053
  have hstable : (prefixWord ++ tailWord_2496053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496053).length < 2 ^ (prefixWord ++ tailWord_2496053).sum := by decide
  have hdescent : baseEnd_2496053 < baseStart_2496053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496070 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2496070 : Nat := 118140960795 + 2496070 * 2 ^ 59
def prefixEnd_2496070 : Nat := 4983230072969 + 3 ^ 40 * 2496070 * 2
def baseEnd_2496070 : Nat := 854455771512102898897193

theorem tailTrace_2496070 : CollatzResearch.WordTrace tailWord_2496070 prefixEnd_2496070 854455771512102898897193 := by
  unfold tailWord_2496070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2844973502099129989438927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60692768044781439774697109 2844973502099129989438927)
  ·
    refine ⟨4267460253148694984158391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2844973502099129989438927 4267460253148694984158391)
    ·
      refine ⟨6401190379723042476237587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267460253148694984158391 6401190379723042476237587)
      ·
        refine ⟨9601785569584563714356381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401190379723042476237587 9601785569584563714356381)
        ·
          refine ⟨3600669588594211392883643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9601785569584563714356381 3600669588594211392883643)
          ·
            refine ⟨5401004382891317089325465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600669588594211392883643 5401004382891317089325465)
            ·
              refine ⟨4050753287168487816994099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5401004382891317089325465 4050753287168487816994099)
              ·
                refine ⟨6076129930752731725491149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050753287168487816994099 6076129930752731725491149)
                ·
                  refine ⟨2278548724032274397059181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6076129930752731725491149 2278548724032274397059181)
                  ·
                    refine ⟨854455771512102898897193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2278548724032274397059181 854455771512102898897193)
                    ·
                      rfl

theorem cell22_2496070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2496070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496070 prefixEnd_2496070 := by exact prefixLift 2496070
  have htrace : WordTrace (prefixWord ++ tailWord_2496070) baseStart_2496070 baseEnd_2496070 := by
    simpa [prefixWord, tailWord_2496070, baseEnd_2496070] using wordTrace_append hprefix tailTrace_2496070
  have hstable : (prefixWord ++ tailWord_2496070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496070).length < 2 ^ (prefixWord ++ tailWord_2496070).sum := by decide
  have hdescent : baseEnd_2496070 < baseStart_2496070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496158 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2496158 : Nat := 118140960795 + 2496158 * 2 ^ 59
def prefixEnd_2496158 : Nat := 4983230072969 + 3 ^ 40 * 2496158 * 2
def baseEnd_2496158 : Nat := 854485895710500002696923

theorem tailTrace_2496158 : CollatzResearch.WordTrace tailWord_2496158 prefixEnd_2496158 854485895710500002696923 := by
  unfold tailWord_2496158
  simp only [CollatzResearch.WordTrace]
  refine ⟨11380295211356668836406141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60694907793902233794166085 11380295211356668836406141)
  ·
    refine ⟨4267610704258750813652303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11380295211356668836406141 4267610704258750813652303)
    ·
      refine ⟨6401416056388126220478455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267610704258750813652303 6401416056388126220478455)
      ·
        refine ⟨9602124084582189330717683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401416056388126220478455 9602124084582189330717683)
        ·
          refine ⟨14403186126873283996076525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9602124084582189330717683 14403186126873283996076525)
          ·
            refine ⟨5401194797577481498528697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14403186126873283996076525 5401194797577481498528697)
            ·
              refine ⟨4050896098183111123896523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5401194797577481498528697 4050896098183111123896523)
              ·
                refine ⟨6076344147274666685844785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050896098183111123896523 6076344147274666685844785)
                ·
                  refine ⟨4557258110456000014383589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6076344147274666685844785 4557258110456000014383589)
                  ·
                    refine ⟨854485895710500002696923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4557258110456000014383589 854485895710500002696923)
                    ·
                      rfl

theorem cell22_2496158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2496158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496158 prefixEnd_2496158 := by exact prefixLift 2496158
  have htrace : WordTrace (prefixWord ++ tailWord_2496158) baseStart_2496158 baseEnd_2496158 := by
    simpa [prefixWord, tailWord_2496158, baseEnd_2496158] using wordTrace_append hprefix tailTrace_2496158
  have hstable : (prefixWord ++ tailWord_2496158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496158).length < 2 ^ (prefixWord ++ tailWord_2496158).sum := by decide
  have hdescent : baseEnd_2496158 < baseStart_2496158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496199 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2496199 : Nat := 118140960795 + 2496199 * 2 ^ 59
def prefixEnd_2496199 : Nat := 4983230072969 + 3 ^ 40 * 2496199 * 2
def baseEnd_2496199 : Nat := 854499930848389562421797

theorem tailTrace_2496199 : CollatzResearch.WordTrace tailWord_2496199 prefixEnd_2496199 854499930848389562421797 := by
  unfold tailWord_2496199
  simp only [CollatzResearch.WordTrace]
  refine ⟨91043857083704814693491651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60695904722469876462327767 91043857083704814693491651)
  ·
    refine ⟨136565785625557222040237477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91043857083704814693491651 136565785625557222040237477)
    ·
      refine ⟨25606084804791979132544527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136565785625557222040237477 25606084804791979132544527)
      ·
        refine ⟨38409127207187968698816791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25606084804791979132544527 38409127207187968698816791)
        ·
          refine ⟨57613690810781953048225187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38409127207187968698816791 57613690810781953048225187)
          ·
            refine ⟨86420536216172929572337781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57613690810781953048225187 86420536216172929572337781)
            ·
              refine ⟨8101925270266212147406667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86420536216172929572337781 8101925270266212147406667)
              ·
                refine ⟨12152887905399318221110001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8101925270266212147406667 12152887905399318221110001)
                ·
                  refine ⟨9114665929049488665832501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12152887905399318221110001 9114665929049488665832501)
                  ·
                    refine ⟨854499930848389562421797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9114665929049488665832501 854499930848389562421797)
                    ·
                      rfl

theorem cell22_2496199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2496199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496199 prefixEnd_2496199 := by exact prefixLift 2496199
  have htrace : WordTrace (prefixWord ++ tailWord_2496199) baseStart_2496199 baseEnd_2496199 := by
    simpa [prefixWord, tailWord_2496199, baseEnd_2496199] using wordTrace_append hprefix tailTrace_2496199
  have hstable : (prefixWord ++ tailWord_2496199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496199).length < 2 ^ (prefixWord ++ tailWord_2496199).sum := by decide
  have hdescent : baseEnd_2496199 < baseStart_2496199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496205 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2496205 : Nat := 118140960795 + 2496205 * 2 ^ 59
def prefixEnd_2496205 : Nat := 4983230072969 + 3 ^ 40 * 2496205 * 2
def baseEnd_2496205 : Nat := 854501984771007546771779

theorem tailTrace_2496205 : CollatzResearch.WordTrace tailWord_2496205 prefixEnd_2496205 854501984771007546771779 := by
  unfold tailWord_2496205
  simp only [CollatzResearch.WordTrace]
  refine ⟨91044075921683077718210069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60696050614455385145473379 91044075921683077718210069)
  ·
    refine ⟨4267691058828894268041097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91044075921683077718210069 4267691058828894268041097)
    ·
      refine ⟨3200768294121670701030823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4267691058828894268041097 3200768294121670701030823)
      ·
        refine ⟨4801152441182506051546235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200768294121670701030823 4801152441182506051546235)
        ·
          refine ⟨7201728661773759077319353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4801152441182506051546235 7201728661773759077319353)
          ·
            refine ⟨5401296496330319307989515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7201728661773759077319353 5401296496330319307989515)
            ·
              refine ⟨8101944744495478961984273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5401296496330319307989515 8101944744495478961984273)
              ·
                refine ⟨6076458558371609221488205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8101944744495478961984273 6076458558371609221488205)
                ·
                  refine ⟨2278671959389353458058077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6076458558371609221488205 2278671959389353458058077)
                  ·
                    refine ⟨854501984771007546771779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2278671959389353458058077 854501984771007546771779)
                    ·
                      rfl

theorem cell22_2496205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2496205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496205 prefixEnd_2496205 := by exact prefixLift 2496205
  have htrace : WordTrace (prefixWord ++ tailWord_2496205) baseStart_2496205 baseEnd_2496205 := by
    simpa [prefixWord, tailWord_2496205, baseEnd_2496205] using wordTrace_append hprefix tailTrace_2496205
  have hstable : (prefixWord ++ tailWord_2496205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496205).length < 2 ^ (prefixWord ++ tailWord_2496205).sum := by decide
  have hdescent : baseEnd_2496205 < baseStart_2496205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496229 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 8]
def baseStart_2496229 : Nat := 118140960795 + 2496229 * 2 ^ 59
def prefixEnd_2496229 : Nat := 4983230072969 + 3 ^ 40 * 2496229 * 2
def baseEnd_2496229 : Nat := 284836733487159828057235

theorem tailTrace_2496229 : CollatzResearch.WordTrace tailWord_2496229 prefixEnd_2496229 284836733487159828057235 := by
  unfold tailWord_2496229
  simp only [CollatzResearch.WordTrace]
  refine ⟨91044951273596129817083741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60696634182397419878055827 91044951273596129817083741)
  ·
    refine ⟨34141856727598548681406403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91044951273596129817083741 34141856727598548681406403)
    ·
      refine ⟨51212785091397823022109605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34141856727598548681406403 51212785091397823022109605)
      ·
        refine ⟨9602397204637091816645551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51212785091397823022109605 9602397204637091816645551)
        ·
          refine ⟨14403595806955637724968327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9602397204637091816645551 14403595806955637724968327)
          ·
            refine ⟨21605393710433456587452491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14403595806955637724968327 21605393710433456587452491)
            ·
              refine ⟨32408090565650184881178737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21605393710433456587452491 32408090565650184881178737)
              ·
                refine ⟨24306067924237638660884053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32408090565650184881178737 24306067924237638660884053)
                ·
                  refine ⟨284836733487159828057235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24306067924237638660884053 284836733487159828057235)
                  ·
                    rfl

theorem cell22_2496229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_2496229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496229 prefixEnd_2496229 := by exact prefixLift 2496229
  have htrace : WordTrace (prefixWord ++ tailWord_2496229) baseStart_2496229 baseEnd_2496229 := by
    simpa [prefixWord, tailWord_2496229, baseEnd_2496229] using wordTrace_append hprefix tailTrace_2496229
  have hstable : (prefixWord ++ tailWord_2496229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496229).length < 2 ^ (prefixWord ++ tailWord_2496229).sum := by decide
  have hdescent : baseEnd_2496229 < baseStart_2496229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496246 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_2496246 : Nat := 118140960795 + 2496246 * 2 ^ 59
def prefixEnd_2496246 : Nat := 4983230072969 + 3 ^ 40 * 2496246 * 2
def baseEnd_2496246 : Nat := 284838673302965702165551

theorem tailTrace_2496246 : CollatzResearch.WordTrace tailWord_2496246 prefixEnd_2496246 284838673302965702165551 := by
  unfold tailWord_2496246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690348207158408857528287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60697047543023027813635061 5690348207158408857528287)
  ·
    refine ⟨8535522310737613286292431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5690348207158408857528287 8535522310737613286292431)
    ·
      refine ⟨12803283466106419929438647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8535522310737613286292431 12803283466106419929438647)
      ·
        refine ⟨19204925199159629894157971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12803283466106419929438647 19204925199159629894157971)
        ·
          refine ⟨28807387798739444841236957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19204925199159629894157971 28807387798739444841236957)
          ·
            refine ⟨10802770424527291815463859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28807387798739444841236957 10802770424527291815463859)
            ·
              refine ⟨16204155636790937723195789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10802770424527291815463859 16204155636790937723195789)
              ·
                refine ⟨6076558363796601646198421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16204155636790937723195789 6076558363796601646198421)
                ·
                  refine ⟨284838673302965702165551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6076558363796601646198421 284838673302965702165551)
                  ·
                    rfl

theorem cell22_2496246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_2496246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496246 prefixEnd_2496246 := by exact prefixLift 2496246
  have htrace : WordTrace (prefixWord ++ tailWord_2496246) baseStart_2496246 baseEnd_2496246 := by
    simpa [prefixWord, tailWord_2496246, baseEnd_2496246] using wordTrace_append hprefix tailTrace_2496246
  have hstable : (prefixWord ++ tailWord_2496246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496246).length < 2 ^ (prefixWord ++ tailWord_2496246).sum := by decide
  have hdescent : baseEnd_2496246 < baseStart_2496246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496259 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 1, 6]
def baseStart_2496259 : Nat := 118140960795 + 2496259 * 2 ^ 59
def prefixEnd_2496259 : Nat := 4983230072969 + 3 ^ 40 * 2496259 * 2
def baseEnd_2496259 : Nat := 854520470074569405921613

theorem tailTrace_2496259 : CollatzResearch.WordTrace tailWord_2496259 prefixEnd_2496259 854520470074569405921613 := by
  unfold tailWord_2496259
  simp only [CollatzResearch.WordTrace]
  refine ⟨91046045463487444940675831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60697363642324963293783887 91046045463487444940675831)
  ·
    refine ⟨136569068195231167411013747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91046045463487444940675831 136569068195231167411013747)
    ·
      refine ⟨204853602292846751116520621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136569068195231167411013747 204853602292846751116520621)
      ·
        refine ⟨76820100859817531668695233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204853602292846751116520621 76820100859817531668695233)
        ·
          refine ⟨57615075644863148751521425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76820100859817531668695233 57615075644863148751521425)
          ·
            refine ⟨43211306733647361563641069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57615075644863148751521425 43211306733647361563641069)
            ·
              refine ⟨16204240025117760586365401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43211306733647361563641069 16204240025117760586365401)
              ·
                refine ⟨12153180018838320439774051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16204240025117760586365401 12153180018838320439774051)
                ·
                  refine ⟨18229770028257480659661077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12153180018838320439774051 18229770028257480659661077)
                  ·
                    refine ⟨854520470074569405921613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18229770028257480659661077 854520470074569405921613)
                    ·
                      rfl

theorem cell22_2496259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_2496259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496259 prefixEnd_2496259 := by exact prefixLift 2496259
  have htrace : WordTrace (prefixWord ++ tailWord_2496259) baseStart_2496259 baseEnd_2496259 := by
    simpa [prefixWord, tailWord_2496259, baseEnd_2496259] using wordTrace_append hprefix tailTrace_2496259
  have hstable : (prefixWord ++ tailWord_2496259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496259).length < 2 ^ (prefixWord ++ tailWord_2496259).sum := by decide
  have hdescent : baseEnd_2496259 < baseStart_2496259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496308 : List Nat := [2, 5, 1, 1, 2, 2, 2, 7]
def baseStart_2496308 : Nat := 118140960795 + 2496308 * 2 ^ 59
def prefixEnd_2496308 : Nat := 4983230072969 + 3 ^ 40 * 2496308 * 2
def baseEnd_2496308 : Nat := 94948582641772179049607

theorem tailTrace_2496308 : CollatzResearch.WordTrace tailWord_2496308 prefixEnd_2496308 94948582641772179049607 := by
  unfold tailWord_2496308
  simp only [CollatzResearch.WordTrace]
  refine ⟨45523916320154963154604789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60698555093539950872806385 45523916320154963154604789)
  ·
    refine ⟨4267867155014527795744199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45523916320154963154604789 4267867155014527795744199)
    ·
      refine ⟨6401800732521791693616299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267867155014527795744199 6401800732521791693616299)
      ·
        refine ⟨9602701098782687540424449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401800732521791693616299 9602701098782687540424449)
        ·
          refine ⟨7202025824087015655318337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9602701098782687540424449 7202025824087015655318337)
          ·
            refine ⟨5401519368065261741488753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7202025824087015655318337 5401519368065261741488753)
            ·
              refine ⟨4051139526048946306116565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5401519368065261741488753 4051139526048946306116565)
              ·
                refine ⟨94948582641772179049607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4051139526048946306116565 94948582641772179049607)
                ·
                  rfl

theorem cell22_2496308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 7].length) (baseStart_2496308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496308 prefixEnd_2496308 := by exact prefixLift 2496308
  have htrace : WordTrace (prefixWord ++ tailWord_2496308) baseStart_2496308 baseEnd_2496308 := by
    simpa [prefixWord, tailWord_2496308, baseEnd_2496308] using wordTrace_append hprefix tailTrace_2496308
  have hstable : (prefixWord ++ tailWord_2496308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496308).length < 2 ^ (prefixWord ++ tailWord_2496308).sum := by decide
  have hdescent : baseEnd_2496308 < baseStart_2496308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496441 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_2496441 : Nat := 118140960795 + 2496441 * 2 ^ 59
def prefixEnd_2496441 : Nat := 4983230072969 + 3 ^ 40 * 2496441 * 2
def baseEnd_2496441 : Nat := 854582772393981597871055

theorem tailTrace_2496441 : CollatzResearch.WordTrace tailWord_2496441 prefixEnd_2496441 854582772393981597871055 := by
  unfold tailWord_2496441
  simp only [CollatzResearch.WordTrace]
  refine ⟨91052683548828090023801177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60701789032552060015867451 91052683548828090023801177)
  ·
    refine ⟨68289512661621067517850883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91052683548828090023801177 68289512661621067517850883)
    ·
      refine ⟨102434268992431601276776325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68289512661621067517850883 102434268992431601276776325)
      ·
        refine ⟨19206425436080925239395561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102434268992431601276776325 19206425436080925239395561)
        ·
          refine ⟨14404819077060693929546671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19206425436080925239395561 14404819077060693929546671)
          ·
            refine ⟨21607228615591040894320007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14404819077060693929546671 21607228615591040894320007)
            ·
              refine ⟨32410842923386561341480011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21607228615591040894320007 32410842923386561341480011)
              ·
                refine ⟨48616264385079842012220017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32410842923386561341480011 48616264385079842012220017)
                ·
                  refine ⟨36462198288809881509165013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48616264385079842012220017 36462198288809881509165013)
                  ·
                    refine ⟨854582772393981597871055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36462198288809881509165013 854582772393981597871055)
                    ·
                      rfl

theorem cell22_2496441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_2496441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496441 prefixEnd_2496441 := by exact prefixLift 2496441
  have htrace : WordTrace (prefixWord ++ tailWord_2496441) baseStart_2496441 baseEnd_2496441 := by
    simpa [prefixWord, tailWord_2496441, baseEnd_2496441] using wordTrace_append hprefix tailTrace_2496441
  have hstable : (prefixWord ++ tailWord_2496441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496441).length < 2 ^ (prefixWord ++ tailWord_2496441).sum := by decide
  have hdescent : baseEnd_2496441 < baseStart_2496441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496458 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_2496458 : Nat := 118140960795 + 2496458 * 2 ^ 59
def prefixEnd_2496458 : Nat := 4983230072969 + 3 ^ 40 * 2496458 * 2
def baseEnd_2496458 : Nat := 854588591841399220196003

theorem tailTrace_2496458 : CollatzResearch.WordTrace tailWord_2496458 prefixEnd_2496458 854588591841399220196003 := by
  unfold tailWord_2496458
  simp only [CollatzResearch.WordTrace]
  refine ⟨22763325897441625481792507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60702202393177667951446685 22763325897441625481792507)
  ·
    refine ⟨34144988846162438222688761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22763325897441625481792507 34144988846162438222688761)
    ·
      refine ⟨25608741634621828667016571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34144988846162438222688761 25608741634621828667016571)
      ·
        refine ⟨38413112451932743000524857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25608741634621828667016571 38413112451932743000524857)
        ·
          refine ⟨28809834338949557250393643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38413112451932743000524857 28809834338949557250393643)
          ·
            refine ⟨43214751508424335875590465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28809834338949557250393643 43214751508424335875590465)
            ·
              refine ⟨32411063631318251906692849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43214751508424335875590465 32411063631318251906692849)
              ·
                refine ⟨24308297723488688930019637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32411063631318251906692849 24308297723488688930019637)
                ·
                  refine ⟨2278902911577064587189341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24308297723488688930019637 2278902911577064587189341)
                  ·
                    refine ⟨854588591841399220196003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2278902911577064587189341 854588591841399220196003)
                    ·
                      rfl

theorem cell22_2496458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_2496458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496458 prefixEnd_2496458 := by exact prefixLift 2496458
  have htrace : WordTrace (prefixWord ++ tailWord_2496458) baseStart_2496458 baseEnd_2496458 := by
    simpa [prefixWord, tailWord_2496458, baseEnd_2496458] using wordTrace_append hprefix tailTrace_2496458
  have hstable : (prefixWord ++ tailWord_2496458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496458).length < 2 ^ (prefixWord ++ tailWord_2496458).sum := by decide
  have hdescent : baseEnd_2496458 < baseStart_2496458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496471 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 7]
def baseStart_2496471 : Nat := 118140960795 + 2496471 * 2 ^ 59
def prefixEnd_2496471 : Nat := 4983230072969 + 3 ^ 40 * 2496471 * 2
def baseEnd_2496471 : Nat := 284864347335690506540321

theorem tailTrace_2496471 : CollatzResearch.WordTrace tailWord_2496471 prefixEnd_2496471 284864347335690506540321 := by
  unfold tailWord_2496471
  simp only [CollatzResearch.WordTrace]
  refine ⟨91053777738719405147393267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60702518492479603431595511 91053777738719405147393267)
  ·
    refine ⟨136580666608079107721089901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91053777738719405147393267 136580666608079107721089901)
    ·
      refine ⟨51217749978029665395408713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136580666608079107721089901 51217749978029665395408713)
      ·
        refine ⟨38413312483522249046556535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51217749978029665395408713 38413312483522249046556535)
        ·
          refine ⟨57619968725283373569834803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38413312483522249046556535 57619968725283373569834803)
          ·
            refine ⟨86429953087925060354752205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57619968725283373569834803 86429953087925060354752205)
            ·
              refine ⟨32411232407971897633032077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86429953087925060354752205 32411232407971897633032077)
              ·
                refine ⟨12154212152989461612387029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32411232407971897633032077 12154212152989461612387029)
                ·
                  refine ⟨284864347335690506540321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12154212152989461612387029 284864347335690506540321)
                  ·
                    rfl

theorem cell22_2496471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 7].length) (baseStart_2496471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496471 prefixEnd_2496471 := by exact prefixLift 2496471
  have htrace : WordTrace (prefixWord ++ tailWord_2496471) baseStart_2496471 baseEnd_2496471 := by
    simpa [prefixWord, tailWord_2496471, baseEnd_2496471] using wordTrace_append hprefix tailTrace_2496471
  have hstable : (prefixWord ++ tailWord_2496471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496471).length < 2 ^ (prefixWord ++ tailWord_2496471).sum := by decide
  have hdescent : baseEnd_2496471 < baseStart_2496471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496569 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 1, 4]
def baseStart_2496569 : Nat := 118140960795 + 2496569 * 2 ^ 59
def prefixEnd_2496569 : Nat := 4983230072969 + 3 ^ 40 * 2496569 * 2
def baseEnd_2496569 : Nat := 854626589409831930670663

theorem tailTrace_2496569 : CollatzResearch.WordTrace tailWord_2496569 prefixEnd_2496569 854626589409831930670663 := by
  unfold tailWord_2496569
  simp only [CollatzResearch.WordTrace]
  refine ⟨91057352092364367884460761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60704901394909578589640507 91057352092364367884460761)
  ·
    refine ⟨68293014069273275913345571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91057352092364367884460761 68293014069273275913345571)
    ·
      refine ⟨102439521103909913870018357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68293014069273275913345571 102439521103909913870018357)
      ·
        refine ⟨9603705103491554425314221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102439521103909913870018357 9603705103491554425314221)
        ·
          refine ⟨3601389413809332909492833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9603705103491554425314221 3601389413809332909492833)
          ·
            refine ⟨2701042060356999682119625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3601389413809332909492833 2701042060356999682119625)
            ·
              refine ⟨2025781545267749761589719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2701042060356999682119625 2025781545267749761589719)
              ·
                refine ⟨3038672317901624642384579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2025781545267749761589719 3038672317901624642384579)
                ·
                  refine ⟨4558008476852436963576869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038672317901624642384579 4558008476852436963576869)
                  ·
                    refine ⟨854626589409831930670663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558008476852436963576869 854626589409831930670663)
                    ·
                      rfl

theorem cell22_2496569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 4].length) (baseStart_2496569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496569 prefixEnd_2496569 := by exact prefixLift 2496569
  have htrace : WordTrace (prefixWord ++ tailWord_2496569) baseStart_2496569 baseEnd_2496569 := by
    simpa [prefixWord, tailWord_2496569, baseEnd_2496569] using wordTrace_append hprefix tailTrace_2496569
  have hstable : (prefixWord ++ tailWord_2496569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496569).length < 2 ^ (prefixWord ++ tailWord_2496569).sum := by decide
  have hdescent : baseEnd_2496569 < baseStart_2496569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496623 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 7]
def baseStart_2496623 : Nat := 118140960795 + 2496623 * 2 ^ 59
def prefixEnd_2496623 : Nat := 4983230072969 + 3 ^ 40 * 2496623 * 2
def baseEnd_2496623 : Nat := 284881691571131263273499

theorem tailTrace_2496623 : CollatzResearch.WordTrace tailWord_2496623 prefixEnd_2496623 284881691571131263273499 := by
  unfold tailWord_2496623
  simp only [CollatzResearch.WordTrace]
  refine ⟨91059321634168735106926523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60706214422779156737951015 91059321634168735106926523)
  ·
    refine ⟨136588982451253102660389785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91059321634168735106926523 136588982451253102660389785)
    ·
      refine ⟨102441736838439826995292339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136588982451253102660389785 102441736838439826995292339)
      ·
        refine ⟨153662605257659740492938509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102441736838439826995292339 153662605257659740492938509)
        ·
          refine ⟨57623476971622402684851941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153662605257659740492938509 57623476971622402684851941)
          ·
            refine ⟨10804401932179200503409739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57623476971622402684851941 10804401932179200503409739)
            ·
              refine ⟨16206602898268800755114609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10804401932179200503409739 16206602898268800755114609)
              ·
                refine ⟨12154952173701600566335957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16206602898268800755114609 12154952173701600566335957)
                ·
                  refine ⟨284881691571131263273499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12154952173701600566335957 284881691571131263273499)
                  ·
                    rfl

theorem cell22_2496623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 7].length) (baseStart_2496623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496623 prefixEnd_2496623 := by exact prefixLift 2496623
  have htrace : WordTrace (prefixWord ++ tailWord_2496623) baseStart_2496623 baseEnd_2496623 := by
    simpa [prefixWord, tailWord_2496623, baseEnd_2496623] using wordTrace_append hprefix tailTrace_2496623
  have hstable : (prefixWord ++ tailWord_2496623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496623).length < 2 ^ (prefixWord ++ tailWord_2496623).sum := by decide
  have hdescent : baseEnd_2496623 < baseStart_2496623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496713 : List Nat := [1, 2, 1, 1, 2, 1, 1, 13]
def baseStart_2496713 : Nat := 118140960795 + 2496713 * 2 ^ 59
def prefixEnd_2496713 : Nat := 4983230072969 + 3 ^ 40 * 2496713 * 2
def baseEnd_2496713 : Nat := 94963987061407061674469

theorem tailTrace_2496713 : CollatzResearch.WordTrace tailWord_2496713 prefixEnd_2496713 94963987061407061674469 := by
  unfold tailWord_2496713
  simp only [CollatzResearch.WordTrace]
  refine ⟨91062604203842680477702793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60708402802561786985135195 91062604203842680477702793)
  ·
    refine ⟨68296953152882010358277095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91062604203842680477702793 68296953152882010358277095)
    ·
      refine ⟨102445429729323015537415643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68296953152882010358277095 102445429729323015537415643)
      ·
        refine ⟨153668144593984523306123465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102445429729323015537415643 153668144593984523306123465)
        ·
          refine ⟨115251108445488392479592599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153668144593984523306123465 115251108445488392479592599)
          ·
            refine ⟨172876662668232588719388899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115251108445488392479592599 172876662668232588719388899)
            ·
              refine ⟨259314994002348883079083349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172876662668232588719388899 259314994002348883079083349)
              ·
                refine ⟨94963987061407061674469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 259314994002348883079083349 94963987061407061674469)
                ·
                  rfl

theorem cell22_2496713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 13].length) (baseStart_2496713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496713 prefixEnd_2496713 := by exact prefixLift 2496713
  have htrace : WordTrace (prefixWord ++ tailWord_2496713) baseStart_2496713 baseEnd_2496713 := by
    simpa [prefixWord, tailWord_2496713, baseEnd_2496713] using wordTrace_append hprefix tailTrace_2496713
  have hstable : (prefixWord ++ tailWord_2496713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496713).length < 2 ^ (prefixWord ++ tailWord_2496713).sum := by decide
  have hdescent : baseEnd_2496713 < baseStart_2496713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496738 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2496738 : Nat := 118140960795 + 2496738 * 2 ^ 59
def prefixEnd_2496738 : Nat := 4983230072969 + 3 ^ 40 * 2496738 * 2
def baseEnd_2496738 : Nat := 854684441563571823195145

theorem tailTrace_2496738 : CollatzResearch.WordTrace tailWord_2496738 prefixEnd_2496738 854684441563571823195145 := by
  unfold tailWord_2496738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22765879007188027436840717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60709010685834739831575245 22765879007188027436840717)
  ·
    refine ⟨8537204627695510288815269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22765879007188027436840717 8537204627695510288815269)
    ·
      refine ⟨1600725867692908179152863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8537204627695510288815269 1600725867692908179152863)
      ·
        refine ⟨2401088801539362268729295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1600725867692908179152863 2401088801539362268729295)
        ·
          refine ⟨3601633202309043403093943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401088801539362268729295 3601633202309043403093943)
          ·
            refine ⟨5402449803463565104640915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601633202309043403093943 5402449803463565104640915)
            ·
              refine ⟨8103674705195347656961373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402449803463565104640915 8103674705195347656961373)
              ·
                refine ⟨3038878014448255371360515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8103674705195347656961373 3038878014448255371360515)
                ·
                  refine ⟨4558317021672383057040773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038878014448255371360515 4558317021672383057040773)
                  ·
                    refine ⟨854684441563571823195145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558317021672383057040773 854684441563571823195145)
                    ·
                      rfl

theorem cell22_2496738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2496738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496738 prefixEnd_2496738 := by exact prefixLift 2496738
  have htrace : WordTrace (prefixWord ++ tailWord_2496738) baseStart_2496738 baseEnd_2496738 := by
    simpa [prefixWord, tailWord_2496738, baseEnd_2496738] using wordTrace_append hprefix tailTrace_2496738
  have hstable : (prefixWord ++ tailWord_2496738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496738).length < 2 ^ (prefixWord ++ tailWord_2496738).sum := by decide
  have hdescent : baseEnd_2496738 < baseStart_2496738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496762 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_2496762 : Nat := 118140960795 + 2496762 * 2 ^ 59
def prefixEnd_2496762 : Nat := 4983230072969 + 3 ^ 40 * 2496762 * 2
def baseEnd_2496762 : Nat := 854692657254043760595071

theorem tailTrace_2496762 : CollatzResearch.WordTrace tailWord_2496762 prefixEnd_2496762 854692657254043760595071 := by
  unfold tailWord_2496762
  simp only [CollatzResearch.WordTrace]
  refine ⟨22766097845166290461559135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60709594253776774564157693 22766097845166290461559135)
  ·
    refine ⟨34149146767749435692338703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22766097845166290461559135 34149146767749435692338703)
    ·
      refine ⟨51223720151624153538508055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34149146767749435692338703 51223720151624153538508055)
      ·
        refine ⟨76835580227436230307762083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51223720151624153538508055 76835580227436230307762083)
        ·
          refine ⟨115253370341154345461643125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76835580227436230307762083 115253370341154345461643125)
          ·
            refine ⟨10805003469483219887029043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115253370341154345461643125 10805003469483219887029043)
            ·
              refine ⟨16207505204224829830543565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10805003469483219887029043 16207505204224829830543565)
              ·
                refine ⟨6077814451584311186453837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16207505204224829830543565 6077814451584311186453837)
                ·
                  refine ⟨2279180419344116694920189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6077814451584311186453837 2279180419344116694920189)
                  ·
                    refine ⟨854692657254043760595071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279180419344116694920189 854692657254043760595071)
                    ·
                      rfl

theorem cell22_2496762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_2496762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496762 prefixEnd_2496762 := by exact prefixLift 2496762
  have htrace : WordTrace (prefixWord ++ tailWord_2496762) baseStart_2496762 baseEnd_2496762 := by
    simpa [prefixWord, tailWord_2496762, baseEnd_2496762] using wordTrace_append hprefix tailTrace_2496762
  have hstable : (prefixWord ++ tailWord_2496762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496762).length < 2 ^ (prefixWord ++ tailWord_2496762).sum := by decide
  have hdescent : baseEnd_2496762 < baseStart_2496762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496813 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2496813 : Nat := 118140960795 + 2496813 * 2 ^ 59
def prefixEnd_2496813 : Nat := 4983230072969 + 3 ^ 40 * 2496813 * 2
def baseEnd_2496813 : Nat := 854710115596296627569915

theorem tailTrace_2496813 : CollatzResearch.WordTrace tailWord_2496813 prefixEnd_2496813 854710115596296627569915 := by
  unfold tailWord_2496813
  simp only [CollatzResearch.WordTrace]
  refine ⟨91066251503480397556343093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60710834335653598370895395 91066251503480397556343093)
  ·
    refine ⟨8537461078451287270907165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91066251503480397556343093 8537461078451287270907165)
    ·
      refine ⟨3201547904419232726590187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8537461078451287270907165 3201547904419232726590187)
      ·
        refine ⟨4802321856628849089885281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201547904419232726590187 4802321856628849089885281)
        ·
          refine ⟨3601741392471636817413961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4802321856628849089885281 3601741392471636817413961)
          ·
            refine ⟨2701306044353727613060471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3601741392471636817413961 2701306044353727613060471)
            ·
              refine ⟨4051959066530591419590707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701306044353727613060471 4051959066530591419590707)
              ·
                refine ⟨6077938599795887129386061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4051959066530591419590707 6077938599795887129386061)
                ·
                  refine ⟨2279226974923457673519773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6077938599795887129386061 2279226974923457673519773)
                  ·
                    refine ⟨854710115596296627569915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279226974923457673519773 854710115596296627569915)
                    ·
                      rfl

theorem cell22_2496813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2496813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496813 prefixEnd_2496813 := by exact prefixLift 2496813
  have htrace : WordTrace (prefixWord ++ tailWord_2496813) baseStart_2496813 baseEnd_2496813 := by
    simpa [prefixWord, tailWord_2496813, baseEnd_2496813] using wordTrace_append hprefix tailTrace_2496813
  have hstable : (prefixWord ++ tailWord_2496813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496813).length < 2 ^ (prefixWord ++ tailWord_2496813).sum := by decide
  have hdescent : baseEnd_2496813 < baseStart_2496813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496852 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2496852 : Nat := 118140960795 + 2496852 * 2 ^ 59
def prefixEnd_2496852 : Nat := 4983230072969 + 3 ^ 40 * 2496852 * 2
def baseEnd_2496852 : Nat := 854723466093313525844795

theorem tailTrace_2496852 : CollatzResearch.WordTrace tailWord_2496852 prefixEnd_2496852 854723466093313525844795 := by
  unfold tailWord_2496852
  simp only [CollatzResearch.WordTrace]
  refine ⟨45533836975169553608506405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60711782633559404811341873 45533836975169553608506405)
  ·
    refine ⟨8537594432844291301594951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45533836975169553608506405 8537594432844291301594951)
    ·
      refine ⟨12806391649266436952392427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8537594432844291301594951 12806391649266436952392427)
      ·
        refine ⟨19209587473899655428588641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12806391649266436952392427 19209587473899655428588641)
        ·
          refine ⟨14407190605424741571441481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19209587473899655428588641 14407190605424741571441481)
          ·
            refine ⟨10805392954068556178581111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14407190605424741571441481 10805392954068556178581111)
            ·
              refine ⟨16208089431102834267871667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10805392954068556178581111 16208089431102834267871667)
              ·
                refine ⟨24312134146654251401807501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16208089431102834267871667 24312134146654251401807501)
                ·
                  refine ⟨9117050304995344275677813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24312134146654251401807501 9117050304995344275677813)
                  ·
                    refine ⟨854723466093313525844795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9117050304995344275677813 854723466093313525844795)
                    ·
                      rfl

theorem cell22_2496852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2496852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496852 prefixEnd_2496852 := by exact prefixLift 2496852
  have htrace : WordTrace (prefixWord ++ tailWord_2496852) baseStart_2496852 baseEnd_2496852 := by
    simpa [prefixWord, tailWord_2496852, baseEnd_2496852] using wordTrace_append hprefix tailTrace_2496852
  have hstable : (prefixWord ++ tailWord_2496852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496852).length < 2 ^ (prefixWord ++ tailWord_2496852).sum := by decide
  have hdescent : baseEnd_2496852 < baseStart_2496852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496867 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 2, 4]
def baseStart_2496867 : Nat := 118140960795 + 2496867 * 2 ^ 59
def prefixEnd_2496867 : Nat := 4983230072969 + 3 ^ 40 * 2496867 * 2
def baseEnd_2496867 : Nat := 854728600899858486719749

theorem tailTrace_2496867 : CollatzResearch.WordTrace tailWord_2496867 prefixEnd_2496867 854728600899858486719749 := by
  unfold tailWord_2496867
  simp only [CollatzResearch.WordTrace]
  refine ⟨91068221045284764778808855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60712147363523176519205903 91068221045284764778808855)
  ·
    refine ⟨136602331567927147168213283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91068221045284764778808855 136602331567927147168213283)
    ·
      refine ⟨204903497351890720752319925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136602331567927147168213283 204903497351890720752319925)
      ·
        refine ⟨19209702876739755070529993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204903497351890720752319925 19209702876739755070529993)
        ·
          refine ⟨14407277157554816302897495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19209702876739755070529993 14407277157554816302897495)
          ·
            refine ⟨21610915736332224454346243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14407277157554816302897495 21610915736332224454346243)
            ·
              refine ⟨32416373604498336681519365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21610915736332224454346243 32416373604498336681519365)
              ·
                refine ⟨6078070050843438127784881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32416373604498336681519365 6078070050843438127784881)
                ·
                  refine ⟨4558552538132578595838661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078070050843438127784881 4558552538132578595838661)
                  ·
                    refine ⟨854728600899858486719749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558552538132578595838661 854728600899858486719749)
                    ·
                      rfl

theorem cell22_2496867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 4].length) (baseStart_2496867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496867 prefixEnd_2496867 := by exact prefixLift 2496867
  have htrace : WordTrace (prefixWord ++ tailWord_2496867) baseStart_2496867 baseEnd_2496867 := by
    simpa [prefixWord, tailWord_2496867, baseEnd_2496867] using wordTrace_append hprefix tailTrace_2496867
  have hstable : (prefixWord ++ tailWord_2496867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496867).length < 2 ^ (prefixWord ++ tailWord_2496867).sum := by decide
  have hdescent : baseEnd_2496867 < baseStart_2496867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496869 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_2496869 : Nat := 118140960795 + 2496869 * 2 ^ 59
def prefixEnd_2496869 : Nat := 4983230072969 + 3 ^ 40 * 2496869 * 2
def baseEnd_2496869 : Nat := 854729285540731148169743

theorem tailTrace_2496869 : CollatzResearch.WordTrace tailWord_2496869 prefixEnd_2496869 854729285540731148169743 := by
  unfold tailWord_2496869
  simp only [CollatzResearch.WordTrace]
  refine ⟨91068293991277519120381661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60712195994185012746921107 91068293991277519120381661)
  ·
    refine ⟨34150610246729069670143123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91068293991277519120381661 34150610246729069670143123)
    ·
      refine ⟨51225915370093604505214685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34150610246729069670143123 51225915370093604505214685)
      ·
        refine ⟨19209718263785101689455507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51225915370093604505214685 19209718263785101689455507)
        ·
          refine ⟨28814577395677652534183261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19209718263785101689455507 28814577395677652534183261)
          ·
            refine ⟨10805466523379119700318723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28814577395677652534183261 10805466523379119700318723)
            ·
              refine ⟨16208199785068679550478085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10805466523379119700318723 16208199785068679550478085)
              ·
                refine ⟨3039037459700377415714641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16208199785068679550478085 3039037459700377415714641)
                ·
                  refine ⟨2279278094775283061785981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3039037459700377415714641 2279278094775283061785981)
                  ·
                    refine ⟨854729285540731148169743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279278094775283061785981 854729285540731148169743)
                    ·
                      rfl

theorem cell22_2496869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_2496869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496869 prefixEnd_2496869 := by exact prefixLift 2496869
  have htrace : WordTrace (prefixWord ++ tailWord_2496869) baseStart_2496869 baseEnd_2496869 := by
    simpa [prefixWord, tailWord_2496869, baseEnd_2496869] using wordTrace_append hprefix tailTrace_2496869
  have hstable : (prefixWord ++ tailWord_2496869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496869).length < 2 ^ (prefixWord ++ tailWord_2496869).sum := by decide
  have hdescent : baseEnd_2496869 < baseStart_2496869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496871 : List Nat := [1, 1, 5, 1, 3, 1, 4, 2, 4]
def baseStart_2496871 : Nat := 118140960795 + 2496871 * 2 ^ 59
def prefixEnd_2496871 : Nat := 4983230072969 + 3 ^ 40 * 2496871 * 2
def baseEnd_2496871 : Nat := 284909990060534603206579

theorem tailTrace_2496871 : CollatzResearch.WordTrace tailWord_2496871 prefixEnd_2496871 284909990060534603206579 := by
  unfold tailWord_2496871
  simp only [CollatzResearch.WordTrace]
  refine ⟨91068366937270273461954467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60712244624846848974636311 91068366937270273461954467)
  ·
    refine ⟨136602550405905410192931701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91068366937270273461954467 136602550405905410192931701)
    ·
      refine ⟨12806489100553632205587347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136602550405905410192931701 12806489100553632205587347)
      ·
        refine ⟨19209733650830448308381021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12806489100553632205587347 19209733650830448308381021)
        ·
          refine ⟨7203650119061418115642883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19209733650830448308381021 7203650119061418115642883)
          ·
            refine ⟨10805475178592127173464325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7203650119061418115642883 10805475178592127173464325)
            ·
              refine ⟨2026026595986023845024561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10805475178592127173464325 2026026595986023845024561)
              ·
                refine ⟨1519519946989517883768421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026026595986023845024561 1519519946989517883768421)
                ·
                  refine ⟨284909990060534603206579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1519519946989517883768421 284909990060534603206579)
                  ·
                    rfl

theorem cell22_2496871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 4].length) (baseStart_2496871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496871 prefixEnd_2496871 := by exact prefixLift 2496871
  have htrace : WordTrace (prefixWord ++ tailWord_2496871) baseStart_2496871 baseEnd_2496871 := by
    simpa [prefixWord, tailWord_2496871, baseEnd_2496871] using wordTrace_append hprefix tailTrace_2496871
  have hstable : (prefixWord ++ tailWord_2496871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496871).length < 2 ^ (prefixWord ++ tailWord_2496871).sum := by decide
  have hdescent : baseEnd_2496871 < baseStart_2496871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496882 : List Nat := [3, 2, 1, 2, 1, 3, 3, 7]
def baseStart_2496882 : Nat := 118140960795 + 2496882 * 2 ^ 59
def prefixEnd_2496882 : Nat := 4983230072969 + 3 ^ 40 * 2496882 * 2
def baseEnd_2496882 : Nat := 94970415078489271954967

theorem tailTrace_2496882 : CollatzResearch.WordTrace tailWord_2496882 prefixEnd_2496882 94970415078489271954967 := by
  unfold tailWord_2496882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22767192035057605585151225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60712512093486948227069933 22767192035057605585151225)
  ·
    refine ⟨17075394026293204188863419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22767192035057605585151225 17075394026293204188863419)
    ·
      refine ⟨25613091039439806283295129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17075394026293204188863419 25613091039439806283295129)
      ·
        refine ⟨19209818279579854712471347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25613091039439806283295129 19209818279579854712471347)
        ·
          refine ⟨28814727419369782068707021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19209818279579854712471347 28814727419369782068707021)
          ·
            refine ⟨10805522782263668275765133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28814727419369782068707021 10805522782263668275765133)
            ·
              refine ⟨4052071043348875603411925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10805522782263668275765133 4052071043348875603411925)
              ·
                refine ⟨94970415078489271954967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4052071043348875603411925 94970415078489271954967)
                ·
                  rfl

theorem cell22_2496882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_2496882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496882 prefixEnd_2496882 := by exact prefixLift 2496882
  have htrace : WordTrace (prefixWord ++ tailWord_2496882) baseStart_2496882 baseEnd_2496882 := by
    simpa [prefixWord, tailWord_2496882, baseEnd_2496882] using wordTrace_append hprefix tailTrace_2496882
  have hstable : (prefixWord ++ tailWord_2496882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496882).length < 2 ^ (prefixWord ++ tailWord_2496882).sum := by decide
  have hdescent : baseEnd_2496882 < baseStart_2496882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496899 : List Nat := [1, 1, 1, 3, 6, 1, 3, 6]
def baseStart_2496899 : Nat := 118140960795 + 2496899 * 2 ^ 59
def prefixEnd_2496899 : Nat := 4983230072969 + 3 ^ 40 * 2496899 * 2
def baseEnd_2496899 : Nat := 94971061683757896657739

theorem tailTrace_2496899 : CollatzResearch.WordTrace tailWord_2496899 prefixEnd_2496899 94971061683757896657739 := by
  unfold tailWord_2496899
  simp only [CollatzResearch.WordTrace]
  refine ⟨91069388181168834243973751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60712925454112556162649167 91069388181168834243973751)
  ·
    refine ⟨136604082271753251365960627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91069388181168834243973751 136604082271753251365960627)
    ·
      refine ⟨204906123407629877048940941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136604082271753251365960627 204906123407629877048940941)
      ·
        refine ⟨76839796277861203893352853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204906123407629877048940941 76839796277861203893352853)
        ·
          refine ⟨3601865450524743932500915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76839796277861203893352853 3601865450524743932500915)
          ·
            refine ⟨5402798175787115898751373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601865450524743932500915 5402798175787115898751373)
            ·
              refine ⟨2026049315920168462031765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5402798175787115898751373 2026049315920168462031765)
              ·
                refine ⟨94971061683757896657739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2026049315920168462031765 94971061683757896657739)
                ·
                  rfl

theorem cell22_2496899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 6].length) (baseStart_2496899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496899 prefixEnd_2496899 := by exact prefixLift 2496899
  have htrace : WordTrace (prefixWord ++ tailWord_2496899) baseStart_2496899 baseEnd_2496899 := by
    simpa [prefixWord, tailWord_2496899, baseEnd_2496899] using wordTrace_append hprefix tailTrace_2496899
  have hstable : (prefixWord ++ tailWord_2496899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496899).length < 2 ^ (prefixWord ++ tailWord_2496899).sum := by decide
  have hdescent : baseEnd_2496899 < baseStart_2496899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496927 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 7]
def baseStart_2496927 : Nat := 118140960795 + 2496927 * 2 ^ 59
def prefixEnd_2496927 : Nat := 4983230072969 + 3 ^ 40 * 2496927 * 2
def baseEnd_2496927 : Nat := 284916380042012776739855

theorem tailTrace_2496927 : CollatzResearch.WordTrace tailWord_2496927 prefixEnd_2496927 284916380042012776739855 := by
  unfold tailWord_2496927
  simp only [CollatzResearch.WordTrace]
  refine ⟨91070409425067395025993035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60713606283378263350662023 91070409425067395025993035)
  ·
    refine ⟨136605614137601092538989553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91070409425067395025993035 136605614137601092538989553)
    ·
      refine ⟨102454210603200819404242165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136605614137601092538989553 102454210603200819404242165)
      ·
        refine ⟨9605082244050076819147703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102454210603200819404242165 9605082244050076819147703)
        ·
          refine ⟨14407623366075115228721555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9605082244050076819147703 14407623366075115228721555)
          ·
            refine ⟨21611435049112672843082333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14407623366075115228721555 21611435049112672843082333)
            ·
              refine ⟨8104288143417252316155875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21611435049112672843082333 8104288143417252316155875)
              ·
                refine ⟨12156432215125878474233813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8104288143417252316155875 12156432215125878474233813)
                ·
                  refine ⟨284916380042012776739855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12156432215125878474233813 284916380042012776739855)
                  ·
                    rfl

theorem cell22_2496927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 7].length) (baseStart_2496927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496927 prefixEnd_2496927 := by exact prefixLift 2496927
  have htrace : WordTrace (prefixWord ++ tailWord_2496927) baseStart_2496927 baseEnd_2496927 := by
    simpa [prefixWord, tailWord_2496927, baseEnd_2496927] using wordTrace_append hprefix tailTrace_2496927
  have hstable : (prefixWord ++ tailWord_2496927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496927).length < 2 ^ (prefixWord ++ tailWord_2496927).sum := by decide
  have hdescent : baseEnd_2496927 < baseStart_2496927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2496931 : List Nat := [1, 1, 1, 4, 1, 4, 2, 4, 1, 3]
def baseStart_2496931 : Nat := 118140960795 + 2496931 * 2 ^ 59
def prefixEnd_2496931 : Nat := 4983230072969 + 3 ^ 40 * 2496931 * 2
def baseEnd_2496931 : Nat := 854750509407783653119553

theorem tailTrace_2496931 : CollatzResearch.WordTrace tailWord_2496931 prefixEnd_2496931 854750509407783653119553 := by
  unfold tailWord_2496931
  simp only [CollatzResearch.WordTrace]
  refine ⟨91070555317052903709138647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60713703544701935806092431 91070555317052903709138647)
  ·
    refine ⟨136605832975579355563707971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91070555317052903709138647 136605832975579355563707971)
    ·
      refine ⟨204908749463369033345561957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136605832975579355563707971 204908749463369033345561957)
      ·
        refine ⟨38420390524381693752292867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204908749463369033345561957 38420390524381693752292867)
        ·
          refine ⟨57630585786572540628439301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38420390524381693752292867 57630585786572540628439301)
          ·
            refine ⟨10805734834982351367832369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57630585786572540628439301 10805734834982351367832369)
            ·
              refine ⟨8104301126236763525874277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10805734834982351367832369 8104301126236763525874277)
              ·
                refine ⟨1519556461169393161101427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8104301126236763525874277 1519556461169393161101427)
                ·
                  refine ⟨2279334691754089741652141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519556461169393161101427 2279334691754089741652141)
                  ·
                    refine ⟨854750509407783653119553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279334691754089741652141 854750509407783653119553)
                    ·
                      rfl

theorem cell22_2496931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 1, 3].length) (baseStart_2496931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2496931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2496931 prefixEnd_2496931 := by exact prefixLift 2496931
  have htrace : WordTrace (prefixWord ++ tailWord_2496931) baseStart_2496931 baseEnd_2496931 := by
    simpa [prefixWord, tailWord_2496931, baseEnd_2496931] using wordTrace_append hprefix tailTrace_2496931
  have hstable : (prefixWord ++ tailWord_2496931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2496931).length < 2 ^ (prefixWord ++ tailWord_2496931).sum := by decide
  have hdescent : baseEnd_2496931 < baseStart_2496931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2496931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497017 : List Nat := [1, 2, 1, 3, 1, 2, 4, 8]
def baseStart_2497017 : Nat := 118140960795 + 2497017 * 2 ^ 59
def prefixEnd_2497017 : Nat := 4983230072969 + 3 ^ 40 * 2497017 * 2
def baseEnd_2497017 : Nat := 94975549885034232829921

theorem tailTrace_2497017 : CollatzResearch.WordTrace tailWord_2497017 prefixEnd_2497017 94975549885034232829921 := by
  unfold tailWord_2497017
  simp only [CollatzResearch.WordTrace]
  refine ⟨91073691994741340396769305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60715794663160893597846203 91073691994741340396769305)
  ·
    refine ⟨68305268996056005297576979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91073691994741340396769305 68305268996056005297576979)
    ·
      refine ⟨102457903494084007946365469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68305268996056005297576979 102457903494084007946365469)
      ·
        refine ⟨38421713810281502979887051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102457903494084007946365469 38421713810281502979887051)
        ·
          refine ⟨57632570715422254469830577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38421713810281502979887051 57632570715422254469830577)
          ·
            refine ⟨43224428036566690852372933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57632570715422254469830577 43224428036566690852372933)
            ·
              refine ⟨8104580256856254534819925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43224428036566690852372933 8104580256856254534819925)
              ·
                refine ⟨94975549885034232829921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8104580256856254534819925 94975549885034232829921)
                ·
                  rfl

theorem cell22_2497017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 8].length) (baseStart_2497017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497017 prefixEnd_2497017 := by exact prefixLift 2497017
  have htrace : WordTrace (prefixWord ++ tailWord_2497017) baseStart_2497017 baseEnd_2497017 := by
    simpa [prefixWord, tailWord_2497017, baseEnd_2497017] using wordTrace_append hprefix tailTrace_2497017
  have hstable : (prefixWord ++ tailWord_2497017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497017).length < 2 ^ (prefixWord ++ tailWord_2497017).sum := by decide
  have hdescent : baseEnd_2497017 < baseStart_2497017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497038 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_2497038 : Nat := 118140960795 + 2497038 * 2 ^ 59
def prefixEnd_2497038 : Nat := 4983230072969 + 3 ^ 40 * 2497038 * 2
def baseEnd_2497038 : Nat := 854787137694471040694225

theorem tailTrace_2497038 : CollatzResearch.WordTrace tailWord_2497038 prefixEnd_2497038 854787137694471040694225 := by
  unfold tailWord_2497038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384307240958157622910471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60716305285110173988855845 11384307240958157622910471)
  ·
    refine ⟨17076460861437236434365707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11384307240958157622910471 17076460861437236434365707)
    ·
      refine ⟨25614691292155854651548561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17076460861437236434365707 25614691292155854651548561)
      ·
        refine ⟨19211018469116890988661421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25614691292155854651548561 19211018469116890988661421)
        ·
          refine ⟨7204131925918834120748033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19211018469116890988661421 7204131925918834120748033)
          ·
            refine ⟨5403098944439125590561025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7204131925918834120748033 5403098944439125590561025)
            ·
              refine ⟨4052324208329344192920769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5403098944439125590561025 4052324208329344192920769)
              ·
                refine ⟨3039243156247008144690577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4052324208329344192920769 3039243156247008144690577)
                ·
                  refine ⟨2279432367185256108517933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3039243156247008144690577 2279432367185256108517933)
                  ·
                    refine ⟨854787137694471040694225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279432367185256108517933 854787137694471040694225)
                    ·
                      rfl

theorem cell22_2497038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_2497038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497038 prefixEnd_2497038 := by exact prefixLift 2497038
  have htrace : WordTrace (prefixWord ++ tailWord_2497038) baseStart_2497038 baseEnd_2497038 := by
    simpa [prefixWord, tailWord_2497038, baseEnd_2497038] using wordTrace_append hprefix tailTrace_2497038
  have hstable : (prefixWord ++ tailWord_2497038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497038).length < 2 ^ (prefixWord ++ tailWord_2497038).sum := by decide
  have hdescent : baseEnd_2497038 < baseStart_2497038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497066 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2497066 : Nat := 118140960795 + 2497066 * 2 ^ 59
def prefixEnd_2497066 : Nat := 4983230072969 + 3 ^ 40 * 2497066 * 2
def baseEnd_2497066 : Nat := 854796722666688300994139

theorem tailTrace_2497066 : CollatzResearch.WordTrace tailWord_2497066 prefixEnd_2497066 854796722666688300994139 := by
  unfold tailWord_2497066
  simp only [CollatzResearch.WordTrace]
  refine ⟨22768869792890955441325763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60716986114375881176868701 22768869792890955441325763)
  ·
    refine ⟨34153304689336433161988645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22768869792890955441325763 34153304689336433161988645)
    ·
      refine ⟨6403744629250581217872871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34153304689336433161988645 6403744629250581217872871)
      ·
        refine ⟨9605616943875871826809307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6403744629250581217872871 9605616943875871826809307)
        ·
          refine ⟨14408425415813807740213961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9605616943875871826809307 14408425415813807740213961)
          ·
            refine ⟨10806319061860355805160471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14408425415813807740213961 10806319061860355805160471)
            ·
              refine ⟨16209478592790533707740707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10806319061860355805160471 16209478592790533707740707)
              ·
                refine ⟨24314217889185800561611061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16209478592790533707740707 24314217889185800561611061)
                ·
                  refine ⟨2279457927111168802651037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24314217889185800561611061 2279457927111168802651037)
                  ·
                    refine ⟨854796722666688300994139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279457927111168802651037 854796722666688300994139)
                    ·
                      rfl

theorem cell22_2497066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2497066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497066 prefixEnd_2497066 := by exact prefixLift 2497066
  have htrace : WordTrace (prefixWord ++ tailWord_2497066) baseStart_2497066 baseEnd_2497066 := by
    simpa [prefixWord, tailWord_2497066, baseEnd_2497066] using wordTrace_append hprefix tailTrace_2497066
  have hstable : (prefixWord ++ tailWord_2497066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497066).length < 2 ^ (prefixWord ++ tailWord_2497066).sum := by decide
  have hdescent : baseEnd_2497066 < baseStart_2497066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497070 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2497070 : Nat := 118140960795 + 2497070 * 2 ^ 59
def prefixEnd_2497070 : Nat := 4983230072969 + 3 ^ 40 * 2497070 * 2
def baseEnd_2497070 : Nat := 854798091948433623894127

theorem tailTrace_2497070 : CollatzResearch.WordTrace tailWord_2497070 prefixEnd_2497070 854798091948433623894127 := by
  unfold tailWord_2497070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384453132943666306056083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60717083375699553632299109 11384453132943666306056083)
  ·
    refine ⟨17076679699415499459084125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11384453132943666306056083 17076679699415499459084125)
    ·
      refine ⟨6403754887280812297156547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17076679699415499459084125 6403754887280812297156547)
      ·
        refine ⟨9605632330921218445734821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6403754887280812297156547 9605632330921218445734821)
        ·
          refine ⟨1801056062047728458575279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9605632330921218445734821 1801056062047728458575279)
          ·
            refine ⟨2701584093071592687862919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801056062047728458575279 2701584093071592687862919)
            ·
              refine ⟨4052376139607389031794379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701584093071592687862919 4052376139607389031794379)
              ·
                refine ⟨6078564209411083547691569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052376139607389031794379 6078564209411083547691569)
                ·
                  refine ⟨4558923157058312660768677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6078564209411083547691569 4558923157058312660768677)
                  ·
                    refine ⟨854798091948433623894127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558923157058312660768677 854798091948433623894127)
                    ·
                      rfl

theorem cell22_2497070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2497070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497070 prefixEnd_2497070 := by exact prefixLift 2497070
  have htrace : WordTrace (prefixWord ++ tailWord_2497070) baseStart_2497070 baseEnd_2497070 := by
    simpa [prefixWord, tailWord_2497070, baseEnd_2497070] using wordTrace_append hprefix tailTrace_2497070
  have hstable : (prefixWord ++ tailWord_2497070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497070).length < 2 ^ (prefixWord ++ tailWord_2497070).sum := by decide
  have hdescent : baseEnd_2497070 < baseStart_2497070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497109 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_2497109 : Nat := 118140960795 + 2497109 * 2 ^ 59
def prefixEnd_2497109 : Nat := 4983230072969 + 3 ^ 40 * 2497109 * 2
def baseEnd_2497109 : Nat := 854811442445450522169007

theorem tailTrace_2497109 : CollatzResearch.WordTrace tailWord_2497109 prefixEnd_2497109 854811442445450522169007 := by
  unfold tailWord_2497109
  simp only [CollatzResearch.WordTrace]
  refine ⟨91077047510408040109118381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60718031673605360072745587 91077047510408040109118381)
  ·
    refine ⟨34153892816403015040919393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91077047510408040109118381 34153892816403015040919393)
    ·
      refine ⟨25615419612302261280689545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34153892816403015040919393 25615419612302261280689545)
      ·
        refine ⟨19211564709226695960517159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25615419612302261280689545 19211564709226695960517159)
        ·
          refine ⟨28817347063840043940775739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19211564709226695960517159 28817347063840043940775739)
          ·
            refine ⟨43226020595760065911163609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28817347063840043940775739 43226020595760065911163609)
            ·
              refine ⟨32419515446820049433372707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43226020595760065911163609 32419515446820049433372707)
              ·
                refine ⟨48629273170230074150059061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32419515446820049433372707 48629273170230074150059061)
                ·
                  refine ⟨4558994359709069451568037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48629273170230074150059061 4558994359709069451568037)
                  ·
                    refine ⟨854811442445450522169007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558994359709069451568037 854811442445450522169007)
                    ·
                      rfl

theorem cell22_2497109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_2497109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497109 prefixEnd_2497109 := by exact prefixLift 2497109
  have htrace : WordTrace (prefixWord ++ tailWord_2497109) baseStart_2497109 baseEnd_2497109 := by
    simpa [prefixWord, tailWord_2497109, baseEnd_2497109] using wordTrace_append hprefix tailTrace_2497109
  have hstable : (prefixWord ++ tailWord_2497109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497109).length < 2 ^ (prefixWord ++ tailWord_2497109).sum := by decide
  have hdescent : baseEnd_2497109 < baseStart_2497109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497124 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 6]
def baseStart_2497124 : Nat := 118140960795 + 2497124 * 2 ^ 59
def prefixEnd_2497124 : Nat := 4983230072969 + 3 ^ 40 * 2497124 * 2
def baseEnd_2497124 : Nat := 284938859083998494347987

theorem tailTrace_2497124 : CollatzResearch.WordTrace tailWord_2497124 prefixEnd_2497124 284938859083998494347987 := by
  unfold tailWord_2497124
  simp only [CollatzResearch.WordTrace]
  refine ⟨45538797302676848835457213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60718396403569131780609617 45538797302676848835457213)
  ·
    refine ⟨17077048988503818313296455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45538797302676848835457213 17077048988503818313296455)
    ·
      refine ⟨25615573482755727469944683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17077048988503818313296455 25615573482755727469944683)
      ·
        refine ⟨38423360224133591204917025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25615573482755727469944683 38423360224133591204917025)
        ·
          refine ⟨28817520168100193403687769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38423360224133591204917025 28817520168100193403687769)
          ·
            refine ⟨21613140126075145052765827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28817520168100193403687769 21613140126075145052765827)
            ·
              refine ⟨32419710189112717579148741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21613140126075145052765827 32419710189112717579148741)
              ·
                refine ⟨6078695660458634546090389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32419710189112717579148741 6078695660458634546090389)
                ·
                  refine ⟨284938859083998494347987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6078695660458634546090389 284938859083998494347987)
                  ·
                    rfl

theorem cell22_2497124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_2497124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497124 prefixEnd_2497124 := by exact prefixLift 2497124
  have htrace : WordTrace (prefixWord ++ tailWord_2497124) baseStart_2497124 baseEnd_2497124 := by
    simpa [prefixWord, tailWord_2497124, baseEnd_2497124] using wordTrace_append hprefix tailTrace_2497124
  have hstable : (prefixWord ++ tailWord_2497124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497124).length < 2 ^ (prefixWord ++ tailWord_2497124).sum := by decide
  have hdescent : baseEnd_2497124 < baseStart_2497124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497259 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 10]
def baseStart_2497259 : Nat := 118140960795 + 2497259 * 2 ^ 59
def prefixEnd_2497259 : Nat := 4983230072969 + 3 ^ 40 * 2497259 * 2
def baseEnd_2497259 : Nat := 284954263503633376972849

theorem tailTrace_2497259 : CollatzResearch.WordTrace tailWord_2497259 prefixEnd_2497259 284954263503633376972849 := by
  unfold tailWord_2497259
  simp only [CollatzResearch.WordTrace]
  refine ⟨91082518459864615727078831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60721678973243077151385887 91082518459864615727078831)
  ·
    refine ⟨136623777689796923590618247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91082518459864615727078831 136623777689796923590618247)
    ·
      refine ⟨204935666534695385385927371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136623777689796923590618247 204935666534695385385927371)
      ·
        refine ⟨307403499802043078078891057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204935666534695385385927371 307403499802043078078891057)
        ·
          refine ⟨230552624851532308559168293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307403499802043078078891057 230552624851532308559168293)
          ·
            refine ⟨43228617159662307854844055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230552624851532308559168293 43228617159662307854844055)
            ·
              refine ⟨64842925739493461782266083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43228617159662307854844055 64842925739493461782266083)
              ·
                refine ⟨97264388609240192673399125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64842925739493461782266083 97264388609240192673399125)
                ·
                  refine ⟨284954263503633376972849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 97264388609240192673399125 284954263503633376972849)
                  ·
                    rfl

theorem cell22_2497259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 10].length) (baseStart_2497259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497259 prefixEnd_2497259 := by exact prefixLift 2497259
  have htrace : WordTrace (prefixWord ++ tailWord_2497259) baseStart_2497259 baseEnd_2497259 := by
    simpa [prefixWord, tailWord_2497259, baseEnd_2497259] using wordTrace_append hprefix tailTrace_2497259
  have hstable : (prefixWord ++ tailWord_2497259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497259).length < 2 ^ (prefixWord ++ tailWord_2497259).sum := by decide
  have hdescent : baseEnd_2497259 < baseStart_2497259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497269 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2497269 : Nat := 118140960795 + 2497269 * 2 ^ 59
def prefixEnd_2497269 : Nat := 4983230072969 + 3 ^ 40 * 2497269 * 2
def baseEnd_2497269 : Nat := 854866213715263438168517

theorem tailTrace_2497269 : CollatzResearch.WordTrace tailWord_2497269 prefixEnd_2497269 854866213715263438168517 := by
  unfold tailWord_2497269
  simp only [CollatzResearch.WordTrace]
  refine ⟨91082883189828387434942861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60721922126552258289961907 91082883189828387434942861)
  ·
    refine ⟨34156081196185645288103573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91082883189828387434942861 34156081196185645288103573)
    ·
      refine ⟨1601066306071202122879855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34156081196185645288103573 1601066306071202122879855)
      ·
        refine ⟨2401599459106803184319783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601066306071202122879855 2401599459106803184319783)
        ·
          refine ⟨3602399188660204776479675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401599459106803184319783 3602399188660204776479675)
          ·
            refine ⟨5403598782990307164719513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602399188660204776479675 5403598782990307164719513)
            ·
              refine ⟨4052699087242730373539635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5403598782990307164719513 4052699087242730373539635)
              ·
                refine ⟨6079048630864095560309453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052699087242730373539635 6079048630864095560309453)
                ·
                  refine ⟨2279643236574035835116045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6079048630864095560309453 2279643236574035835116045)
                  ·
                    refine ⟨854866213715263438168517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279643236574035835116045 854866213715263438168517)
                    ·
                      rfl

theorem cell22_2497269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2497269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497269 prefixEnd_2497269 := by exact prefixLift 2497269
  have htrace : WordTrace (prefixWord ++ tailWord_2497269) baseStart_2497269 baseEnd_2497269 := by
    simpa [prefixWord, tailWord_2497269, baseEnd_2497269] using wordTrace_append hprefix tailTrace_2497269
  have hstable : (prefixWord ++ tailWord_2497269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497269).length < 2 ^ (prefixWord ++ tailWord_2497269).sum := by decide
  have hdescent : baseEnd_2497269 < baseStart_2497269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497276 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 6]
def baseStart_2497276 : Nat := 118140960795 + 2497276 * 2 ^ 59
def prefixEnd_2497276 : Nat := 4983230072969 + 3 ^ 40 * 2497276 * 2
def baseEnd_2497276 : Nat := 284956203319439251081165

theorem tailTrace_2497276 : CollatzResearch.WordTrace tailWord_2497276 prefixEnd_2497276 284956203319439251081165 := by
  unfold tailWord_2497276
  simp only [CollatzResearch.WordTrace]
  refine ⟨45541569250401513815223841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60722092333868685086965121 45541569250401513815223841)
  ·
    refine ⟨34156176937801135361417881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45541569250401513815223841 34156176937801135361417881)
    ·
      refine ⟨25617132703350851521063411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34156176937801135361417881 25617132703350851521063411)
      ·
        refine ⟨38425699055026277281595117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25617132703350851521063411 38425699055026277281595117)
        ·
          refine ⟨14409637145634853980598169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38425699055026277281595117 14409637145634853980598169)
          ·
            refine ⟨10807227859226140485448627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14409637145634853980598169 10807227859226140485448627)
            ·
              refine ⟨16210841788839210728172941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10807227859226140485448627 16210841788839210728172941)
              ·
                refine ⟨6079065670814704023064853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16210841788839210728172941 6079065670814704023064853)
                ·
                  refine ⟨284956203319439251081165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6079065670814704023064853 284956203319439251081165)
                  ·
                    rfl

theorem cell22_2497276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_2497276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497276 prefixEnd_2497276 := by exact prefixLift 2497276
  have htrace : WordTrace (prefixWord ++ tailWord_2497276) baseStart_2497276 baseEnd_2497276 := by
    simpa [prefixWord, tailWord_2497276, baseEnd_2497276] using wordTrace_append hprefix tailTrace_2497276
  have hstable : (prefixWord ++ tailWord_2497276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497276).length < 2 ^ (prefixWord ++ tailWord_2497276).sum := by decide
  have hdescent : baseEnd_2497276 < baseStart_2497276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497306 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_2497306 : Nat := 118140960795 + 2497306 * 2 ^ 59
def prefixEnd_2497306 : Nat := 4983230072969 + 3 ^ 40 * 2497306 * 2
def baseEnd_2497306 : Nat := 854878879571407674993403

theorem tailTrace_2497306 : CollatzResearch.WordTrace tailWord_2497306 prefixEnd_2497306 854878879571407674993403 := by
  unfold tailWord_2497306
  simp only [CollatzResearch.WordTrace]
  refine ⟨22771058172673585688509943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60722821793796228502693181 22771058172673585688509943)
  ·
    refine ⟨34156587259010378532764915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22771058172673585688509943 34156587259010378532764915)
    ·
      refine ⟨51234880888515567799147373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34156587259010378532764915 51234880888515567799147373)
      ·
        refine ⟨19213080333193337924680265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51234880888515567799147373 19213080333193337924680265)
        ·
          refine ⟨14409810249895003443510199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19213080333193337924680265 14409810249895003443510199)
          ·
            refine ⟨21614715374842505165265299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14409810249895003443510199 21614715374842505165265299)
            ·
              refine ⟨32422073062263757747897949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21614715374842505165265299 32422073062263757747897949)
              ·
                refine ⟨12158277398348909155461731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32422073062263757747897949 12158277398348909155461731)
                ·
                  refine ⟨18237416097523363733192597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12158277398348909155461731 18237416097523363733192597)
                  ·
                    refine ⟨854878879571407674993403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18237416097523363733192597 854878879571407674993403)
                    ·
                      rfl

theorem cell22_2497306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_2497306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497306 prefixEnd_2497306 := by exact prefixLift 2497306
  have htrace : WordTrace (prefixWord ++ tailWord_2497306) baseStart_2497306 baseEnd_2497306 := by
    simpa [prefixWord, tailWord_2497306, baseEnd_2497306] using wordTrace_append hprefix tailTrace_2497306
  have hstable : (prefixWord ++ tailWord_2497306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497306).length < 2 ^ (prefixWord ++ tailWord_2497306).sum := by decide
  have hdescent : baseEnd_2497306 < baseStart_2497306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497308 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_2497308 : Nat := 118140960795 + 2497308 * 2 ^ 59
def prefixEnd_2497308 : Nat := 4983230072969 + 3 ^ 40 * 2497308 * 2
def baseEnd_2497308 : Nat := 854879564212280336443397

theorem tailTrace_2497308 : CollatzResearch.WordTrace tailWord_2497308 prefixEnd_2497308 854879564212280336443397 := by
  unfold tailWord_2497308
  simp only [CollatzResearch.WordTrace]
  refine ⟨45542152818343548547806289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60722870424458064730408385 45542152818343548547806289)
  ·
    refine ⟨34156614613757661410854717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45542152818343548547806289 34156614613757661410854717)
    ·
      refine ⟨12808730480159123029070519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34156614613757661410854717 12808730480159123029070519)
      ·
        refine ⟨19213095720238684543605779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12808730480159123029070519 19213095720238684543605779)
        ·
          refine ⟨28819643580358026815408669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19213095720238684543605779 28819643580358026815408669)
          ·
            refine ⟨10807366342634260055778251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28819643580358026815408669 10807366342634260055778251)
            ·
              refine ⟨16211049513951390083667377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10807366342634260055778251 16211049513951390083667377)
              ·
                refine ⟨12158287135463542562750533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16211049513951390083667377 12158287135463542562750533)
                ·
                  refine ⟨2279678837899414230515725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12158287135463542562750533 2279678837899414230515725)
                  ·
                    refine ⟨854879564212280336443397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279678837899414230515725 854879564212280336443397)
                    ·
                      rfl

theorem cell22_2497308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_2497308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497308 prefixEnd_2497308 := by exact prefixLift 2497308
  have htrace : WordTrace (prefixWord ++ tailWord_2497308) baseStart_2497308 baseEnd_2497308 := by
    simpa [prefixWord, tailWord_2497308, baseEnd_2497308] using wordTrace_append hprefix tailTrace_2497308
  have hstable : (prefixWord ++ tailWord_2497308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497308).length < 2 ^ (prefixWord ++ tailWord_2497308).sum := by decide
  have hdescent : baseEnd_2497308 < baseStart_2497308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497338 : List Nat := [3, 1, 1, 1, 6, 1, 2, 7]
def baseStart_2497338 : Nat := 118140960795 + 2497338 * 2 ^ 59
def prefixEnd_2497338 : Nat := 4983230072969 + 3 ^ 40 * 2497338 * 2
def baseEnd_2497338 : Nat := 94987759313930028688145

theorem tailTrace_2497338 : CollatzResearch.WordTrace tailWord_2497338 prefixEnd_2497338 94987759313930028688145 := by
  unfold tailWord_2497338
  simp only [CollatzResearch.WordTrace]
  refine ⟨22771349956644603054801167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60723599884385608146136445 22771349956644603054801167)
  ·
    refine ⟨34157024934966904582201751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22771349956644603054801167 34157024934966904582201751)
    ·
      refine ⟨51235537402450356873302627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34157024934966904582201751 51235537402450356873302627)
      ·
        refine ⟨76853306103675535309953941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51235537402450356873302627 76853306103675535309953941)
        ·
          refine ⟨3602498723609790717654091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76853306103675535309953941 3602498723609790717654091)
          ·
            refine ⟨5403748085414686076481137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602498723609790717654091 5403748085414686076481137)
            ·
              refine ⟨4052811064061014557360853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5403748085414686076481137 4052811064061014557360853)
              ·
                refine ⟨94987759313930028688145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4052811064061014557360853 94987759313930028688145)
                ·
                  rfl

theorem cell22_2497338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_2497338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497338 prefixEnd_2497338 := by exact prefixLift 2497338
  have htrace : WordTrace (prefixWord ++ tailWord_2497338) baseStart_2497338 baseEnd_2497338 := by
    simpa [prefixWord, tailWord_2497338, baseEnd_2497338] using wordTrace_append hprefix tailTrace_2497338
  have hstable : (prefixWord ++ tailWord_2497338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497338).length < 2 ^ (prefixWord ++ tailWord_2497338).sum := by decide
  have hdescent : baseEnd_2497338 < baseStart_2497338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497342 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_2497342 : Nat := 118140960795 + 2497342 * 2 ^ 59
def prefixEnd_2497342 : Nat := 4983230072969 + 3 ^ 40 * 2497342 * 2
def baseEnd_2497342 : Nat := 854891203107115581093293

theorem tailTrace_2497342 : CollatzResearch.WordTrace tailWord_2497342 prefixEnd_2497342 854891203107115581093293 := by
  unfold tailWord_2497342
  simp only [CollatzResearch.WordTrace]
  refine ⟨11385693214820490112793785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60723697145709280601566853 11385693214820490112793785)
  ·
    refine ⟨8539269911115367584595339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11385693214820490112793785 8539269911115367584595339)
    ·
      refine ⟨12808904866673051376893009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8539269911115367584595339 12808904866673051376893009)
      ·
        refine ⟨9606678650004788532669757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12808904866673051376893009 9606678650004788532669757)
        ·
          refine ⟨3602504493751795699751159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9606678650004788532669757 3602504493751795699751159)
          ·
            refine ⟨5403756740627693549626739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602504493751795699751159 5403756740627693549626739)
            ·
              refine ⟨8105635110941540324440109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5403756740627693549626739 8105635110941540324440109)
              ·
                refine ⟨3039613166603077621665041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8105635110941540324440109 3039613166603077621665041)
                ·
                  refine ⟨2279709874952308216248781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3039613166603077621665041 2279709874952308216248781)
                  ·
                    refine ⟨854891203107115581093293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279709874952308216248781 854891203107115581093293)
                    ·
                      rfl

theorem cell22_2497342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_2497342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497342 prefixEnd_2497342 := by exact prefixLift 2497342
  have htrace : WordTrace (prefixWord ++ tailWord_2497342) baseStart_2497342 baseEnd_2497342 := by
    simpa [prefixWord, tailWord_2497342, baseEnd_2497342] using wordTrace_append hprefix tailTrace_2497342
  have hstable : (prefixWord ++ tailWord_2497342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497342).length < 2 ^ (prefixWord ++ tailWord_2497342).sum := by decide
  have hdescent : baseEnd_2497342 < baseStart_2497342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497357 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2497357 : Nat := 118140960795 + 2497357 * 2 ^ 59
def prefixEnd_2497357 : Nat := 4983230072969 + 3 ^ 40 * 2497357 * 2
def baseEnd_2497357 : Nat := 854896337913660541968247

theorem tailTrace_2497357 : CollatzResearch.WordTrace tailWord_2497357 prefixEnd_2497357 854896337913660541968247 := by
  unfold tailWord_2497357
  simp only [CollatzResearch.WordTrace]
  refine ⟨91086092813509578464146325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60724061875673052309430883 91086092813509578464146325)
  ·
    refine ⟨4269660600633261490506859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91086092813509578464146325 4269660600633261490506859)
    ·
      refine ⟨6404490900949892235760289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4269660600633261490506859 6404490900949892235760289)
      ·
        refine ⟨4803368175712419176820217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6404490900949892235760289 4803368175712419176820217)
        ·
          refine ⟨3602526131784314382615163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4803368175712419176820217 3602526131784314382615163)
          ·
            refine ⟨5403789197676471573922745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602526131784314382615163 5403789197676471573922745)
            ·
              refine ⟨4052841898257353680442059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5403789197676471573922745 4052841898257353680442059)
              ·
                refine ⟨6079262847386030520663089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4052841898257353680442059 6079262847386030520663089)
                ·
                  refine ⟨4559447135539522890497317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079262847386030520663089 4559447135539522890497317)
                  ·
                    refine ⟨854896337913660541968247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4559447135539522890497317 854896337913660541968247)
                    ·
                      rfl

theorem cell22_2497357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2497357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497357 prefixEnd_2497357 := by exact prefixLift 2497357
  have htrace : WordTrace (prefixWord ++ tailWord_2497357) baseStart_2497357 baseEnd_2497357 := by
    simpa [prefixWord, tailWord_2497357, baseEnd_2497357] using wordTrace_append hprefix tailTrace_2497357
  have hstable : (prefixWord ++ tailWord_2497357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497357).length < 2 ^ (prefixWord ++ tailWord_2497357).sum := by decide
  have hdescent : baseEnd_2497357 < baseStart_2497357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497383 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 5]
def baseStart_2497383 : Nat := 118140960795 + 2497383 * 2 ^ 59
def prefixEnd_2497383 : Nat := 4983230072969 + 3 ^ 40 * 2497383 * 2
def baseEnd_2497383 : Nat := 284968412748335046939389

theorem tailTrace_2497383 : CollatzResearch.WordTrace tailWord_2497383 prefixEnd_2497383 284968412748335046939389 := by
  unfold tailWord_2497383
  simp only [CollatzResearch.WordTrace]
  refine ⟨91087041111415384904592803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60724694074276923269728535 91087041111415384904592803)
  ·
    refine ⟨136630561667123077356889205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91087041111415384904592803 136630561667123077356889205)
    ·
      refine ⟨12809115156292788502208363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136630561667123077356889205 12809115156292788502208363)
      ·
        refine ⟨19213672734439182753312545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12809115156292788502208363 19213672734439182753312545)
        ·
          refine ⟨14410254550829387064984409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19213672734439182753312545 14410254550829387064984409)
          ·
            refine ⟨10807690913122040298738307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14410254550829387064984409 10807690913122040298738307)
            ·
              refine ⟨16211536369683060448107461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10807690913122040298738307 16211536369683060448107461)
              ·
                refine ⟨3039663069315573834020149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16211536369683060448107461 3039663069315573834020149)
                ·
                  refine ⟨284968412748335046939389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3039663069315573834020149 284968412748335046939389)
                  ·
                    rfl

theorem cell22_2497383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 5].length) (baseStart_2497383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497383 prefixEnd_2497383 := by exact prefixLift 2497383
  have htrace : WordTrace (prefixWord ++ tailWord_2497383) baseStart_2497383 baseEnd_2497383 := by
    simpa [prefixWord, tailWord_2497383, baseEnd_2497383] using wordTrace_append hprefix tailTrace_2497383
  have hstable : (prefixWord ++ tailWord_2497383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497383).length < 2 ^ (prefixWord ++ tailWord_2497383).sum := by decide
  have hdescent : baseEnd_2497383 < baseStart_2497383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497387 : List Nat := [1, 1, 1, 1, 2, 2, 8, 2, 1, 3]
def baseStart_2497387 : Nat := 118140960795 + 2497387 * 2 ^ 59
def prefixEnd_2497387 : Nat := 4983230072969 + 3 ^ 40 * 2497387 * 2
def baseEnd_2497387 : Nat := 854906607526750463718155

theorem tailTrace_2497387 : CollatzResearch.WordTrace tailWord_2497387 prefixEnd_2497387 854906607526750463718155 := by
  unfold tailWord_2497387
  simp only [CollatzResearch.WordTrace]
  refine ⟨91087187003400893587738415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60724791335600595725158943 91087187003400893587738415)
  ·
    refine ⟨136630780505101340381607623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91087187003400893587738415 136630780505101340381607623)
    ·
      refine ⟨204946170757652010572411435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136630780505101340381607623 204946170757652010572411435)
      ·
        refine ⟨307419256136478015858617153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204946170757652010572411435 307419256136478015858617153)
        ·
          refine ⟨230564442102358511893962865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307419256136478015858617153 230564442102358511893962865)
          ·
            refine ⟨172923331576768883920472149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230564442102358511893962865 172923331576768883920472149)
            ·
              refine ⟨2026445291915260358443033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 172923331576768883920472149 2026445291915260358443033)
              ·
                refine ⟨1519833968936445268832275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026445291915260358443033 1519833968936445268832275)
                ·
                  refine ⟨2279750953404667903248413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519833968936445268832275 2279750953404667903248413)
                  ·
                    refine ⟨854906607526750463718155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2279750953404667903248413 854906607526750463718155)
                    ·
                      rfl

theorem cell22_2497387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 3].length) (baseStart_2497387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497387 prefixEnd_2497387 := by exact prefixLift 2497387
  have htrace : WordTrace (prefixWord ++ tailWord_2497387) baseStart_2497387 baseEnd_2497387 := by
    simpa [prefixWord, tailWord_2497387, baseEnd_2497387] using wordTrace_append hprefix tailTrace_2497387
  have hstable : (prefixWord ++ tailWord_2497387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497387).length < 2 ^ (prefixWord ++ tailWord_2497387).sum := by decide
  have hdescent : baseEnd_2497387 < baseStart_2497387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497413 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_2497413 : Nat := 118140960795 + 2497413 * 2 ^ 59
def prefixEnd_2497413 : Nat := 4983230072969 + 3 ^ 40 * 2497413 * 2
def baseEnd_2497413 : Nat := 854915507858095062568075

theorem tailTrace_2497413 : CollatzResearch.WordTrace tailWord_2497413 prefixEnd_2497413 854915507858095062568075 := by
  unfold tailWord_2497413
  simp only [CollatzResearch.WordTrace]
  refine ⟨91088135301306700028184893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60725423534204466685456595 91088135301306700028184893)
  ·
    refine ⟨34158050737990012510569335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91088135301306700028184893 34158050737990012510569335)
    ·
      refine ⟨51237076106985018765854003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34158050737990012510569335 51237076106985018765854003)
      ·
        refine ⟨76855614160477528148781005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51237076106985018765854003 76855614160477528148781005)
        ·
          refine ⟨28820855310179073055792877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76855614160477528148781005 28820855310179073055792877)
          ·
            refine ⟨10807820741317152395922329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28820855310179073055792877 10807820741317152395922329)
            ·
              refine ⟨8105865555987864296941747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10807820741317152395922329 8105865555987864296941747)
              ·
                refine ⟨12158798333981796445412621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8105865555987864296941747 12158798333981796445412621)
                ·
                  refine ⟨4559549375243173667029733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12158798333981796445412621 4559549375243173667029733)
                  ·
                    refine ⟨854915507858095062568075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4559549375243173667029733 854915507858095062568075)
                    ·
                      rfl

theorem cell22_2497413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_2497413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497413 prefixEnd_2497413 := by exact prefixLift 2497413
  have htrace : WordTrace (prefixWord ++ tailWord_2497413) baseStart_2497413 baseEnd_2497413 := by
    simpa [prefixWord, tailWord_2497413, baseEnd_2497413] using wordTrace_append hprefix tailTrace_2497413
  have hstable : (prefixWord ++ tailWord_2497413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497413).length < 2 ^ (prefixWord ++ tailWord_2497413).sum := by decide
  have hdescent : baseEnd_2497413 < baseStart_2497413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497428 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 8]
def baseStart_2497428 : Nat := 118140960795 + 2497428 * 2 ^ 59
def prefixEnd_2497428 : Nat := 4983230072969 + 3 ^ 40 * 2497428 * 2
def baseEnd_2497428 : Nat := 284973547554880007814343

theorem tailTrace_2497428 : CollatzResearch.WordTrace tailWord_2497428 prefixEnd_2497428 284973547554880007814343 := by
  unfold tailWord_2497428
  simp only [CollatzResearch.WordTrace]
  refine ⟨45544341198126178794990469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60725788264168238393320625 45544341198126178794990469)
  ·
    refine ⟨8539563974648658524060713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45544341198126178794990469 8539563974648658524060713)
    ·
      refine ⟨6404672980986493893045535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8539563974648658524060713 6404672980986493893045535)
      ·
        refine ⟨9607009471479740839568303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6404672980986493893045535 9607009471479740839568303)
        ·
          refine ⟨14410514207219611259352455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9607009471479740839568303 14410514207219611259352455)
          ·
            refine ⟨21615771310829416889028683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14410514207219611259352455 21615771310829416889028683)
            ·
              refine ⟨32423656966244125333543025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21615771310829416889028683 32423656966244125333543025)
              ·
                refine ⟨24317742724683094000157269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32423656966244125333543025 24317742724683094000157269)
                ·
                  refine ⟨284973547554880007814343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24317742724683094000157269 284973547554880007814343)
                  ·
                    rfl

theorem cell22_2497428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2497428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497428 prefixEnd_2497428 := by exact prefixLift 2497428
  have htrace : WordTrace (prefixWord ++ tailWord_2497428) baseStart_2497428 baseEnd_2497428 := by
    simpa [prefixWord, tailWord_2497428, baseEnd_2497428] using wordTrace_append hprefix tailTrace_2497428
  have hstable : (prefixWord ++ tailWord_2497428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497428).length < 2 ^ (prefixWord ++ tailWord_2497428).sum := by decide
  have hdescent : baseEnd_2497428 < baseStart_2497428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497490 : List Nat := [3, 2, 2, 3, 1, 3, 8]
def baseStart_2497490 : Nat := 118140960795 + 2497490 * 2 ^ 59
def prefixEnd_2497490 : Nat := 4983230072969 + 3 ^ 40 * 2497490 * 2
def baseEnd_2497490 : Nat := 31664513575247871421957

theorem tailTrace_2497490 : CollatzResearch.WordTrace tailWord_2497490 prefixEnd_2497490 31664513575247871421957 := by
  unfold tailWord_2497490
  simp only [CollatzResearch.WordTrace]
  refine ⟨22772735930506935544684481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60727295814685161452491949 22772735930506935544684481)
  ·
    refine ⟨17079551947880201658513361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22772735930506935544684481 17079551947880201658513361)
    ·
      refine ⟨12809663960910151243885021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17079551947880201658513361 12809663960910151243885021)
      ·
        refine ⟨4803623985341306716456883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12809663960910151243885021 4803623985341306716456883)
        ·
          refine ⟨7205435978011960074685325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4803623985341306716456883 7205435978011960074685325)
          ·
            refine ⟨2702038491754485028006997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7205435978011960074685325 2702038491754485028006997)
            ·
              refine ⟨31664513575247871421957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2702038491754485028006997 31664513575247871421957)
              ·
                rfl

theorem cell22_2497490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 8].length) (baseStart_2497490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497490 prefixEnd_2497490 := by exact prefixLift 2497490
  have htrace : WordTrace (prefixWord ++ tailWord_2497490) baseStart_2497490 baseEnd_2497490 := by
    simpa [prefixWord, tailWord_2497490, baseEnd_2497490] using wordTrace_append hprefix tailTrace_2497490
  have hstable : (prefixWord ++ tailWord_2497490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497490).length < 2 ^ (prefixWord ++ tailWord_2497490).sum := by decide
  have hdescent : baseEnd_2497490 < baseStart_2497490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497533 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2497533 : Nat := 118140960795 + 2497533 * 2 ^ 59
def prefixEnd_2497533 : Nat := 4983230072969 + 3 ^ 40 * 2497533 * 2
def baseEnd_2497533 : Nat := 854956586310454749567707

theorem tailTrace_2497533 : CollatzResearch.WordTrace tailWord_2497533 prefixEnd_2497533 854956586310454749567707 := by
  unfold tailWord_2497533
  simp only [CollatzResearch.WordTrace]
  refine ⟨91092512060871960522553253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60728341373914640348368835 91092512060871960522553253)
  ·
    refine ⟨17079846011413492597978735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91092512060871960522553253 17079846011413492597978735)
    ·
      refine ⟨25619769017120238896968103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17079846011413492597978735 25619769017120238896968103)
      ·
        refine ⟨38429653525680358345452155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25619769017120238896968103 38429653525680358345452155)
        ·
          refine ⟨57644480288520537518178233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38429653525680358345452155 57644480288520537518178233)
          ·
            refine ⟨43233360216390403138633675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57644480288520537518178233 43233360216390403138633675)
            ·
              refine ⟨64850040324585604707950513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43233360216390403138633675 64850040324585604707950513)
              ·
                refine ⟨48637530243439203530962885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64850040324585604707950513 48637530243439203530962885)
                ·
                  refine ⟨9119536920644850662055541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48637530243439203530962885 9119536920644850662055541)
                  ·
                    refine ⟨854956586310454749567707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9119536920644850662055541 854956586310454749567707)
                    ·
                      rfl

theorem cell22_2497533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2497533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497533 prefixEnd_2497533 := by exact prefixLift 2497533
  have htrace : WordTrace (prefixWord ++ tailWord_2497533) baseStart_2497533 baseEnd_2497533 := by
    simpa [prefixWord, tailWord_2497533, baseEnd_2497533] using wordTrace_append hprefix tailTrace_2497533
  have hstable : (prefixWord ++ tailWord_2497533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497533).length < 2 ^ (prefixWord ++ tailWord_2497533).sum := by decide
  have hdescent : baseEnd_2497533 < baseStart_2497533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497582 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2497582 : Nat := 118140960795 + 2497582 * 2 ^ 59
def prefixEnd_2497582 : Nat := 4983230072969 + 3 ^ 40 * 2497582 * 2
def baseEnd_2497582 : Nat := 854973360011834955092557

theorem tailTrace_2497582 : CollatzResearch.WordTrace tailWord_2497582 prefixEnd_2497582 854973360011834955092557 := by
  unfold tailWord_2497582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11386787404711805236385875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60729532825129627927391333 11386787404711805236385875)
  ·
    refine ⟨17080181107067707854578813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11386787404711805236385875 17080181107067707854578813)
    ·
      refine ⟨6405067915150390445467055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17080181107067707854578813 6405067915150390445467055)
      ·
        refine ⟨9607601872725585668200583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6405067915150390445467055 9607601872725585668200583)
        ·
          refine ⟨14411402809088378502300875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9607601872725585668200583 14411402809088378502300875)
          ·
            refine ⟨21617104213632567753451313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14411402809088378502300875 21617104213632567753451313)
            ·
              refine ⟨16212828160224425815088485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21617104213632567753451313 16212828160224425815088485)
              ·
                refine ⟨3039905280042079840329091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16212828160224425815088485 3039905280042079840329091)
                ·
                  refine ⟨4559857920063119760493637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039905280042079840329091 4559857920063119760493637)
                  ·
                    refine ⟨854973360011834955092557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4559857920063119760493637 854973360011834955092557)
                    ·
                      rfl

theorem cell22_2497582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2497582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497582 prefixEnd_2497582 := by exact prefixLift 2497582
  have htrace : WordTrace (prefixWord ++ tailWord_2497582) baseStart_2497582 baseEnd_2497582 := by
    simpa [prefixWord, tailWord_2497582, baseEnd_2497582] using wordTrace_append hprefix tailTrace_2497582
  have hstable : (prefixWord ++ tailWord_2497582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497582).length < 2 ^ (prefixWord ++ tailWord_2497582).sum := by decide
  have hdescent : baseEnd_2497582 < baseStart_2497582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497597 : List Nat := [1, 4, 1, 3, 1, 2, 1, 5, 4]
def baseStart_2497597 : Nat := 118140960795 + 2497597 * 2 ^ 59
def prefixEnd_2497597 : Nat := 4983230072969 + 3 ^ 40 * 2497597 * 2
def baseEnd_2497597 : Nat := 284992831606126638655837

theorem tailTrace_2497597 : CollatzResearch.WordTrace tailWord_2497597 prefixEnd_2497597 284992831606126638655837 := by
  unfold tailWord_2497597
  simp only [CollatzResearch.WordTrace]
  refine ⟨91094846332640099452883045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60729897555093399635255363 91094846332640099452883045)
  ·
    refine ⟨17080283687370018647415571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91094846332640099452883045 17080283687370018647415571)
    ·
      refine ⟨25620425531055027971123357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17080283687370018647415571 25620425531055027971123357)
      ·
        refine ⟨9607659574145635489171259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25620425531055027971123357 9607659574145635489171259)
        ·
          refine ⟨14411489361218453233756889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9607659574145635489171259 14411489361218453233756889)
          ·
            refine ⟨10808617020913839925317667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14411489361218453233756889 10808617020913839925317667)
            ·
              refine ⟨16212925531370759887976501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10808617020913839925317667 16212925531370759887976501)
              ·
                refine ⟨1519961768566008739497797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16212925531370759887976501 1519961768566008739497797)
                ·
                  refine ⟨284992831606126638655837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1519961768566008739497797 284992831606126638655837)
                  ·
                    rfl

theorem cell22_2497597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_2497597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497597 prefixEnd_2497597 := by exact prefixLift 2497597
  have htrace : WordTrace (prefixWord ++ tailWord_2497597) baseStart_2497597 baseEnd_2497597 := by
    simpa [prefixWord, tailWord_2497597, baseEnd_2497597] using wordTrace_append hprefix tailTrace_2497597
  have hstable : (prefixWord ++ tailWord_2497597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497597).length < 2 ^ (prefixWord ++ tailWord_2497597).sum := by decide
  have hdescent : baseEnd_2497597 < baseStart_2497597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497608 : List Nat := [2, 1, 3, 1, 1, 1, 13]
def baseStart_2497608 : Nat := 118140960795 + 2497608 * 2 ^ 59
def prefixEnd_2497608 : Nat := 4983230072969 + 3 ^ 40 * 2497608 * 2
def baseEnd_2497608 : Nat := 31666009642339983479351

theorem tailTrace_2497608 : CollatzResearch.WordTrace tailWord_2497608 prefixEnd_2497608 31666009642339983479351 := by
  unfold tailWord_2497608
  simp only [CollatzResearch.WordTrace]
  refine ⟨45547623767800124165766739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60730165023733498887688985 45547623767800124165766739)
  ·
    refine ⟨68321435651700186248650109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45547623767800124165766739 68321435651700186248650109)
    ·
      refine ⟨25620538369387569843243791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68321435651700186248650109 25620538369387569843243791)
      ·
        refine ⟨38430807554081354764865687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25620538369387569843243791 38430807554081354764865687)
        ·
          refine ⟨57646211331122032147298531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38430807554081354764865687 57646211331122032147298531)
          ·
            refine ⟨86469316996683048220947797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57646211331122032147298531 86469316996683048220947797)
            ·
              refine ⟨31666009642339983479351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 86469316996683048220947797 31666009642339983479351)
              ·
                rfl

theorem cell22_2497608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 13].length) (baseStart_2497608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497608 prefixEnd_2497608 := by exact prefixLift 2497608
  have htrace : WordTrace (prefixWord ++ tailWord_2497608) baseStart_2497608 baseEnd_2497608 := by
    simpa [prefixWord, tailWord_2497608, baseEnd_2497608] using wordTrace_append hprefix tailTrace_2497608
  have hstable : (prefixWord ++ tailWord_2497608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497608).length < 2 ^ (prefixWord ++ tailWord_2497608).sum := by decide
  have hdescent : baseEnd_2497608 < baseStart_2497608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497610 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_2497610 : Nat := 118140960795 + 2497610 * 2 ^ 59
def prefixEnd_2497610 : Nat := 4983230072969 + 3 ^ 40 * 2497610 * 2
def baseEnd_2497610 : Nat := 854982944984052215392471

theorem tailTrace_2497610 : CollatzResearch.WordTrace tailWord_2497610 prefixEnd_2497610 854982944984052215392471 := by
  unfold tailWord_2497610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22773830120398250668276571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60730213654395335115404189 22773830120398250668276571)
  ·
    refine ⟨34160745180597376002414857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22773830120398250668276571 34160745180597376002414857)
    ·
      refine ⟨25620558885448032001811143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34160745180597376002414857 25620558885448032001811143)
      ·
        refine ⟨38430838328172048002716715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25620558885448032001811143 38430838328172048002716715)
        ·
          refine ⟨57646257492258072004075073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38430838328172048002716715 57646257492258072004075073)
          ·
            refine ⟨43234693119193554003056305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57646257492258072004075073 43234693119193554003056305)
            ·
              refine ⟨32426019839395165502292229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43234693119193554003056305 32426019839395165502292229)
              ·
                refine ⟨6079878719886593531679793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32426019839395165502292229 6079878719886593531679793)
                ·
                  refine ⟨4559909039914945148759845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079878719886593531679793 4559909039914945148759845)
                  ·
                    refine ⟨854982944984052215392471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4559909039914945148759845 854982944984052215392471)
                    ·
                      rfl

theorem cell22_2497610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_2497610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497610 prefixEnd_2497610 := by exact prefixLift 2497610
  have htrace : WordTrace (prefixWord ++ tailWord_2497610) baseStart_2497610 baseEnd_2497610 := by
    simpa [prefixWord, tailWord_2497610, baseEnd_2497610] using wordTrace_append hprefix tailTrace_2497610
  have hstable : (prefixWord ++ tailWord_2497610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497610).length < 2 ^ (prefixWord ++ tailWord_2497610).sum := by decide
  have hdescent : baseEnd_2497610 < baseStart_2497610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497642 : List Nat := [3, 1, 3, 2, 2, 1, 4, 6]
def baseStart_2497642 : Nat := 118140960795 + 2497642 * 2 ^ 59
def prefixEnd_2497642 : Nat := 4983230072969 + 3 ^ 40 * 2497642 * 2
def baseEnd_2497642 : Nat := 94999322137557199843597

theorem tailTrace_2497642 : CollatzResearch.WordTrace tailWord_2497642 prefixEnd_2497642 94999322137557199843597 := by
  unfold tailWord_2497642
  simp only [CollatzResearch.WordTrace]
  refine ⟨22774121904369268034567795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60730991744984714758847453 22774121904369268034567795)
  ·
    refine ⟨34161182856553902051851693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22774121904369268034567795 34161182856553902051851693)
    ·
      refine ⟨12810443571207713269444385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34161182856553902051851693 12810443571207713269444385)
      ·
        refine ⟨9607832678405784952083289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12810443571207713269444385 9607832678405784952083289)
        ·
          refine ⟨7205874508804338714062467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9607832678405784952083289 7205874508804338714062467)
          ·
            refine ⟨10808811763206508071093701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7205874508804338714062467 10808811763206508071093701)
            ·
              refine ⟨2026652205601220263330069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10808811763206508071093701 2026652205601220263330069)
              ·
                refine ⟨94999322137557199843597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2026652205601220263330069 94999322137557199843597)
                ·
                  rfl

theorem cell22_2497642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_2497642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497642 prefixEnd_2497642 := by exact prefixLift 2497642
  have htrace : WordTrace (prefixWord ++ tailWord_2497642) baseStart_2497642 baseEnd_2497642 := by
    simpa [prefixWord, tailWord_2497642, baseEnd_2497642] using wordTrace_append hprefix tailTrace_2497642
  have hstable : (prefixWord ++ tailWord_2497642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497642).length < 2 ^ (prefixWord ++ tailWord_2497642).sum := by decide
  have hdescent : baseEnd_2497642 < baseStart_2497642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497687 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 5]
def baseStart_2497687 : Nat := 118140960795 + 2497687 * 2 ^ 59
def prefixEnd_2497687 : Nat := 4983230072969 + 3 ^ 40 * 2497687 * 2
def baseEnd_2497687 : Nat := 285003101219216560405745

theorem tailTrace_2497687 : CollatzResearch.WordTrace tailWord_2497687 prefixEnd_2497687 285003101219216560405745 := by
  unfold tailWord_2497687
  simp only [CollatzResearch.WordTrace]
  refine ⟨91098128902314044823659315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60732085934876029882439543 91098128902314044823659315)
  ·
    refine ⟨136647193353471067235488973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91098128902314044823659315 136647193353471067235488973)
    ·
      refine ⟨51242697507551650213308365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136647193353471067235488973 51242697507551650213308365)
      ·
        refine ⟨19216011565331868829990637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51242697507551650213308365 19216011565331868829990637)
        ·
          refine ⟨7206004336999450811246489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19216011565331868829990637 7206004336999450811246489)
          ·
            refine ⟨5404503252749588108434867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7206004336999450811246489 5404503252749588108434867)
            ·
              refine ⟨8106754879124382162652301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404503252749588108434867 8106754879124382162652301)
              ·
                refine ⟨3040033079671643310994613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8106754879124382162652301 3040033079671643310994613)
                ·
                  refine ⟨285003101219216560405745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3040033079671643310994613 285003101219216560405745)
                  ·
                    rfl

theorem cell22_2497687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 5].length) (baseStart_2497687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497687 prefixEnd_2497687 := by exact prefixLift 2497687
  have htrace : WordTrace (prefixWord ++ tailWord_2497687) baseStart_2497687 baseEnd_2497687 := by
    simpa [prefixWord, tailWord_2497687, baseEnd_2497687] using wordTrace_append hprefix tailTrace_2497687
  have hstable : (prefixWord ++ tailWord_2497687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497687).length < 2 ^ (prefixWord ++ tailWord_2497687).sum := by decide
  have hdescent : baseEnd_2497687 < baseStart_2497687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497745 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_2497745 : Nat := 118140960795 + 2497745 * 2 ^ 59
def prefixEnd_2497745 : Nat := 4983230072969 + 3 ^ 40 * 2497745 * 2
def baseEnd_2497745 : Nat := 855029158242956863267057

theorem tailTrace_2497745 : CollatzResearch.WordTrace tailWord_2497745 prefixEnd_2497745 855029158242956863267057 := by
  unfold tailWord_2497745
  simp only [CollatzResearch.WordTrace]
  refine ⟨91100244336103920729270689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60733496224069280486180459 91100244336103920729270689)
  ·
    refine ⟨68325183252077940546953017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91100244336103920729270689 68325183252077940546953017)
    ·
      refine ⟨51243887439058455410214763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68325183252077940546953017 51243887439058455410214763)
      ·
        refine ⟨76865831158587683115322145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51243887439058455410214763 76865831158587683115322145)
        ·
          refine ⟨57649373368940762336491609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76865831158587683115322145 57649373368940762336491609)
          ·
            refine ⟨43237030026705571752368707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57649373368940762336491609 43237030026705571752368707)
            ·
              refine ⟨64855545040058357628553061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43237030026705571752368707 64855545040058357628553061)
              ·
                refine ⟨12160414695010942055353699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64855545040058357628553061 12160414695010942055353699)
                ·
                  refine ⟨18240622042516413083030549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12160414695010942055353699 18240622042516413083030549)
                  ·
                    refine ⟨855029158242956863267057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18240622042516413083030549 855029158242956863267057)
                    ·
                      rfl

theorem cell22_2497745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_2497745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497745 prefixEnd_2497745 := by exact prefixLift 2497745
  have htrace : WordTrace (prefixWord ++ tailWord_2497745) baseStart_2497745 baseEnd_2497745 := by
    simpa [prefixWord, tailWord_2497745, baseEnd_2497745] using wordTrace_append hprefix tailTrace_2497745
  have hstable : (prefixWord ++ tailWord_2497745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497745).length < 2 ^ (prefixWord ++ tailWord_2497745).sum := by decide
  have hdescent : baseEnd_2497745 < baseStart_2497745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497843 : List Nat := [1, 1, 1, 2, 5, 3, 3, 2, 1, 3]
def baseStart_2497843 : Nat := 118140960795 + 2497843 * 2 ^ 59
def prefixEnd_2497843 : Nat := 4983230072969 + 3 ^ 40 * 2497843 * 2
def baseEnd_2497843 : Nat := 855062705645717274316757

theorem tailTrace_2497843 : CollatzResearch.WordTrace tailWord_2497843 prefixEnd_2497843 855062705645717274316757 := by
  unfold tailWord_2497843
  simp only [CollatzResearch.WordTrace]
  refine ⟨91103818689748883466338183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60735879126499255644225455 91103818689748883466338183)
  ·
    refine ⟨136655728034623325199507275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91103818689748883466338183 136655728034623325199507275)
    ·
      refine ⟨204983592051934987799260913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136655728034623325199507275 204983592051934987799260913)
      ·
        refine ⟨153737694038951240849445685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204983592051934987799260913 153737694038951240849445685)
        ·
          refine ⟨14412908816151678829635533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153737694038951240849445685 14412908816151678829635533)
          ·
            refine ⟨5404840806056879561113325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14412908816151678829635533 5404840806056879561113325)
            ·
              refine ⟨2026815302271329835417497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5404840806056879561113325 2026815302271329835417497)
              ·
                refine ⟨1520111476703497376563123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026815302271329835417497 1520111476703497376563123)
                ·
                  refine ⟨2280167215055246064844685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520111476703497376563123 2280167215055246064844685)
                  ·
                    refine ⟨855062705645717274316757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280167215055246064844685 855062705645717274316757)
                    ·
                      rfl

theorem cell22_2497843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 1, 3].length) (baseStart_2497843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497843 prefixEnd_2497843 := by exact prefixLift 2497843
  have htrace : WordTrace (prefixWord ++ tailWord_2497843) baseStart_2497843 baseEnd_2497843 := by
    simpa [prefixWord, tailWord_2497843, baseEnd_2497843] using wordTrace_append hprefix tailTrace_2497843
  have hstable : (prefixWord ++ tailWord_2497843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497843).length < 2 ^ (prefixWord ++ tailWord_2497843).sum := by decide
  have hdescent : baseEnd_2497843 < baseStart_2497843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497882 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_2497882 : Nat := 118140960795 + 2497882 * 2 ^ 59
def prefixEnd_2497882 : Nat := 4983230072969 + 3 ^ 40 * 2497882 * 2
def baseEnd_2497882 : Nat := 855076056142734172591637

theorem tailTrace_2497882 : CollatzResearch.WordTrace tailWord_2497882 prefixEnd_2497882 855076056142734172591637 := by
  unfold tailWord_2497882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22776310284151898281751975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60736827424405062084671933 22776310284151898281751975)
  ·
    refine ⟨34164465426227847422627963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22776310284151898281751975 34164465426227847422627963)
    ·
      refine ⟨51246698139341771133941945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34164465426227847422627963 51246698139341771133941945)
      ·
        refine ⟨38435023604506328350456459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51246698139341771133941945 38435023604506328350456459)
        ·
          refine ⟨57652535406759492525684689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38435023604506328350456459 57652535406759492525684689)
          ·
            refine ⟨43239401555069619394263517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57652535406759492525684689 43239401555069619394263517)
            ·
              refine ⟨16214775583151107272848819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43239401555069619394263517 16214775583151107272848819)
              ·
                refine ⟨24322163374726660909273229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16214775583151107272848819 24322163374726660909273229)
                ·
                  refine ⟨9120811265522497840977461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24322163374726660909273229 9120811265522497840977461)
                  ·
                    refine ⟨855076056142734172591637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9120811265522497840977461 855076056142734172591637)
                    ·
                      rfl

theorem cell22_2497882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_2497882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497882 prefixEnd_2497882 := by exact prefixLift 2497882
  have htrace : WordTrace (prefixWord ++ tailWord_2497882) baseStart_2497882 baseEnd_2497882 := by
    simpa [prefixWord, tailWord_2497882, baseEnd_2497882] using wordTrace_append hprefix tailTrace_2497882
  have hstable : (prefixWord ++ tailWord_2497882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497882).length < 2 ^ (prefixWord ++ tailWord_2497882).sum := by decide
  have hdescent : baseEnd_2497882 < baseStart_2497882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497897 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_2497897 : Nat := 118140960795 + 2497897 * 2 ^ 59
def prefixEnd_2497897 : Nat := 4983230072969 + 3 ^ 40 * 2497897 * 2
def baseEnd_2497897 : Nat := 855081190949279133466591

theorem tailTrace_2497897 : CollatzResearch.WordTrace tailWord_2497897 prefixEnd_2497897 855081190949279133466591 := by
  unfold tailWord_2497897
  simp only [CollatzResearch.WordTrace]
  refine ⟨91105788231553250688803945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60737192154368833792535963 91105788231553250688803945)
  ·
    refine ⟨68329341173664938016602959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91105788231553250688803945 68329341173664938016602959)
    ·
      refine ⟨102494011760497407024904439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68329341173664938016602959 102494011760497407024904439)
      ·
        refine ⟨153741017640746110537356659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102494011760497407024904439 153741017640746110537356659)
        ·
          refine ⟨230611526461119165806034989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153741017640746110537356659 230611526461119165806034989)
          ·
            refine ⟨86479322422919687177263121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230611526461119165806034989 86479322422919687177263121)
            ·
              refine ⟨64859491817189765382947341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86479322422919687177263121 64859491817189765382947341)
              ·
                refine ⟨24322309431446162018605253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64859491817189765382947341 24322309431446162018605253)
                ·
                  refine ⟨4560433018396155378488485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24322309431446162018605253 4560433018396155378488485)
                  ·
                    refine ⟨855081190949279133466591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4560433018396155378488485 855081190949279133466591)
                    ·
                      rfl

theorem cell22_2497897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_2497897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497897 prefixEnd_2497897 := by exact prefixLift 2497897
  have htrace : WordTrace (prefixWord ++ tailWord_2497897) baseStart_2497897 baseEnd_2497897 := by
    simpa [prefixWord, tailWord_2497897, baseEnd_2497897] using wordTrace_append hprefix tailTrace_2497897
  have hstable : (prefixWord ++ tailWord_2497897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497897).length < 2 ^ (prefixWord ++ tailWord_2497897).sum := by decide
  have hdescent : baseEnd_2497897 < baseStart_2497897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497901 : List Nat := [1, 5, 1, 1, 1, 4, 1, 4, 4]
def baseStart_2497901 : Nat := 118140960795 + 2497901 * 2 ^ 59
def prefixEnd_2497901 : Nat := 4983230072969 + 3 ^ 40 * 2497901 * 2
def baseEnd_2497901 : Nat := 285027520077008152122193

theorem tailTrace_2497901 : CollatzResearch.WordTrace tailWord_2497901 prefixEnd_2497901 285027520077008152122193 := by
  unfold tailWord_2497901
  simp only [CollatzResearch.WordTrace]
  refine ⟨91105934123538759371949557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60737289415692506247966371 91105934123538759371949557)
  ·
    refine ⟨8541181324081758691120271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91105934123538759371949557 8541181324081758691120271)
    ·
      refine ⟨12811771986122638036680407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8541181324081758691120271 12811771986122638036680407)
      ·
        refine ⟨19217657979183957055020611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12811771986122638036680407 19217657979183957055020611)
        ·
          refine ⟨28826486968775935582530917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19217657979183957055020611 28826486968775935582530917)
          ·
            refine ⟨5404966306645487921724547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28826486968775935582530917 5404966306645487921724547)
            ·
              refine ⟨8107449459968231882586821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404966306645487921724547 8107449459968231882586821)
              ·
                refine ⟨1520146773744043477985029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8107449459968231882586821 1520146773744043477985029)
                ·
                  refine ⟨285027520077008152122193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520146773744043477985029 285027520077008152122193)
                  ·
                    rfl

theorem cell22_2497901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_2497901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497901 prefixEnd_2497901 := by exact prefixLift 2497901
  have htrace : WordTrace (prefixWord ++ tailWord_2497901) baseStart_2497901 baseEnd_2497901 := by
    simpa [prefixWord, tailWord_2497901, baseEnd_2497901] using wordTrace_append hprefix tailTrace_2497901
  have hstable : (prefixWord ++ tailWord_2497901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497901).length < 2 ^ (prefixWord ++ tailWord_2497901).sum := by decide
  have hdescent : baseEnd_2497901 < baseStart_2497901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497918 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_2497918 : Nat := 118140960795 + 2497918 * 2 ^ 59
def prefixEnd_2497918 : Nat := 4983230072969 + 3 ^ 40 * 2497918 * 2
def baseEnd_2497918 : Nat := 285029459892814026230509

theorem tailTrace_2497918 : CollatzResearch.WordTrace tailWord_2497918 prefixEnd_2497918 285029459892814026230509 := by
  unfold tailWord_2497918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11388319270559646409414801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60737702776318114183545605 11388319270559646409414801)
  ·
    refine ⟨8541239452919734807061101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11388319270559646409414801 8541239452919734807061101)
    ·
      refine ⟨3202964794844900552647913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8541239452919734807061101 3202964794844900552647913)
      ·
        refine ⟨2402223596133675414485935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3202964794844900552647913 2402223596133675414485935)
        ·
          refine ⟨3603335394200513121728903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402223596133675414485935 3603335394200513121728903)
          ·
            refine ⟨5405003091300769682593355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603335394200513121728903 5405003091300769682593355)
            ·
              refine ⟨8107504636951154523890033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5405003091300769682593355 8107504636951154523890033)
              ·
                refine ⟨6080628477713365892917525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8107504636951154523890033 6080628477713365892917525)
                ·
                  refine ⟨285029459892814026230509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6080628477713365892917525 285029459892814026230509)
                  ·
                    rfl

theorem cell22_2497918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_2497918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497918 prefixEnd_2497918 := by exact prefixLift 2497918
  have htrace : WordTrace (prefixWord ++ tailWord_2497918) baseStart_2497918 baseEnd_2497918 := by
    simpa [prefixWord, tailWord_2497918, baseEnd_2497918] using wordTrace_append hprefix tailTrace_2497918
  have hstable : (prefixWord ++ tailWord_2497918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497918).length < 2 ^ (prefixWord ++ tailWord_2497918).sum := by decide
  have hdescent : baseEnd_2497918 < baseStart_2497918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2497986 : List Nat := [3, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2497986 : Nat := 118140960795 + 2497986 * 2 ^ 59
def prefixEnd_2497986 : Nat := 4983230072969 + 3 ^ 40 * 2497986 * 2
def baseEnd_2497986 : Nat := 285037219156037522663773

theorem tailTrace_2497986 : CollatzResearch.WordTrace tailWord_2497986 prefixEnd_2497986 285037219156037522663773 := by
  unfold tailWord_2497986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22777258582057704722198453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60739356218820545925862541 22777258582057704722198453)
  ·
    refine ⟨2135367992067909817706105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22777258582057704722198453 2135367992067909817706105)
    ·
      refine ⟨1601525994050932363279579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2135367992067909817706105 1601525994050932363279579)
      ·
        refine ⟨2402288991076398544919369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601525994050932363279579 2402288991076398544919369)
        ·
          refine ⟨1801716743307298908689527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2402288991076398544919369 1801716743307298908689527)
          ·
            refine ⟨2702575114960948363034291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801716743307298908689527 2702575114960948363034291)
            ·
              refine ⟨4053862672441422544551437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702575114960948363034291 4053862672441422544551437)
              ·
                refine ⟨1520198502165533454206789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4053862672441422544551437 1520198502165533454206789)
                ·
                  refine ⟨285037219156037522663773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520198502165533454206789 285037219156037522663773)
                  ·
                    rfl

theorem cell22_2497986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2497986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2497986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2497986 prefixEnd_2497986 := by exact prefixLift 2497986
  have htrace : WordTrace (prefixWord ++ tailWord_2497986) baseStart_2497986 baseEnd_2497986 := by
    simpa [prefixWord, tailWord_2497986, baseEnd_2497986] using wordTrace_append hprefix tailTrace_2497986
  have hstable : (prefixWord ++ tailWord_2497986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2497986).length < 2 ^ (prefixWord ++ tailWord_2497986).sum := by decide
  have hdescent : baseEnd_2497986 < baseStart_2497986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2497986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498038 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2498038 : Nat := 118140960795 + 2498038 * 2 ^ 59
def prefixEnd_2498038 : Nat := 4983230072969 + 3 ^ 40 * 2498038 * 2
def baseEnd_2498038 : Nat := 855129458130801765691159

theorem tailTrace_2498038 : CollatzResearch.WordTrace tailWord_2498038 prefixEnd_2498038 855129458130801765691159 := by
  unfold tailWord_2498038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694433182752651985605423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60740620616028287846457845 5694433182752651985605423)
  ·
    refine ⟨8541649774128977978408135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5694433182752651985605423 8541649774128977978408135)
    ·
      refine ⟨12812474661193466967612203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8541649774128977978408135 12812474661193466967612203)
      ·
        refine ⟨19218711991790200451418305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12812474661193466967612203 19218711991790200451418305)
        ·
          refine ⟨14414033993842650338563729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19218711991790200451418305 14414033993842650338563729)
          ·
            refine ⟨10810525495381987753922797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14414033993842650338563729 10810525495381987753922797)
            ·
              refine ⟨4053947060768245407721049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10810525495381987753922797 4053947060768245407721049)
              ·
                refine ⟨3040460295576184055790787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4053947060768245407721049 3040460295576184055790787)
                ·
                  refine ⟨4560690443364276083686181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040460295576184055790787 4560690443364276083686181)
                  ·
                    refine ⟨855129458130801765691159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4560690443364276083686181 855129458130801765691159)
                    ·
                      rfl

theorem cell22_2498038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2498038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498038 prefixEnd_2498038 := by exact prefixLift 2498038
  have htrace : WordTrace (prefixWord ++ tailWord_2498038) baseStart_2498038 baseEnd_2498038 := by
    simpa [prefixWord, tailWord_2498038, baseEnd_2498038] using wordTrace_append hprefix tailTrace_2498038
  have hstable : (prefixWord ++ tailWord_2498038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498038).length < 2 ^ (prefixWord ++ tailWord_2498038).sum := by decide
  have hdescent : baseEnd_2498038 < baseStart_2498038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498081 : List Nat := [1, 2, 3, 2, 2, 4, 1, 7]
def baseStart_2498081 : Nat := 118140960795 + 2498081 * 2 ^ 59
def prefixEnd_2498081 : Nat := 4983230072969 + 3 ^ 40 * 2498081 * 2
def baseEnd_2498081 : Nat := 95016019767729331874003

theorem tailTrace_2498081 : CollatzResearch.WordTrace tailWord_2498081 prefixEnd_2498081 95016019767729331874003 := by
  unfold tailWord_2498081
  simp only [CollatzResearch.WordTrace]
  refine ⟨91112499262886650113502097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60741666175257766742334731 91112499262886650113502097)
  ·
    refine ⟨68334374447164987585126573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91112499262886650113502097 68334374447164987585126573)
    ·
      refine ⟨25625390417686870344422465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68334374447164987585126573 25625390417686870344422465)
      ·
        refine ⟨19219042813265152758316849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25625390417686870344422465 19219042813265152758316849)
        ·
          refine ⟨14414282109948864568737637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19219042813265152758316849 14414282109948864568737637)
          ·
            refine ⟨2702677895615412106638307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14414282109948864568737637 2702677895615412106638307)
            ·
              refine ⟨4054016843423118159957461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702677895615412106638307 4054016843423118159957461)
              ·
                refine ⟨95016019767729331874003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4054016843423118159957461 95016019767729331874003)
                ·
                  rfl

theorem cell22_2498081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 7].length) (baseStart_2498081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498081 prefixEnd_2498081 := by exact prefixLift 2498081
  have htrace : WordTrace (prefixWord ++ tailWord_2498081) baseStart_2498081 baseEnd_2498081 := by
    simpa [prefixWord, tailWord_2498081, baseEnd_2498081] using wordTrace_append hprefix tailTrace_2498081
  have hstable : (prefixWord ++ tailWord_2498081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498081).length < 2 ^ (prefixWord ++ tailWord_2498081).sum := by decide
  have hdescent : baseEnd_2498081 < baseStart_2498081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498130 : List Nat := [3, 2, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_2498130 : Nat := 118140960795 + 2498130 * 2 ^ 59
def prefixEnd_2498130 : Nat := 4983230072969 + 3 ^ 40 * 2498130 * 2
def baseEnd_2498130 : Nat := 855160951610944192390877

theorem tailTrace_2498130 : CollatzResearch.WordTrace tailWord_2498130 prefixEnd_2498130 855160951610944192390877 := by
  unfold tailWord_2498130
  simp only [CollatzResearch.WordTrace]
  refine ⟨22778571609927282870508961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60742857626472754321357229 22778571609927282870508961)
  ·
    refine ⟨17083928707445462152881721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22778571609927282870508961 17083928707445462152881721)
    ·
      refine ⟨12812946530584096614661291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17083928707445462152881721 12812946530584096614661291)
      ·
        refine ⟨19219419795876144921991937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12812946530584096614661291 19219419795876144921991937)
        ·
          refine ⟨14414564846907108691493953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19219419795876144921991937 14414564846907108691493953)
          ·
            refine ⟨10810923635180331518620465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14414564846907108691493953 10810923635180331518620465)
            ·
              refine ⟨8108192726385248638965349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10810923635180331518620465 8108192726385248638965349)
              ·
                refine ⟨1520286136197234119806003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8108192726385248638965349 1520286136197234119806003)
                ·
                  refine ⟨2280429204295851179709005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520286136197234119806003 2280429204295851179709005)
                  ·
                    refine ⟨855160951610944192390877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280429204295851179709005 855160951610944192390877)
                    ·
                      rfl

theorem cell22_2498130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_2498130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498130 prefixEnd_2498130 := by exact prefixLift 2498130
  have htrace : WordTrace (prefixWord ++ tailWord_2498130) baseStart_2498130 baseEnd_2498130 := by
    simpa [prefixWord, tailWord_2498130, baseEnd_2498130] using wordTrace_append hprefix tailTrace_2498130
  have hstable : (prefixWord ++ tailWord_2498130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498130).length < 2 ^ (prefixWord ++ tailWord_2498130).sum := by decide
  have hdescent : baseEnd_2498130 < baseStart_2498130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498173 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_2498173 : Nat := 118140960795 + 2498173 * 2 ^ 59
def prefixEnd_2498173 : Nat := 4983230072969 + 3 ^ 40 * 2498173 * 2
def baseEnd_2498173 : Nat := 855175671389706413565745

theorem tailTrace_2498173 : CollatzResearch.WordTrace tailWord_2498173 prefixEnd_2498173 855175671389706413565745 := by
  unfold tailWord_2498173
  simp only [CollatzResearch.WordTrace]
  refine ⟨91115854778553349825851173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60743903185702233217234115 91115854778553349825851173)
  ·
    refine ⟨17084222770978753092347095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91115854778553349825851173 17084222770978753092347095)
    ·
      refine ⟨25626334156468129638520643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17084222770978753092347095 25626334156468129638520643)
      ·
        refine ⟨38439501234702194457780965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25626334156468129638520643 38439501234702194457780965)
        ·
          refine ⟨7207406481506661460833931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38439501234702194457780965 7207406481506661460833931)
          ·
            refine ⟨10811109722259992191250897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7207406481506661460833931 10811109722259992191250897)
            ·
              refine ⟨8108332291694994143438173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10811109722259992191250897 8108332291694994143438173)
              ·
                refine ⟨3040624609385622803789315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8108332291694994143438173 3040624609385622803789315)
                ·
                  refine ⟨4560936914078434205683973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040624609385622803789315 4560936914078434205683973)
                  ·
                    refine ⟨855175671389706413565745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4560936914078434205683973 855175671389706413565745)
                    ·
                      rfl

theorem cell22_2498173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_2498173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498173 prefixEnd_2498173 := by exact prefixLift 2498173
  have htrace : WordTrace (prefixWord ++ tailWord_2498173) baseStart_2498173 baseEnd_2498173 := by
    simpa [prefixWord, tailWord_2498173, baseEnd_2498173] using wordTrace_append hprefix tailTrace_2498173
  have hstable : (prefixWord ++ tailWord_2498173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498173).length < 2 ^ (prefixWord ++ tailWord_2498173).sum := by decide
  have hdescent : baseEnd_2498173 < baseStart_2498173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498207 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 1, 4]
def baseStart_2498207 : Nat := 118140960795 + 2498207 * 2 ^ 59
def prefixEnd_2498207 : Nat := 4983230072969 + 3 ^ 40 * 2498207 * 2
def baseEnd_2498207 : Nat := 855187310284541658215641

theorem tailTrace_2498207 : CollatzResearch.WordTrace tailWord_2498207 prefixEnd_2498207 855187310284541658215641 := by
  unfold tailWord_2498207
  simp only [CollatzResearch.WordTrace]
  refine ⟨91117094860430173632588875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60744729906953449088392583 91117094860430173632588875)
  ·
    refine ⟨136675642290645260448883313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91117094860430173632588875 136675642290645260448883313)
    ·
      refine ⟨102506731717983945336662485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136675642290645260448883313 102506731717983945336662485)
      ·
        refine ⟨2402501524640248718828027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 102506731717983945336662485 2402501524640248718828027)
        ·
          refine ⟨3603752286960373078242041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402501524640248718828027 3603752286960373078242041)
          ·
            refine ⟨2702814215220279808681531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3603752286960373078242041 2702814215220279808681531)
            ·
              refine ⟨4054221322830419713022297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702814215220279808681531 4054221322830419713022297)
              ·
                refine ⟨3040665992122814784766723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4054221322830419713022297 3040665992122814784766723)
                ·
                  refine ⟨4560998988184222177150085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040665992122814784766723 4560998988184222177150085)
                  ·
                    refine ⟨855187310284541658215641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4560998988184222177150085 855187310284541658215641)
                    ·
                      rfl

theorem cell22_2498207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_2498207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498207 prefixEnd_2498207 := by exact prefixLift 2498207
  have htrace : WordTrace (prefixWord ++ tailWord_2498207) baseStart_2498207 baseEnd_2498207 := by
    simpa [prefixWord, tailWord_2498207, baseEnd_2498207] using wordTrace_append hprefix tailTrace_2498207
  have hstable : (prefixWord ++ tailWord_2498207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498207).length < 2 ^ (prefixWord ++ tailWord_2498207).sum := by decide
  have hdescent : baseEnd_2498207 < baseStart_2498207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498248 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 3, 3]
def baseStart_2498248 : Nat := 118140960795 + 2498248 * 2 ^ 59
def prefixEnd_2498248 : Nat := 4983230072969 + 3 ^ 40 * 2498248 * 2
def baseEnd_2498248 : Nat := 855201345422431217940515

theorem tailTrace_2498248 : CollatzResearch.WordTrace tailWord_2498248 prefixEnd_2498248 855201345422431217940515 := by
  unfold tailWord_2498248
  simp only [CollatzResearch.WordTrace]
  refine ⟨45559295126640818817415699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60745726835521091756554265 45559295126640818817415699)
  ·
    refine ⟨68338942689961228226123549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45559295126640818817415699 68338942689961228226123549)
    ·
      refine ⟨25627103508735460584796331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68338942689961228226123549 25627103508735460584796331)
      ·
        refine ⟨38440655263103190877194497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25627103508735460584796331 38440655263103190877194497)
        ·
          refine ⟨28830491447327393157895873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38440655263103190877194497 28830491447327393157895873)
          ·
            refine ⟨21622868585495544868421905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28830491447327393157895873 21622868585495544868421905)
            ·
              refine ⟨16217151439121658651316429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21622868585495544868421905 16217151439121658651316429)
              ·
                refine ⟨6081431789670621994243661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16217151439121658651316429 6081431789670621994243661)
                ·
                  refine ⟨2280536921126483247841373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6081431789670621994243661 2280536921126483247841373)
                  ·
                    refine ⟨855201345422431217940515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280536921126483247841373 855201345422431217940515)
                    ·
                      rfl

theorem cell22_2498248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_2498248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498248 prefixEnd_2498248 := by exact prefixLift 2498248
  have htrace : WordTrace (prefixWord ++ tailWord_2498248) baseStart_2498248 baseEnd_2498248 := by
    simpa [prefixWord, tailWord_2498248, baseEnd_2498248] using wordTrace_append hprefix tailTrace_2498248
  have hstable : (prefixWord ++ tailWord_2498248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498248).length < 2 ^ (prefixWord ++ tailWord_2498248).sum := by decide
  have hdescent : baseEnd_2498248 < baseStart_2498248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498250 : List Nat := [3, 1, 2, 1, 6, 1, 1, 7]
def baseStart_2498250 : Nat := 118140960795 + 2498250 * 2 ^ 59
def prefixEnd_2498250 : Nat := 4983230072969 + 3 ^ 40 * 2498250 * 2
def baseEnd_2498250 : Nat := 95022447784811542154501

theorem tailTrace_2498250 : CollatzResearch.WordTrace tailWord_2498250 prefixEnd_2498250 95022447784811542154501 := by
  unfold tailWord_2498250
  simp only [CollatzResearch.WordTrace]
  refine ⟨22779665799818597994101051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60745775466182927984269469 22779665799818597994101051)
  ·
    refine ⟨34169498699727896991151577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22779665799818597994101051 34169498699727896991151577)
    ·
      refine ⟨25627124024795922743363683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34169498699727896991151577 25627124024795922743363683)
      ·
        refine ⟨38440686037193884115045525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25627124024795922743363683 38440686037193884115045525)
        ·
          refine ⟨1801907157993463317892759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38440686037193884115045525 1801907157993463317892759)
          ·
            refine ⟨2702860736990194976839139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801907157993463317892759 2702860736990194976839139)
            ·
              refine ⟨4054291105485292465258709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702860736990194976839139 4054291105485292465258709)
              ·
                refine ⟨95022447784811542154501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4054291105485292465258709 95022447784811542154501)
                ·
                  rfl

theorem cell22_2498250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_2498250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498250 prefixEnd_2498250 := by exact prefixLift 2498250
  have htrace : WordTrace (prefixWord ++ tailWord_2498250) baseStart_2498250 baseEnd_2498250 := by
    simpa [prefixWord, tailWord_2498250, baseEnd_2498250] using wordTrace_append hprefix tailTrace_2498250
  have hstable : (prefixWord ++ tailWord_2498250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498250).length < 2 ^ (prefixWord ++ tailWord_2498250).sum := by decide
  have hdescent : baseEnd_2498250 < baseStart_2498250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498269 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_2498269 : Nat := 118140960795 + 2498269 * 2 ^ 59
def prefixEnd_2498269 : Nat := 4983230072969 + 3 ^ 40 * 2498269 * 2
def baseEnd_2498269 : Nat := 855208534151594163165451

theorem tailTrace_2498269 : CollatzResearch.WordTrace tailWord_2498269 prefixEnd_2498269 855208534151594163165451 := by
  unfold tailWord_2498269
  simp only [CollatzResearch.WordTrace]
  refine ⟨91119356186205558221345861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60746237457470372147563907 91119356186205558221345861)
  ·
    refine ⟨17084879284913542166502349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91119356186205558221345861 17084879284913542166502349)
    ·
      refine ⟨6406829731842578312438381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17084879284913542166502349 6406829731842578312438381)
      ·
        refine ⟨2402561149440966867164393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6406829731842578312438381 2402561149440966867164393)
        ·
          refine ⟨1801920862080725150373295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2402561149440966867164393 1801920862080725150373295)
          ·
            refine ⟨2702881293121087725559943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801920862080725150373295 2702881293121087725559943)
            ·
              refine ⟨4054321939681631588339915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702881293121087725559943 4054321939681631588339915)
              ·
                refine ⟨6081482909522447382509873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4054321939681631588339915 6081482909522447382509873)
                ·
                  refine ⟨4561112182141835536882405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6081482909522447382509873 4561112182141835536882405)
                  ·
                    refine ⟨855208534151594163165451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4561112182141835536882405 855208534151594163165451)
                    ·
                      rfl

theorem cell22_2498269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_2498269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498269 prefixEnd_2498269 := by exact prefixLift 2498269
  have htrace : WordTrace (prefixWord ++ tailWord_2498269) baseStart_2498269 baseEnd_2498269 := by
    simpa [prefixWord, tailWord_2498269, baseEnd_2498269] using wordTrace_append hprefix tailTrace_2498269
  have hstable : (prefixWord ++ tailWord_2498269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498269).length < 2 ^ (prefixWord ++ tailWord_2498269).sum := by decide
  have hdescent : baseEnd_2498269 < baseStart_2498269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498276 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_2498276 : Nat := 118140960795 + 2498276 * 2 ^ 59
def prefixEnd_2498276 : Nat := 4983230072969 + 3 ^ 40 * 2498276 * 2
def baseEnd_2498276 : Nat := 855210930394648478240429

theorem tailTrace_2498276 : CollatzResearch.WordTrace tailWord_2498276 prefixEnd_2498276 855210930394648478240429 := by
  unfold tailWord_2498276
  simp only [CollatzResearch.WordTrace]
  refine ⟨45559805748590099208425341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60746407664786798944567121 45559805748590099208425341)
  ·
    refine ⟨17084927155721287203159503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45559805748590099208425341 17084927155721287203159503)
    ·
      refine ⟨25627390733581930804739255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17084927155721287203159503 25627390733581930804739255)
      ·
        refine ⟨38441086100372896207108883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25627390733581930804739255 38441086100372896207108883)
        ·
          refine ⟨57661629150559344310663325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38441086100372896207108883 57661629150559344310663325)
          ·
            refine ⟨21623110931459754116498747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57661629150559344310663325 21623110931459754116498747)
            ·
              refine ⟨32434666397189631174748121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21623110931459754116498747 32434666397189631174748121)
              ·
                refine ⟨24325999797892223381061091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32434666397189631174748121 24325999797892223381061091)
                ·
                  refine ⟨36488999696838335071591637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24325999797892223381061091 36488999696838335071591637)
                  ·
                    refine ⟨855210930394648478240429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36488999696838335071591637 855210930394648478240429)
                    ·
                      rfl

theorem cell22_2498276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_2498276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498276 prefixEnd_2498276 := by exact prefixLift 2498276
  have htrace : WordTrace (prefixWord ++ tailWord_2498276) baseStart_2498276 baseEnd_2498276 := by
    simpa [prefixWord, tailWord_2498276, baseEnd_2498276] using wordTrace_append hprefix tailTrace_2498276
  have hstable : (prefixWord ++ tailWord_2498276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498276).length < 2 ^ (prefixWord ++ tailWord_2498276).sum := by decide
  have hdescent : baseEnd_2498276 < baseStart_2498276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498325 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_2498325 : Nat := 118140960795 + 2498325 * 2 ^ 59
def prefixEnd_2498325 : Nat := 4983230072969 + 3 ^ 40 * 2498325 * 2
def baseEnd_2498325 : Nat := 855227704096028683765279

theorem tailTrace_2498325 : CollatzResearch.WordTrace tailWord_2498325 prefixEnd_2498325 855227704096028683765279 := by
  unfold tailWord_2498325
  simp only [CollatzResearch.WordTrace]
  refine ⟨91121398674002679785384429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60747599116001786523589619 91121398674002679785384429)
  ·
    refine ⟨34170524502751004919519161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91121398674002679785384429 34170524502751004919519161)
    ·
      refine ⟨25627893377063253689639371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34170524502751004919519161 25627893377063253689639371)
      ·
        refine ⟨38441840065594880534459057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25627893377063253689639371 38441840065594880534459057)
        ·
          refine ⟨28831380049196160400844293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38441840065594880534459057 28831380049196160400844293)
          ·
            refine ⟨5405883759224280075158305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28831380049196160400844293 5405883759224280075158305)
            ·
              refine ⟨4054412819418210056368729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5405883759224280075158305 4054412819418210056368729)
              ·
                refine ⟨3040809614563657542276547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4054412819418210056368729 3040809614563657542276547)
                ·
                  refine ⟨4561214421845486313414821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040809614563657542276547 4561214421845486313414821)
                  ·
                    refine ⟨855227704096028683765279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4561214421845486313414821 855227704096028683765279)
                    ·
                      rfl

theorem cell22_2498325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_2498325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498325 prefixEnd_2498325 := by exact prefixLift 2498325
  have htrace : WordTrace (prefixWord ++ tailWord_2498325) baseStart_2498325 baseEnd_2498325 := by
    simpa [prefixWord, tailWord_2498325, baseEnd_2498325] using wordTrace_append hprefix tailTrace_2498325
  have hstable : (prefixWord ++ tailWord_2498325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498325).length < 2 ^ (prefixWord ++ tailWord_2498325).sum := by decide
  have hdescent : baseEnd_2498325 < baseStart_2498325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498338 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2498338 : Nat := 118140960795 + 2498338 * 2 ^ 59
def prefixEnd_2498338 : Nat := 4983230072969 + 3 ^ 40 * 2498338 * 2
def baseEnd_2498338 : Nat := 855232154261700983190239

theorem tailTrace_2498338 : CollatzResearch.WordTrace tailWord_2498338 prefixEnd_2498338 855232154261700983190239 := by
  unfold tailWord_2498338
  simp only [CollatzResearch.WordTrace]
  refine ⟨22780468205738895751401917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60747915215303722003738445 22780468205738895751401917)
  ·
    refine ⟨8542675577152085906775719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22780468205738895751401917 8542675577152085906775719)
    ·
      refine ⟨12814013365728128860163579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8542675577152085906775719 12814013365728128860163579)
      ·
        refine ⟨19221020048592193290245369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12814013365728128860163579 19221020048592193290245369)
        ·
          refine ⟨14415765036444144967684027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19221020048592193290245369 14415765036444144967684027)
          ·
            refine ⟨21623647554666217451526041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14415765036444144967684027 21623647554666217451526041)
            ·
              refine ⟨16217735665999663088644531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21623647554666217451526041 16217735665999663088644531)
              ·
                refine ⟨24326603498999494632966797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16217735665999663088644531 24326603498999494632966797)
                ·
                  refine ⟨9122476312124810487362549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24326603498999494632966797 9122476312124810487362549)
                  ·
                    refine ⟨855232154261700983190239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9122476312124810487362549 855232154261700983190239)
                    ·
                      rfl

theorem cell22_2498338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2498338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498338 prefixEnd_2498338 := by exact prefixLift 2498338
  have htrace : WordTrace (prefixWord ++ tailWord_2498338) baseStart_2498338 baseEnd_2498338 := by
    simpa [prefixWord, tailWord_2498338, baseEnd_2498338] using wordTrace_append hprefix tailTrace_2498338
  have hstable : (prefixWord ++ tailWord_2498338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498338).length < 2 ^ (prefixWord ++ tailWord_2498338).sum := by decide
  have hdescent : baseEnd_2498338 < baseStart_2498338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498353 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_2498353 : Nat := 118140960795 + 2498353 * 2 ^ 59
def prefixEnd_2498353 : Nat := 4983230072969 + 3 ^ 40 * 2498353 * 2
def baseEnd_2498353 : Nat := 855237289068245944065193

theorem tailTrace_2498353 : CollatzResearch.WordTrace tailWord_2498353 prefixEnd_2498353 855237289068245944065193 := by
  unfold tailWord_2498353
  simp only [CollatzResearch.WordTrace]
  refine ⟨91122419917901240567403713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60748279945267493711602475 91122419917901240567403713)
  ·
    refine ⟨68341814938425930425552785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91122419917901240567403713 68341814938425930425552785)
    ·
      refine ⟨51256361203819447819164589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68341814938425930425552785 51256361203819447819164589)
      ·
        refine ⟨19221135451432292932186721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51256361203819447819164589 19221135451432292932186721)
        ·
          refine ⟨14415851588574219699140041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19221135451432292932186721 14415851588574219699140041)
          ·
            refine ⟨10811888691430664774355031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14415851588574219699140041 10811888691430664774355031)
            ·
              refine ⟨16217833037145997161532547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10811888691430664774355031 16217833037145997161532547)
              ·
                refine ⟨24326749555718995742298821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16217833037145997161532547 24326749555718995742298821)
                ·
                  refine ⟨4561265541697311701681029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24326749555718995742298821 4561265541697311701681029)
                  ·
                    refine ⟨855237289068245944065193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4561265541697311701681029 855237289068245944065193)
                    ·
                      rfl

theorem cell22_2498353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_2498353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498353 prefixEnd_2498353 := by exact prefixLift 2498353
  have htrace : WordTrace (prefixWord ++ tailWord_2498353) baseStart_2498353 baseEnd_2498353 := by
    simpa [prefixWord, tailWord_2498353, baseEnd_2498353] using wordTrace_append hprefix tailTrace_2498353
  have hstable : (prefixWord ++ tailWord_2498353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498353).length < 2 ^ (prefixWord ++ tailWord_2498353).sum := by decide
  have hdescent : baseEnd_2498353 < baseStart_2498353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498357 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 6]
def baseStart_2498357 : Nat := 118140960795 + 2498357 * 2 ^ 59
def prefixEnd_2498357 : Nat := 4983230072969 + 3 ^ 40 * 2498357 * 2
def baseEnd_2498357 : Nat := 285079552783330422321727

theorem tailTrace_2498357 : CollatzResearch.WordTrace tailWord_2498357 prefixEnd_2498357 285079552783330422321727 := by
  unfold tailWord_2498357
  simp only [CollatzResearch.WordTrace]
  refine ⟨91122565809886749250549325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60748377206591166167032883 91122565809886749250549325)
  ·
    refine ⟨34170962178707530968955997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91122565809886749250549325 34170962178707530968955997)
    ·
      refine ⟨12814110817015324113358499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34170962178707530968955997 12814110817015324113358499)
      ·
        refine ⟨19221166225522986170037749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12814110817015324113358499 19221166225522986170037749)
        ·
          refine ⟨1801984333642779953441039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19221166225522986170037749 1801984333642779953441039)
          ·
            refine ⟨2702976500464169930161559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801984333642779953441039 2702976500464169930161559)
            ·
              refine ⟨4054464750696254895242339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702976500464169930161559 4054464750696254895242339)
              ·
                refine ⟨6081697126044382342863509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4054464750696254895242339 6081697126044382342863509)
                ·
                  refine ⟨285079552783330422321727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6081697126044382342863509 285079552783330422321727)
                  ·
                    rfl

theorem cell22_2498357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_2498357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498357 prefixEnd_2498357 := by exact prefixLift 2498357
  have htrace : WordTrace (prefixWord ++ tailWord_2498357) baseStart_2498357 baseEnd_2498357 := by
    simpa [prefixWord, tailWord_2498357, baseEnd_2498357] using wordTrace_append hprefix tailTrace_2498357
  have hstable : (prefixWord ++ tailWord_2498357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498357).length < 2 ^ (prefixWord ++ tailWord_2498357).sum := by decide
  have hdescent : baseEnd_2498357 < baseStart_2498357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498413 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2498413 : Nat := 118140960795 + 2498413 * 2 ^ 59
def prefixEnd_2498413 : Nat := 4983230072969 + 3 ^ 40 * 2498413 * 2
def baseEnd_2498413 : Nat := 285085942764808595855003

theorem tailTrace_2498413 : CollatzResearch.WordTrace tailWord_2498413 prefixEnd_2498413 285085942764808595855003 := by
  unfold tailWord_2498413
  simp only [CollatzResearch.WordTrace]
  refine ⟨91124608297683870814587893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60749738865122580543058595 91124608297683870814587893)
  ·
    refine ⟨8542932027907862888867615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91124608297683870814587893 8542932027907862888867615)
    ·
      refine ⟨12814398041861794333301423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8542932027907862888867615 12814398041861794333301423)
      ·
        refine ⟨19221597062792691499952135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12814398041861794333301423 19221597062792691499952135)
        ·
          refine ⟨28832395594189037249928203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19221597062792691499952135 28832395594189037249928203)
          ·
            refine ⟨43248593391283555874892305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28832395594189037249928203 43248593391283555874892305)
            ·
              refine ⟨32436445043462666906169229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43248593391283555874892305 32436445043462666906169229)
              ·
                refine ⟨12163666891298500089813461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32436445043462666906169229 12163666891298500089813461)
                ·
                  refine ⟨285085942764808595855003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12163666891298500089813461 285085942764808595855003)
                  ·
                    rfl

theorem cell22_2498413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2498413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498413 prefixEnd_2498413 := by exact prefixLift 2498413
  have htrace : WordTrace (prefixWord ++ tailWord_2498413) baseStart_2498413 baseEnd_2498413 := by
    simpa [prefixWord, tailWord_2498413, baseEnd_2498413] using wordTrace_append hprefix tailTrace_2498413
  have hstable : (prefixWord ++ tailWord_2498413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498413).length < 2 ^ (prefixWord ++ tailWord_2498413).sum := by decide
  have hdescent : baseEnd_2498413 < baseStart_2498413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498417 : List Nat := [1, 2, 2, 2, 1, 3, 3, 4, 1, 3]
def baseStart_2498417 : Nat := 118140960795 + 2498417 * 2 ^ 59
def prefixEnd_2498417 : Nat := 4983230072969 + 3 ^ 40 * 2498417 * 2
def baseEnd_2498417 : Nat := 855259197576171110464997

theorem tailTrace_2498417 : CollatzResearch.WordTrace tailWord_2498417 prefixEnd_2498417 855259197576171110464997 := by
  unfold tailWord_2498417
  simp only [CollatzResearch.WordTrace]
  refine ⟨91124754189669379497733505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60749836126446252998489003 91124754189669379497733505)
  ·
    refine ⟨68343565642252034623300129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91124754189669379497733505 68343565642252034623300129)
    ·
      refine ⟨51257674231689025967475097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68343565642252034623300129 51257674231689025967475097)
      ·
        refine ⟨38443255673766769475606323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51257674231689025967475097 38443255673766769475606323)
        ·
          refine ⟨57664883510650154213409485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38443255673766769475606323 57664883510650154213409485)
          ·
            refine ⟨21624331316493807830028557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57664883510650154213409485 21624331316493807830028557)
            ·
              refine ⟨8109124243685177936260709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21624331316493807830028557 8109124243685177936260709)
              ·
                refine ⟨1520460795690970863048883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8109124243685177936260709 1520460795690970863048883)
                ·
                  refine ⟨2280691193536456294573325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520460795690970863048883 2280691193536456294573325)
                  ·
                    refine ⟨855259197576171110464997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280691193536456294573325 855259197576171110464997)
                    ·
                      rfl

theorem cell22_2498417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_2498417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498417 prefixEnd_2498417 := by exact prefixLift 2498417
  have htrace : WordTrace (prefixWord ++ tailWord_2498417) baseStart_2498417 baseEnd_2498417 := by
    simpa [prefixWord, tailWord_2498417, baseEnd_2498417] using wordTrace_append hprefix tailTrace_2498417
  have hstable : (prefixWord ++ tailWord_2498417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498417).length < 2 ^ (prefixWord ++ tailWord_2498417).sum := by decide
  have hdescent : baseEnd_2498417 < baseStart_2498417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498488 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_2498488 : Nat := 118140960795 + 2498488 * 2 ^ 59
def prefixEnd_2498488 : Nat := 4983230072969 + 3 ^ 40 * 2498488 * 2
def baseEnd_2498488 : Nat := 855283502327150591939779

theorem tailTrace_2498488 : CollatzResearch.WordTrace tailWord_2498488 prefixEnd_2498488 855283502327150591939779 := by
  unfold tailWord_2498488
  simp only [CollatzResearch.WordTrace]
  refine ⟨45563671886206079311784059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60751562514941439082378745 45563671886206079311784059)
  ·
    refine ⟨68345507829309118967676089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45563671886206079311784059 68345507829309118967676089)
    ·
      refine ⟨51259130871981839225757067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68345507829309118967676089 51259130871981839225757067)
      ·
        refine ⟨76888696307972758838635601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51259130871981839225757067 76888696307972758838635601)
        ·
          refine ⟨57666522230979569128976701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76888696307972758838635601 57666522230979569128976701)
          ·
            refine ⟨21624945836617338423366263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57666522230979569128976701 21624945836617338423366263)
            ·
              refine ⟨32437418754926007635049395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21624945836617338423366263 32437418754926007635049395)
              ·
                refine ⟨48656128132389011452574093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32437418754926007635049395 48656128132389011452574093)
                ·
                  refine ⟨18246048049645879294715285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48656128132389011452574093 18246048049645879294715285)
                  ·
                    refine ⟨855283502327150591939779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18246048049645879294715285 855283502327150591939779)
                    ·
                      rfl

theorem cell22_2498488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_2498488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498488 prefixEnd_2498488 := by exact prefixLift 2498488
  have htrace : WordTrace (prefixWord ++ tailWord_2498488) baseStart_2498488 baseEnd_2498488 := by
    simpa [prefixWord, tailWord_2498488, baseEnd_2498488] using wordTrace_append hprefix tailTrace_2498488
  have hstable : (prefixWord ++ tailWord_2498488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498488).length < 2 ^ (prefixWord ++ tailWord_2498488).sum := by decide
  have hdescent : baseEnd_2498488 < baseStart_2498488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498522 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_2498522 : Nat := 118140960795 + 2498522 * 2 ^ 59
def prefixEnd_2498522 : Nat := 4983230072969 + 3 ^ 40 * 2498522 * 2
def baseEnd_2498522 : Nat := 855295141221985836589675

theorem tailTrace_2498522 : CollatzResearch.WordTrace tailWord_2498522 prefixEnd_2498522 855295141221985836589675 := by
  unfold tailWord_2498522
  simp only [CollatzResearch.WordTrace]
  refine ⟨22782145963572245607576455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60752389236192654953537213 22782145963572245607576455)
  ·
    refine ⟨34173218945358368411364683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22782145963572245607576455 34173218945358368411364683)
    ·
      refine ⟨51259828418037552617047025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34173218945358368411364683 51259828418037552617047025)
      ·
        refine ⟨38444871313528164462785269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51259828418037552617047025 38444871313528164462785269)
        ·
          refine ⟨3604206685643265418386119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38444871313528164462785269 3604206685643265418386119)
          ·
            refine ⟨5406310028464898127579179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604206685643265418386119 5406310028464898127579179)
            ·
              refine ⟨8109465042697347191368769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5406310028464898127579179 8109465042697347191368769)
              ·
                refine ⟨6082098782023010393526577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8109465042697347191368769 6082098782023010393526577)
                ·
                  refine ⟨4561574086517257795144933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6082098782023010393526577 4561574086517257795144933)
                  ·
                    refine ⟨855295141221985836589675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4561574086517257795144933 855295141221985836589675)
                    ·
                      rfl

theorem cell22_2498522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_2498522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498522 prefixEnd_2498522 := by exact prefixLift 2498522
  have htrace : WordTrace (prefixWord ++ tailWord_2498522) baseStart_2498522 baseEnd_2498522 := by
    simpa [prefixWord, tailWord_2498522, baseEnd_2498522] using wordTrace_append hprefix tailTrace_2498522
  have hstable : (prefixWord ++ tailWord_2498522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498522).length < 2 ^ (prefixWord ++ tailWord_2498522).sum := by decide
  have hdescent : baseEnd_2498522 < baseStart_2498522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498541 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_2498541 : Nat := 118140960795 + 2498541 * 2 ^ 59
def prefixEnd_2498541 : Nat := 4983230072969 + 3 ^ 40 * 2498541 * 2
def baseEnd_2498541 : Nat := 855301645310276120364617

theorem tailTrace_2498541 : CollatzResearch.WordTrace tailWord_2498541 prefixEnd_2498541 855301645310276120364617 := by
  unfold tailWord_2498541
  simp only [CollatzResearch.WordTrace]
  refine ⟨91129276841220148675247477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60752851227480099116831651 91129276841220148675247477)
  ·
    refine ⟨8543369703864388938304451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91129276841220148675247477 8543369703864388938304451)
    ·
      refine ⟨12815054555796583407456677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8543369703864388938304451 12815054555796583407456677)
      ·
        refine ⟨2402822729211859388898127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12815054555796583407456677 2402822729211859388898127)
        ·
          refine ⟨3604234093817789083347191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402822729211859388898127 3604234093817789083347191)
          ·
            refine ⟨5406351140726683625020787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604234093817789083347191 5406351140726683625020787)
            ·
              refine ⟨8109526711090025437531181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5406351140726683625020787 8109526711090025437531181)
              ·
                refine ⟨3041072516658759539074193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8109526711090025437531181 3041072516658759539074193)
                ·
                  refine ⟨2280804387494069654305645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3041072516658759539074193 2280804387494069654305645)
                  ·
                    refine ⟨855301645310276120364617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280804387494069654305645 855301645310276120364617)
                    ·
                      rfl

theorem cell22_2498541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_2498541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498541 prefixEnd_2498541 := by exact prefixLift 2498541
  have htrace : WordTrace (prefixWord ++ tailWord_2498541) baseStart_2498541 baseEnd_2498541 := by
    simpa [prefixWord, tailWord_2498541, baseEnd_2498541] using wordTrace_append hprefix tailTrace_2498541
  have hstable : (prefixWord ++ tailWord_2498541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498541).length < 2 ^ (prefixWord ++ tailWord_2498541).sum := by decide
  have hdescent : baseEnd_2498541 < baseStart_2498541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498586 : List Nat := [3, 1, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_2498586 : Nat := 118140960795 + 2498586 * 2 ^ 59
def prefixEnd_2498586 : Nat := 4983230072969 + 3 ^ 40 * 2498586 * 2
def baseEnd_2498586 : Nat := 855317049729911002989479

theorem tailTrace_2498586 : CollatzResearch.WordTrace tailWord_2498586 prefixEnd_2498586 855317049729911002989479 := by
  unfold tailWord_2498586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22782729531514280340158903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60753945417371414240423741 22782729531514280340158903)
  ·
    refine ⟨34174094297271420510238355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22782729531514280340158903 34174094297271420510238355)
    ·
      refine ⟨51261141445907130765357533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34174094297271420510238355 51261141445907130765357533)
      ·
        refine ⟨19222928042215174037009075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51261141445907130765357533 19222928042215174037009075)
        ·
          refine ⟨28834392063322761055513613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19222928042215174037009075 28834392063322761055513613)
          ·
            refine ⟨10812897023746035395817605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28834392063322761055513613 10812897023746035395817605)
            ·
              refine ⟨2027418191952381636715801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10812897023746035395817605 2027418191952381636715801)
              ·
                refine ⟨1520563643964286227536851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027418191952381636715801 1520563643964286227536851)
                ·
                  refine ⟨2280845465946429341305277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520563643964286227536851 2280845465946429341305277)
                  ·
                    refine ⟨855317049729911002989479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280845465946429341305277 855317049729911002989479)
                    ·
                      rfl

theorem cell22_2498586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_2498586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498586 prefixEnd_2498586 := by exact prefixLift 2498586
  have htrace : WordTrace (prefixWord ++ tailWord_2498586) baseStart_2498586 baseEnd_2498586 := by
    simpa [prefixWord, tailWord_2498586, baseEnd_2498586] using wordTrace_append hprefix tailTrace_2498586
  have hstable : (prefixWord ++ tailWord_2498586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498586).length < 2 ^ (prefixWord ++ tailWord_2498586).sum := by decide
  have hdescent : baseEnd_2498586 < baseStart_2498586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498595 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 5, 4]
def baseStart_2498595 : Nat := 118140960795 + 2498595 * 2 ^ 59
def prefixEnd_2498595 : Nat := 4983230072969 + 3 ^ 40 * 2498595 * 2
def baseEnd_2498595 : Nat := 855320130613837979514451

theorem tailTrace_2498595 : CollatzResearch.WordTrace tailWord_2498595 prefixEnd_2498595 855320130613837979514451 := by
  unfold tailWord_2498595
  simp only [CollatzResearch.WordTrace]
  refine ⟨91131246383024515897713239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60754164255349677265142159 91131246383024515897713239)
  ·
    refine ⟨136696869574536773846569859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91131246383024515897713239 136696869574536773846569859)
    ·
      refine ⟨205045304361805160769854789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136696869574536773846569859 205045304361805160769854789)
      ·
        refine ⟨38445994567838467644347773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205045304361805160769854789 38445994567838467644347773)
        ·
          refine ⟨14417247962939425366630415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38445994567838467644347773 14417247962939425366630415)
          ·
            refine ⟨21625871944409138049945623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14417247962939425366630415 21625871944409138049945623)
            ·
              refine ⟨32438807916613707074918435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21625871944409138049945623 32438807916613707074918435)
              ·
                refine ⟨48658211874920560612377653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32438807916613707074918435 48658211874920560612377653)
                ·
                  refine ⟨4561707363273802557410405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48658211874920560612377653 4561707363273802557410405)
                  ·
                    refine ⟨855320130613837979514451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4561707363273802557410405 855320130613837979514451)
                    ·
                      rfl

theorem cell22_2498595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 4].length) (baseStart_2498595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498595 prefixEnd_2498595 := by exact prefixLift 2498595
  have htrace : WordTrace (prefixWord ++ tailWord_2498595) baseStart_2498595 baseEnd_2498595 := by
    simpa [prefixWord, tailWord_2498595, baseEnd_2498595] using wordTrace_append hprefix tailTrace_2498595
  have hstable : (prefixWord ++ tailWord_2498595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498595).length < 2 ^ (prefixWord ++ tailWord_2498595).sum := by decide
  have hdescent : baseEnd_2498595 < baseStart_2498595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498610 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_2498610 : Nat := 118140960795 + 2498610 * 2 ^ 59
def prefixEnd_2498610 : Nat := 4983230072969 + 3 ^ 40 * 2498610 * 2
def baseEnd_2498610 : Nat := 285108421806794313463135

theorem tailTrace_2498610 : CollatzResearch.WordTrace tailWord_2498610 prefixEnd_2498610 285108421806794313463135 := by
  unfold tailWord_2498610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22782948369492543364877321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60754528985313448973006189 22782948369492543364877321)
  ·
    refine ⟨17087211277119407523657991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22782948369492543364877321 17087211277119407523657991)
    ·
      refine ⟨25630816915679111285486987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17087211277119407523657991 25630816915679111285486987)
      ·
        refine ⟨38446225373518666928230481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25630816915679111285486987 38446225373518666928230481)
        ·
          refine ⟨28834669030139000196172861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38446225373518666928230481 28834669030139000196172861)
          ·
            refine ⟨10813000886302125073564823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28834669030139000196172861 10813000886302125073564823)
            ·
              refine ⟨16219501329453187610347235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10813000886302125073564823 16219501329453187610347235)
              ·
                refine ⟨24329251994179781415520853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16219501329453187610347235 24329251994179781415520853)
                ·
                  refine ⟨285108421806794313463135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24329251994179781415520853 285108421806794313463135)
                  ·
                    rfl

theorem cell22_2498610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_2498610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498610 prefixEnd_2498610 := by exact prefixLift 2498610
  have htrace : WordTrace (prefixWord ++ tailWord_2498610) baseStart_2498610 baseEnd_2498610 := by
    simpa [prefixWord, tailWord_2498610, baseEnd_2498610] using wordTrace_append hprefix tailTrace_2498610
  have hstable : (prefixWord ++ tailWord_2498610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498610).length < 2 ^ (prefixWord ++ tailWord_2498610).sum := by decide
  have hdescent : baseEnd_2498610 < baseStart_2498610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498672 : List Nat := [2, 1, 1, 1, 5, 2, 4, 6]
def baseStart_2498672 : Nat := 118140960795 + 2498672 * 2 ^ 59
def prefixEnd_2498672 : Nat := 4983230072969 + 3 ^ 40 * 2498672 * 2
def baseEnd_2498672 : Nat := 95038498809715049482135

theorem tailTrace_2498672 : CollatzResearch.WordTrace tailWord_2498672 prefixEnd_2498672 95038498809715049482135 := by
  unfold tailWord_2498672
  simp only [CollatzResearch.WordTrace]
  refine ⟨45567027401872779024133135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60756036535830372032177513 45567027401872779024133135)
  ·
    refine ⟨68350541102809168536199703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45567027401872779024133135 68350541102809168536199703)
    ·
      refine ⟨102525811654213752804299555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68350541102809168536199703 102525811654213752804299555)
      ·
        refine ⟨153788717481320629206449333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102525811654213752804299555 153788717481320629206449333)
        ·
          refine ⟨14417692263873808988104625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153788717481320629206449333 14417692263873808988104625)
          ·
            refine ⟨10813269197905356741078469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14417692263873808988104625 10813269197905356741078469)
            ·
              refine ⟨2027487974607254388952213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10813269197905356741078469 2027487974607254388952213)
              ·
                refine ⟨95038498809715049482135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2027487974607254388952213 95038498809715049482135)
                ·
                  rfl

theorem cell22_2498672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 6].length) (baseStart_2498672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498672 prefixEnd_2498672 := by exact prefixLift 2498672
  have htrace : WordTrace (prefixWord ++ tailWord_2498672) baseStart_2498672 baseEnd_2498672 := by
    simpa [prefixWord, tailWord_2498672, baseEnd_2498672] using wordTrace_append hprefix tailTrace_2498672
  have hstable : (prefixWord ++ tailWord_2498672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498672).length < 2 ^ (prefixWord ++ tailWord_2498672).sum := by decide
  have hdescent : baseEnd_2498672 < baseStart_2498672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498689 : List Nat := [1, 2, 4, 2, 4, 1, 8]
def baseStart_2498689 : Nat := 118140960795 + 2498689 * 2 ^ 59
def prefixEnd_2498689 : Nat := 4983230072969 + 3 ^ 40 * 2498689 * 2
def baseEnd_2498689 : Nat := 31679715138327891394969

theorem tailTrace_2498689 : CollatzResearch.WordTrace tailWord_2498689 prefixEnd_2498689 31679715138327891394969 := by
  unfold tailWord_2498689
  simp only [CollatzResearch.WordTrace]
  refine ⟨91134674844683969951635121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60756449896455979967756747 91134674844683969951635121)
  ·
    refine ⟨68351006133512977463726341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91134674844683969951635121 68351006133512977463726341)
    ·
      refine ⟨12815813650033683274448689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68351006133512977463726341 12815813650033683274448689)
      ·
        refine ⟨9611860237525262455836517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12815813650033683274448689 9611860237525262455836517)
        ·
          refine ⟨1802223794535986710469347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9611860237525262455836517 1802223794535986710469347)
          ·
            refine ⟨2703335691803980065704021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802223794535986710469347 2703335691803980065704021)
            ·
              refine ⟨31679715138327891394969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2703335691803980065704021 31679715138327891394969)
              ·
                rfl

theorem cell22_2498689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 8].length) (baseStart_2498689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498689 prefixEnd_2498689 := by exact prefixLift 2498689
  have htrace : WordTrace (prefixWord ++ tailWord_2498689) baseStart_2498689 baseEnd_2498689 := by
    simpa [prefixWord, tailWord_2498689, baseEnd_2498689] using wordTrace_append hprefix tailTrace_2498689
  have hstable : (prefixWord ++ tailWord_2498689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498689).length < 2 ^ (prefixWord ++ tailWord_2498689).sum := by decide
  have hdescent : baseEnd_2498689 < baseStart_2498689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498762 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_2498762 : Nat := 118140960795 + 2498762 * 2 ^ 59
def prefixEnd_2498762 : Nat := 4983230072969 + 3 ^ 40 * 2498762 * 2
def baseEnd_2498762 : Nat := 285125766042235070196313

theorem tailTrace_2498762 : CollatzResearch.WordTrace tailWord_2498762 prefixEnd_2498762 285125766042235070196313 := by
  unfold tailWord_2498762
  simp only [CollatzResearch.WordTrace]
  refine ⟨22784334343354875854760635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60758224915613002279361693 22784334343354875854760635)
  ·
    refine ⟨34176501515032313782140953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22784334343354875854760635 34176501515032313782140953)
    ·
      refine ⟨25632376136274235336605715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34176501515032313782140953 25632376136274235336605715)
      ·
        refine ⟨38448564204411353004908573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25632376136274235336605715 38448564204411353004908573)
        ·
          refine ⟨14418211576654257376840715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38448564204411353004908573 14418211576654257376840715)
          ·
            refine ⟨21627317364981386065261073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14418211576654257376840715 21627317364981386065261073)
            ·
              refine ⟨16220488023736039548945805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21627317364981386065261073 16220488023736039548945805)
              ·
                refine ⟨6082683008901014830854677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16220488023736039548945805 6082683008901014830854677)
                ·
                  refine ⟨285125766042235070196313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6082683008901014830854677 285125766042235070196313)
                  ·
                    rfl

theorem cell22_2498762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_2498762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498762 prefixEnd_2498762 := by exact prefixLift 2498762
  have htrace : WordTrace (prefixWord ++ tailWord_2498762) baseStart_2498762 baseEnd_2498762 := by
    simpa [prefixWord, tailWord_2498762, baseEnd_2498762] using wordTrace_append hprefix tailTrace_2498762
  have hstable : (prefixWord ++ tailWord_2498762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498762).length < 2 ^ (prefixWord ++ tailWord_2498762).sum := by decide
  have hdescent : baseEnd_2498762 < baseStart_2498762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498777 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_2498777 : Nat := 118140960795 + 2498777 * 2 ^ 59
def prefixEnd_2498777 : Nat := 4983230072969 + 3 ^ 40 * 2498777 * 2
def baseEnd_2498777 : Nat := 855382432933250171463893

theorem tailTrace_2498777 : CollatzResearch.WordTrace tailWord_2498777 prefixEnd_2498777 855382432933250171463893 := by
  unfold tailWord_2498777
  simp only [CollatzResearch.WordTrace]
  refine ⟨91137884468365160980838585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60758589645576773987225723 91137884468365160980838585)
  ·
    refine ⟨68353413351273870735628939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91137884468365160980838585 68353413351273870735628939)
    ·
      refine ⟨102530120026910806103443409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68353413351273870735628939 102530120026910806103443409)
      ·
        refine ⟨76897590020183104577582557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102530120026910806103443409 76897590020183104577582557)
        ·
          refine ⟨28836596257568664216593459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76897590020183104577582557 28836596257568664216593459)
          ·
            refine ⟨43254894386352996324890189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28836596257568664216593459 43254894386352996324890189)
            ·
              refine ⟨16220585394882373621833821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43254894386352996324890189 16220585394882373621833821)
              ·
                refine ⟨6082719523080890108187683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16220585394882373621833821 6082719523080890108187683)
                ·
                  refine ⟨9124079284621335162281525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6082719523080890108187683 9124079284621335162281525)
                  ·
                    refine ⟨855382432933250171463893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9124079284621335162281525 855382432933250171463893)
                    ·
                      rfl

theorem cell22_2498777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_2498777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498777 prefixEnd_2498777 := by exact prefixLift 2498777
  have htrace : WordTrace (prefixWord ++ tailWord_2498777) baseStart_2498777 baseEnd_2498777 := by
    simpa [prefixWord, tailWord_2498777, baseEnd_2498777] using wordTrace_append hprefix tailTrace_2498777
  have hstable : (prefixWord ++ tailWord_2498777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498777).length < 2 ^ (prefixWord ++ tailWord_2498777).sum := by decide
  have hdescent : baseEnd_2498777 < baseStart_2498777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498794 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_2498794 : Nat := 118140960795 + 2498794 * 2 ^ 59
def prefixEnd_2498794 : Nat := 4983230072969 + 3 ^ 40 * 2498794 * 2
def baseEnd_2498794 : Nat := 855388252380667793788841

theorem tailTrace_2498794 : CollatzResearch.WordTrace tailWord_2498794 prefixEnd_2498794 855388252380667793788841 := by
  unfold tailWord_2498794
  simp only [CollatzResearch.WordTrace]
  refine ⟨22784626127325893221051859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60759003006202381922804957 22784626127325893221051859)
  ·
    refine ⟨34176939190988839831577789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22784626127325893221051859 34176939190988839831577789)
    ·
      refine ⟨12816352196620814936841671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34176939190988839831577789 12816352196620814936841671)
      ·
        refine ⟨19224528294931222405262507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12816352196620814936841671 19224528294931222405262507)
        ·
          refine ⟨28836792442396833607893761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19224528294931222405262507 28836792442396833607893761)
          ·
            refine ⟨21627594331797625205920321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28836792442396833607893761 21627594331797625205920321)
            ·
              refine ⟨16220695748848218904440241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21627594331797625205920321 16220695748848218904440241)
              ·
                refine ⟨12165521811636164178330181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16220695748848218904440241 12165521811636164178330181)
                ·
                  refine ⟨2281035339681780783436909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12165521811636164178330181 2281035339681780783436909)
                  ·
                    refine ⟨855388252380667793788841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2281035339681780783436909 855388252380667793788841)
                    ·
                      rfl

theorem cell22_2498794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_2498794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498794 prefixEnd_2498794 := by exact prefixLift 2498794
  have htrace : WordTrace (prefixWord ++ tailWord_2498794) baseStart_2498794 baseEnd_2498794 := by
    simpa [prefixWord, tailWord_2498794, baseEnd_2498794] using wordTrace_append hprefix tailTrace_2498794
  have hstable : (prefixWord ++ tailWord_2498794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498794).length < 2 ^ (prefixWord ++ tailWord_2498794).sum := by decide
  have hdescent : baseEnd_2498794 < baseStart_2498794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498837 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2498837 : Nat := 118140960795 + 2498837 * 2 ^ 59
def prefixEnd_2498837 : Nat := 4983230072969 + 3 ^ 40 * 2498837 * 2
def baseEnd_2498837 : Nat := 855402972159430014963709

theorem tailTrace_2498837 : CollatzResearch.WordTrace tailWord_2498837 prefixEnd_2498837 855402972159430014963709 := by
  unfold tailWord_2498837
  simp only [CollatzResearch.WordTrace]
  refine ⟨91140072848147791228022765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60760048565431860818681843 91140072848147791228022765)
  ·
    refine ⟨34177527318055421710508537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91140072848147791228022765 34177527318055421710508537)
    ·
      refine ⟨25633145488541566282881403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34177527318055421710508537 25633145488541566282881403)
      ·
        refine ⟨38449718232812349424322105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25633145488541566282881403 38449718232812349424322105)
        ·
          refine ⟨28837288674609262068241579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38449718232812349424322105 28837288674609262068241579)
          ·
            refine ⟨43255933011913893102362369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28837288674609262068241579 43255933011913893102362369)
            ·
              refine ⟨32441949758935419826771777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43255933011913893102362369 32441949758935419826771777)
              ·
                refine ⟨24331462319201564870078833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32441949758935419826771777 24331462319201564870078833)
                ·
                  refine ⟨18248596739401173652559125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24331462319201564870078833 18248596739401173652559125)
                  ·
                    refine ⟨855402972159430014963709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18248596739401173652559125 855402972159430014963709)
                    ·
                      rfl

theorem cell22_2498837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2498837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498837 prefixEnd_2498837 := by exact prefixLift 2498837
  have htrace : WordTrace (prefixWord ++ tailWord_2498837) baseStart_2498837 baseEnd_2498837 := by
    simpa [prefixWord, tailWord_2498837, baseEnd_2498837] using wordTrace_append hprefix tailTrace_2498837
  have hstable : (prefixWord ++ tailWord_2498837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498837).length < 2 ^ (prefixWord ++ tailWord_2498837).sum := by decide
  have hdescent : baseEnd_2498837 < baseStart_2498837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498869 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 5]
def baseStart_2498869 : Nat := 118140960795 + 2498869 * 2 ^ 59
def prefixEnd_2498869 : Nat := 4983230072969 + 3 ^ 40 * 2498869 * 2
def baseEnd_2498869 : Nat := 285137975471130866054537

theorem tailTrace_2498869 : CollatzResearch.WordTrace tailWord_2498869 prefixEnd_2498869 285137975471130866054537 := by
  unfold tailWord_2498869
  simp only [CollatzResearch.WordTrace]
  refine ⟨91141239984031860693187661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60760826656021240462125107 91141239984031860693187661)
  ·
    refine ⟨34177964994011947759945373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91141239984031860693187661 34177964994011947759945373)
    ·
      refine ⟨12816736872754480409979515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34177964994011947759945373 12816736872754480409979515)
      ·
        refine ⟨19225105309131720614969273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12816736872754480409979515 19225105309131720614969273)
        ·
          refine ⟨14418828981848790461226955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19225105309131720614969273 14418828981848790461226955)
          ·
            refine ⟨21628243472773185691840433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14418828981848790461226955 21628243472773185691840433)
            ·
              refine ⟨16221182604579889268880325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21628243472773185691840433 16221182604579889268880325)
              ·
                refine ⟨3041471738358729237915061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16221182604579889268880325 3041471738358729237915061)
                ·
                  refine ⟨285137975471130866054537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3041471738358729237915061 285137975471130866054537)
                  ·
                    rfl

theorem cell22_2498869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_2498869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498869 prefixEnd_2498869 := by exact prefixLift 2498869
  have htrace : WordTrace (prefixWord ++ tailWord_2498869) baseStart_2498869 baseEnd_2498869 := by
    simpa [prefixWord, tailWord_2498869, baseEnd_2498869] using wordTrace_append hprefix tailTrace_2498869
  have hstable : (prefixWord ++ tailWord_2498869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498869).length < 2 ^ (prefixWord ++ tailWord_2498869).sum := by decide
  have hdescent : baseEnd_2498869 < baseStart_2498869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498873 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 3, 3]
def baseStart_2498873 : Nat := 118140960795 + 2498873 * 2 ^ 59
def prefixEnd_2498873 : Nat := 4983230072969 + 3 ^ 40 * 2498873 * 2
def baseEnd_2498873 : Nat := 855415295695137921063599

theorem tailTrace_2498873 : CollatzResearch.WordTrace tailWord_2498873 prefixEnd_2498873 855415295695137921063599 := by
  unfold tailWord_2498873
  simp only [CollatzResearch.WordTrace]
  refine ⟨91141385876017369376333273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60760923917344912917555515 91141385876017369376333273)
  ·
    refine ⟨68356039407013027032249955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91141385876017369376333273 68356039407013027032249955)
    ·
      refine ⟨102534059110519540548374933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68356039407013027032249955 102534059110519540548374933)
      ·
        refine ⟨4806284020805603463205075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102534059110519540548374933 4806284020805603463205075)
        ·
          refine ⟨7209426031208405194807613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806284020805603463205075 7209426031208405194807613)
          ·
            refine ⟨2703534761703151948052855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7209426031208405194807613 2703534761703151948052855)
            ·
              refine ⟨4055302142554727922079283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703534761703151948052855 4055302142554727922079283)
              ·
                refine ⟨6082953213832091883118925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055302142554727922079283 6082953213832091883118925)
                ·
                  refine ⟨2281107455187034456169597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6082953213832091883118925 2281107455187034456169597)
                  ·
                    refine ⟨855415295695137921063599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2281107455187034456169597 855415295695137921063599)
                    ·
                      rfl

theorem cell22_2498873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_2498873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498873 prefixEnd_2498873 := by exact prefixLift 2498873
  have htrace : WordTrace (prefixWord ++ tailWord_2498873) baseStart_2498873 baseEnd_2498873 := by
    simpa [prefixWord, tailWord_2498873, baseEnd_2498873] using wordTrace_append hprefix tailTrace_2498873
  have hstable : (prefixWord ++ tailWord_2498873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498873).length < 2 ^ (prefixWord ++ tailWord_2498873).sum := by decide
  have hdescent : baseEnd_2498873 < baseStart_2498873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2498899 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 1, 4]
def baseStart_2498899 : Nat := 118140960795 + 2498899 * 2 ^ 59
def prefixEnd_2498899 : Nat := 4983230072969 + 3 ^ 40 * 2498899 * 2
def baseEnd_2498899 : Nat := 855424196026482519913519

theorem tailTrace_2498899 : CollatzResearch.WordTrace tailWord_2498899 prefixEnd_2498899 855424196026482519913519 := by
  unfold tailWord_2498899
  simp only [CollatzResearch.WordTrace]
  refine ⟨91142334173923175816779751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60761556115948783877853167 91142334173923175816779751)
  ·
    refine ⟨136713501260884763725169627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91142334173923175816779751 136713501260884763725169627)
    ·
      refine ⟨205070251891327145587754441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136713501260884763725169627 205070251891327145587754441)
      ·
        refine ⟨153802688918495359190815831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205070251891327145587754441 153802688918495359190815831)
        ·
          refine ⟨230704033377743038786223747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153802688918495359190815831 230704033377743038786223747)
          ·
            refine ⟨346056050066614558179335621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230704033377743038786223747 346056050066614558179335621)
            ·
              refine ⟨64885509387490229658625429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 346056050066614558179335621 64885509387490229658625429)
              ·
                refine ⟨3041508252538604515248067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64885509387490229658625429 3041508252538604515248067)
                ·
                  refine ⟨4562262378807906772872101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3041508252538604515248067 4562262378807906772872101)
                  ·
                    refine ⟨855424196026482519913519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4562262378807906772872101 855424196026482519913519)
                    ·
                      rfl

theorem cell22_2498899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 4].length) (baseStart_2498899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2498899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2498899 prefixEnd_2498899 := by exact prefixLift 2498899
  have htrace : WordTrace (prefixWord ++ tailWord_2498899) baseStart_2498899 baseEnd_2498899 := by
    simpa [prefixWord, tailWord_2498899, baseEnd_2498899] using wordTrace_append hprefix tailTrace_2498899
  have hstable : (prefixWord ++ tailWord_2498899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2498899).length < 2 ^ (prefixWord ++ tailWord_2498899).sum := by decide
  have hdescent : baseEnd_2498899 < baseStart_2498899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2498899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499049 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 6]
def baseStart_2499049 : Nat := 118140960795 + 2499049 * 2 ^ 59
def prefixEnd_2499049 : Nat := 4983230072969 + 3 ^ 40 * 2499049 * 2
def baseEnd_2499049 : Nat := 285158514697310709554353

theorem tailTrace_2499049 : CollatzResearch.WordTrace tailWord_2499049 prefixEnd_2499049 285158514697310709554353 := by
  unfold tailWord_2499049
  simp only [CollatzResearch.WordTrace]
  refine ⟨91147805123379751434740201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60765203415586500956493467 91147805123379751434740201)
  ·
    refine ⟨68360853842534813576055151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91147805123379751434740201 68360853842534813576055151)
    ·
      refine ⟨102541280763802220364082727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68360853842534813576055151 102541280763802220364082727)
      ·
        refine ⟨153811921145703330546124091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102541280763802220364082727 153811921145703330546124091)
        ·
          refine ⟨230717881718554995819186137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153811921145703330546124091 230717881718554995819186137)
          ·
            refine ⟨173038411288916246864389603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230717881718554995819186137 173038411288916246864389603)
            ·
              refine ⟨259557616933374370296584405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173038411288916246864389603 259557616933374370296584405)
              ·
                refine ⟨6083381646875961803826197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 259557616933374370296584405 6083381646875961803826197)
                ·
                  refine ⟨285158514697310709554353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6083381646875961803826197 285158514697310709554353)
                  ·
                    rfl

theorem cell22_2499049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_2499049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499049 prefixEnd_2499049 := by exact prefixLift 2499049
  have htrace : WordTrace (prefixWord ++ tailWord_2499049) baseStart_2499049 baseEnd_2499049 := by
    simpa [prefixWord, tailWord_2499049, baseEnd_2499049] using wordTrace_append hprefix tailTrace_2499049
  have hstable : (prefixWord ++ tailWord_2499049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499049).length < 2 ^ (prefixWord ++ tailWord_2499049).sum := by decide
  have hdescent : baseEnd_2499049 < baseStart_2499049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499081 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 4, 3]
def baseStart_2499081 : Nat := 118140960795 + 2499081 * 2 ^ 59
def prefixEnd_2499081 : Nat := 4983230072969 + 3 ^ 40 * 2499081 * 2
def baseEnd_2499081 : Nat := 855486498345894711862961

theorem tailTrace_2499081 : CollatzResearch.WordTrace tailWord_2499081 prefixEnd_2499081 855486498345894711862961 := by
  unfold tailWord_2499081
  simp only [CollatzResearch.WordTrace]
  refine ⟨91148972259263820899905097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60765981506175880599936731 91148972259263820899905097)
  ·
    refine ⟨68361729194447865674928823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91148972259263820899905097 68361729194447865674928823)
    ·
      refine ⟨102542593791671798512393235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68361729194447865674928823 102542593791671798512393235)
      ·
        refine ⟨153813890687507697768589853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102542593791671798512393235 153813890687507697768589853)
        ·
          refine ⟨57680209007815386663221195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153813890687507697768589853 57680209007815386663221195)
          ·
            refine ⟨86520313511723079994831793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57680209007815386663221195 86520313511723079994831793)
            ·
              refine ⟨64890235133792309996123845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86520313511723079994831793 64890235133792309996123845)
              ·
                refine ⟨12166919087586058124273221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64890235133792309996123845 12166919087586058124273221)
                ·
                  refine ⟨2281297328922385898301229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12166919087586058124273221 2281297328922385898301229)
                  ·
                    refine ⟨855486498345894711862961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2281297328922385898301229 855486498345894711862961)
                    ·
                      rfl

theorem cell22_2499081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_2499081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499081 prefixEnd_2499081 := by exact prefixLift 2499081
  have htrace : WordTrace (prefixWord ++ tailWord_2499081) baseStart_2499081 baseEnd_2499081 := by
    simpa [prefixWord, tailWord_2499081, baseEnd_2499081] using wordTrace_append hprefix tailTrace_2499081
  have hstable : (prefixWord ++ tailWord_2499081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499081).length < 2 ^ (prefixWord ++ tailWord_2499081).sum := by decide
  have hdescent : baseEnd_2499081 < baseStart_2499081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499098 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_2499098 : Nat := 118140960795 + 2499098 * 2 ^ 59
def prefixEnd_2499098 : Nat := 4983230072969 + 3 ^ 40 * 2499098 * 2
def baseEnd_2499098 : Nat := 855492317793312334187909

theorem tailTrace_2499098 : CollatzResearch.WordTrace tailWord_2499098 prefixEnd_2499098 855492317793312334187909 := by
  unfold tailWord_2499098
  simp only [CollatzResearch.WordTrace]
  refine ⟨22787398075050558200818487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60766394866801488535515965 22787398075050558200818487)
  ·
    refine ⟨34181097112575837301227731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22787398075050558200818487 34181097112575837301227731)
    ·
      refine ⟨51271645668863755951841597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34181097112575837301227731 51271645668863755951841597)
      ·
        refine ⟨19226867125823908481940599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51271645668863755951841597 19226867125823908481940599)
        ·
          refine ⟨28840300688735862722910899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19226867125823908481940599 28840300688735862722910899)
          ·
            refine ⟨43260451033103794084366349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28840300688735862722910899 43260451033103794084366349)
            ·
              refine ⟨16222669137413922781637381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43260451033103794084366349 16222669137413922781637381)
              ·
                refine ⟨3041750463265110521557009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16222669137413922781637381 3041750463265110521557009)
                ·
                  refine ⟨2281312847448832891167757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3041750463265110521557009 2281312847448832891167757)
                  ·
                    refine ⟨855492317793312334187909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2281312847448832891167757 855492317793312334187909)
                    ·
                      rfl

theorem cell22_2499098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_2499098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499098 prefixEnd_2499098 := by exact prefixLift 2499098
  have htrace : WordTrace (prefixWord ++ tailWord_2499098) baseStart_2499098 baseEnd_2499098 := by
    simpa [prefixWord, tailWord_2499098, baseEnd_2499098] using wordTrace_append hprefix tailTrace_2499098
  have hstable : (prefixWord ++ tailWord_2499098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499098).length < 2 ^ (prefixWord ++ tailWord_2499098).sum := by decide
  have hdescent : baseEnd_2499098 < baseStart_2499098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499100 : List Nat := [2, 2, 3, 1, 2, 2, 4, 2, 4]
def baseStart_2499100 : Nat := 118140960795 + 2499100 * 2 ^ 59
def prefixEnd_2499100 : Nat := 4983230072969 + 3 ^ 40 * 2499100 * 2
def baseEnd_2499100 : Nat := 285164334144728331879301

theorem tailTrace_2499100 : CollatzResearch.WordTrace tailWord_2499100 prefixEnd_2499100 285164334144728331879301 := by
  unfold tailWord_2499100
  simp only [CollatzResearch.WordTrace]
  refine ⟨45574832623097493572423377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60766443497463324763231169 45574832623097493572423377)
  ·
    refine ⟨34181124467323120179317533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45574832623097493572423377 34181124467323120179317533)
    ·
      refine ⟨12817921675246170067244075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34181124467323120179317533 12817921675246170067244075)
      ·
        refine ⟨19226882512869255100866113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12817921675246170067244075 19226882512869255100866113)
        ·
          refine ⟨14420161884651941325649585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19226882512869255100866113 14420161884651941325649585)
          ·
            refine ⟨10815121413488955994237189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14420161884651941325649585 10815121413488955994237189)
            ·
              refine ⟨2027835265029179248919473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10815121413488955994237189 2027835265029179248919473)
              ·
                refine ⟨1520876448771884436689605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027835265029179248919473 1520876448771884436689605)
                ·
                  refine ⟨285164334144728331879301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520876448771884436689605 285164334144728331879301)
                  ·
                    rfl

theorem cell22_2499100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_2499100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499100 prefixEnd_2499100 := by exact prefixLift 2499100
  have htrace : WordTrace (prefixWord ++ tailWord_2499100) baseStart_2499100 baseEnd_2499100 := by
    simpa [prefixWord, tailWord_2499100, baseEnd_2499100] using wordTrace_append hprefix tailTrace_2499100
  have hstable : (prefixWord ++ tailWord_2499100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499100).length < 2 ^ (prefixWord ++ tailWord_2499100).sum := by decide
  have hdescent : baseEnd_2499100 < baseStart_2499100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499117 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 6]
def baseStart_2499117 : Nat := 118140960795 + 2499117 * 2 ^ 59
def prefixEnd_2499117 : Nat := 4983230072969 + 3 ^ 40 * 2499117 * 2
def baseEnd_2499117 : Nat := 285166273960534205987617

theorem tailTrace_2499117 : CollatzResearch.WordTrace tailWord_2499117 prefixEnd_2499117 285166273960534205987617 := by
  unfold tailWord_2499117
  simp only [CollatzResearch.WordTrace]
  refine ⟨91150285287133399048215605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60766856858088932698810403 91150285287133399048215605)
  ·
    refine ⟨8545339245668756160770213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91150285287133399048215605 8545339245668756160770213)
    ·
      refine ⟨1602251108562891780144415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8545339245668756160770213 1602251108562891780144415)
      ·
        refine ⟨2403376662844337670216623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602251108562891780144415 2403376662844337670216623)
        ·
          refine ⟨3605064994266506505324935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2403376662844337670216623 3605064994266506505324935)
          ·
            refine ⟨5407597491399759757987403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3605064994266506505324935 5407597491399759757987403)
            ·
              refine ⟨8111396237099639636981105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407597491399759757987403 8111396237099639636981105)
              ·
                refine ⟨6083547177824729727735829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8111396237099639636981105 6083547177824729727735829)
                ·
                  refine ⟨285166273960534205987617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6083547177824729727735829 285166273960534205987617)
                  ·
                    rfl

theorem cell22_2499117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_2499117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499117 prefixEnd_2499117 := by exact prefixLift 2499117
  have htrace : WordTrace (prefixWord ++ tailWord_2499117) baseStart_2499117 baseEnd_2499117 := by
    simpa [prefixWord, tailWord_2499117, baseEnd_2499117] using wordTrace_append hprefix tailTrace_2499117
  have hstable : (prefixWord ++ tailWord_2499117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499117).length < 2 ^ (prefixWord ++ tailWord_2499117).sum := by decide
  have hdescent : baseEnd_2499117 < baseStart_2499117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499160 : List Nat := [2, 1, 2, 2, 1, 2, 4, 4, 1, 3]
def baseStart_2499160 : Nat := 118140960795 + 2499160 * 2 ^ 59
def prefixEnd_2499160 : Nat := 4983230072969 + 3 ^ 40 * 2499160 * 2
def baseEnd_2499160 : Nat := 855513541660364839137719

theorem tailTrace_2499160 : CollatzResearch.WordTrace tailWord_2499160 prefixEnd_2499160 855513541660364839137719 := by
  unfold tailWord_2499160
  simp only [CollatzResearch.WordTrace]
  refine ⟨45575926812988808696015467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60767902417318411594687289 45575926812988808696015467)
  ·
    refine ⟨68363890219483213044023201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45575926812988808696015467 68363890219483213044023201)
    ·
      refine ⟨51272917664612409783017401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68363890219483213044023201 51272917664612409783017401)
      ·
        refine ⟨38454688248459307337263051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51272917664612409783017401 38454688248459307337263051)
        ·
          refine ⟨57682032372688961005894577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38454688248459307337263051 57682032372688961005894577)
          ·
            refine ⟨43261524279516720754420933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57682032372688961005894577 43261524279516720754420933)
            ·
              refine ⟨8111535802409385141453925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43261524279516720754420933 8111535802409385141453925)
              ·
                refine ⟨1520912962951759714022611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8111535802409385141453925 1520912962951759714022611)
                ·
                  refine ⟨2281369444427639571033917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520912962951759714022611 2281369444427639571033917)
                  ·
                    refine ⟨855513541660364839137719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2281369444427639571033917 855513541660364839137719)
                    ·
                      rfl

theorem cell22_2499160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_2499160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499160 prefixEnd_2499160 := by exact prefixLift 2499160
  have htrace : WordTrace (prefixWord ++ tailWord_2499160) baseStart_2499160 baseEnd_2499160 := by
    simpa [prefixWord, tailWord_2499160, baseEnd_2499160] using wordTrace_append hprefix tailTrace_2499160
  have hstable : (prefixWord ++ tailWord_2499160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499160).length < 2 ^ (prefixWord ++ tailWord_2499160).sum := by decide
  have hdescent : baseEnd_2499160 < baseStart_2499160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499166 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2499166 : Nat := 118140960795 + 2499166 * 2 ^ 59
def prefixEnd_2499166 : Nat := 4983230072969 + 3 ^ 40 * 2499166 * 2
def baseEnd_2499166 : Nat := 855515595582982823487701

theorem tailTrace_2499166 : CollatzResearch.WordTrace tailWord_2499166 prefixEnd_2499166 855515595582982823487701 := by
  unfold tailWord_2499166
  simp only [CollatzResearch.WordTrace]
  refine ⟨11394009057994485052093669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60768048309303920277832901 11394009057994485052093669)
  ·
    refine ⟨2136376698373965947267563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11394009057994485052093669 2136376698373965947267563)
    ·
      refine ⟨3204565047560948920901345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136376698373965947267563 3204565047560948920901345)
      ·
        refine ⟨2403423785670711690676009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3204565047560948920901345 2403423785670711690676009)
        ·
          refine ⟨1802567839253033768007007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2403423785670711690676009 1802567839253033768007007)
          ·
            refine ⟨2703851758879550652010511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802567839253033768007007 2703851758879550652010511)
            ·
              refine ⟨4055777638319325978015767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703851758879550652010511 4055777638319325978015767)
              ·
                refine ⟨6083666457478988967023651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055777638319325978015767 6083666457478988967023651)
                ·
                  refine ⟨9125499686218483450535477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6083666457478988967023651 9125499686218483450535477)
                  ·
                    refine ⟨855515595582982823487701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9125499686218483450535477 855515595582982823487701)
                    ·
                      rfl

theorem cell22_2499166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2499166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499166 prefixEnd_2499166 := by exact prefixLift 2499166
  have htrace : WordTrace (prefixWord ++ tailWord_2499166) baseStart_2499166 baseEnd_2499166 := by
    simpa [prefixWord, tailWord_2499166, baseEnd_2499166] using wordTrace_append hprefix tailTrace_2499166
  have hstable : (prefixWord ++ tailWord_2499166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499166).length < 2 ^ (prefixWord ++ tailWord_2499166).sum := by decide
  have hdescent : baseEnd_2499166 < baseStart_2499166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499171 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 2, 5]
def baseStart_2499171 : Nat := 118140960795 + 2499171 * 2 ^ 59
def prefixEnd_2499171 : Nat := 4983230072969 + 3 ^ 40 * 2499171 * 2
def baseEnd_2499171 : Nat := 855517307185164477112685

theorem tailTrace_2499171 : CollatzResearch.WordTrace tailWord_2499171 prefixEnd_2499171 855517307185164477112685 := by
  unfold tailWord_2499171
  simp only [CollatzResearch.WordTrace]
  refine ⟨91152254828937766270681367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60768169885958510847120911 91152254828937766270681367)
  ·
    refine ⟨136728382243406649406022051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91152254828937766270681367 136728382243406649406022051)
    ·
      refine ⟨205092573365109974109033077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136728382243406649406022051 205092573365109974109033077)
      ·
        refine ⟨19227428752979060072721851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205092573365109974109033077 19227428752979060072721851)
        ·
          refine ⟨28841143129468590109082777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19227428752979060072721851 28841143129468590109082777)
          ·
            refine ⟨21630857347101442581812083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28841143129468590109082777 21630857347101442581812083)
            ·
              refine ⟨32446286020652163872718125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21630857347101442581812083 32446286020652163872718125)
              ·
                refine ⟨12167357257744561452269297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32446286020652163872718125 12167357257744561452269297)
                ·
                  refine ⟨9125517943308421089201973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12167357257744561452269297 9125517943308421089201973)
                  ·
                    refine ⟨855517307185164477112685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9125517943308421089201973 855517307185164477112685)
                    ·
                      rfl

theorem cell22_2499171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_2499171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499171 prefixEnd_2499171 := by exact prefixLift 2499171
  have htrace : WordTrace (prefixWord ++ tailWord_2499171) baseStart_2499171 baseEnd_2499171 := by
    simpa [prefixWord, tailWord_2499171, baseEnd_2499171] using wordTrace_append hprefix tailTrace_2499171
  have hstable : (prefixWord ++ tailWord_2499171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499171).length < 2 ^ (prefixWord ++ tailWord_2499171).sum := by decide
  have hdescent : baseEnd_2499171 < baseStart_2499171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499203 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 1, 4]
def baseStart_2499203 : Nat := 118140960795 + 2499203 * 2 ^ 59
def prefixEnd_2499203 : Nat := 4983230072969 + 3 ^ 40 * 2499203 * 2
def baseEnd_2499203 : Nat := 855528261439127060312587

theorem tailTrace_2499203 : CollatzResearch.WordTrace tailWord_2499203 prefixEnd_2499203 855528261439127060312587 := by
  unfold tailWord_2499203
  simp only [CollatzResearch.WordTrace]
  refine ⟨91153421964821835735846263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60768947976547890490564175 91153421964821835735846263)
  ·
    refine ⟨136730132947232753603769395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91153421964821835735846263 136730132947232753603769395)
    ·
      refine ⟨205095199420849130405654093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136730132947232753603769395 205095199420849130405654093)
      ·
        refine ⟨76910699782818423902120285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205095199420849130405654093 76910699782818423902120285)
        ·
          refine ⟨28841512418556908963295107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76910699782818423902120285 28841512418556908963295107)
          ·
            refine ⟨43262268627835363444942661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28841512418556908963295107 43262268627835363444942661)
            ·
              refine ⟨8111675367719130645926749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43262268627835363444942661 8111675367719130645926749)
              ·
                refine ⟨3041878262894673992222531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8111675367719130645926749 3041878262894673992222531)
                ·
                  refine ⟨4562817394342010988333797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3041878262894673992222531 4562817394342010988333797)
                  ·
                    refine ⟨855528261439127060312587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4562817394342010988333797 855528261439127060312587)
                    ·
                      rfl

theorem cell22_2499203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 4].length) (baseStart_2499203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499203 prefixEnd_2499203 := by exact prefixLift 2499203
  have htrace : WordTrace (prefixWord ++ tailWord_2499203) baseStart_2499203 baseEnd_2499203 := by
    simpa [prefixWord, tailWord_2499203, baseEnd_2499203] using wordTrace_append hprefix tailTrace_2499203
  have hstable : (prefixWord ++ tailWord_2499203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499203).length < 2 ^ (prefixWord ++ tailWord_2499203).sum := by decide
  have hdescent : baseEnd_2499203 < baseStart_2499203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499295 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 3, 3]
def baseStart_2499295 : Nat := 118140960795 + 2499295 * 2 ^ 59
def prefixEnd_2499295 : Nat := 4983230072969 + 3 ^ 40 * 2499295 * 2
def baseEnd_2499295 : Nat := 855559754919269487012305

theorem tailTrace_2499295 : CollatzResearch.WordTrace tailWord_2499295 prefixEnd_2499295 855559754919269487012305 := by
  unfold tailWord_2499295
  simp only [CollatzResearch.WordTrace]
  refine ⟨91156777480488535448195339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60771184986992356965463559 91156777480488535448195339)
  ·
    refine ⟨136735166220732803172293009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91156777480488535448195339 136735166220732803172293009)
    ·
      refine ⟨102551374665549602379219757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136735166220732803172293009 102551374665549602379219757)
      ·
        refine ⟨38456765499581100892207409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102551374665549602379219757 38456765499581100892207409)
        ·
          refine ⟨28842574124685825669155557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38456765499581100892207409 28842574124685825669155557)
          ·
            refine ⟨5407982648378592312966667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28842574124685825669155557 5407982648378592312966667)
            ·
              refine ⟨8111973972567888469450001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407982648378592312966667 8111973972567888469450001)
              ·
                refine ⟨6083980479425916352087501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8111973972567888469450001 6083980479425916352087501)
                ·
                  refine ⟨2281492679784718632032813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6083980479425916352087501 2281492679784718632032813)
                  ·
                    refine ⟨855559754919269487012305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2281492679784718632032813 855559754919269487012305)
                    ·
                      rfl

theorem cell22_2499295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_2499295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499295 prefixEnd_2499295 := by exact prefixLift 2499295
  have htrace : WordTrace (prefixWord ++ tailWord_2499295) baseStart_2499295 baseEnd_2499295 := by
    simpa [prefixWord, tailWord_2499295, baseEnd_2499295] using wordTrace_append hprefix tailTrace_2499295
  have hstable : (prefixWord ++ tailWord_2499295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499295).length < 2 ^ (prefixWord ++ tailWord_2499295).sum := by decide
  have hdescent : baseEnd_2499295 < baseStart_2499295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499312 : List Nat := [2, 1, 1, 1, 3, 1, 6, 3, 1, 3]
def baseStart_2499312 : Nat := 118140960795 + 2499312 * 2 ^ 59
def prefixEnd_2499312 : Nat := 4983230072969 + 3 ^ 40 * 2499312 * 2
def baseEnd_2499312 : Nat := 855565574366687109337253

theorem tailTrace_2499312 : CollatzResearch.WordTrace tailWord_2499312 prefixEnd_2499312 855565574366687109337253 := by
  unfold tailWord_2499312
  simp only [CollatzResearch.WordTrace]
  refine ⟨45578698760713473675782095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60771598347617964901042793 45578698760713473675782095)
  ·
    refine ⟨68368048141070210513673143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45578698760713473675782095 68368048141070210513673143)
    ·
      refine ⟨102552072211605315770509715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68368048141070210513673143 102552072211605315770509715)
      ·
        refine ⟨153828108317407973655764573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102552072211605315770509715 153828108317407973655764573)
        ·
          refine ⟨57685540619027990120911715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153828108317407973655764573 57685540619027990120911715)
          ·
            refine ⟨86528310928541985181367573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57685540619027990120911715 86528310928541985181367573)
            ·
              refine ⟨4056014574775405555376605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86528310928541985181367573 4056014574775405555376605)
              ·
                refine ⟨1521005465540777083266227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4056014574775405555376605 1521005465540777083266227)
                ·
                  refine ⟨2281508198311165624899341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521005465540777083266227 2281508198311165624899341)
                  ·
                    refine ⟨855565574366687109337253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2281508198311165624899341 855565574366687109337253)
                    ·
                      rfl

theorem cell22_2499312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3, 1, 3].length) (baseStart_2499312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499312 prefixEnd_2499312 := by exact prefixLift 2499312
  have htrace : WordTrace (prefixWord ++ tailWord_2499312) baseStart_2499312 baseEnd_2499312 := by
    simpa [prefixWord, tailWord_2499312, baseEnd_2499312] using wordTrace_append hprefix tailTrace_2499312
  have hstable : (prefixWord ++ tailWord_2499312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499312).length < 2 ^ (prefixWord ++ tailWord_2499312).sum := by decide
  have hdescent : baseEnd_2499312 < baseStart_2499312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499438 : List Nat := [4, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_2499438 : Nat := 118140960795 + 2499438 * 2 ^ 59
def prefixEnd_2499438 : Nat := 4983230072969 + 3 ^ 40 * 2499438 * 2
def baseEnd_2499438 : Nat := 285202902247221593562289

theorem tailTrace_2499438 : CollatzResearch.WordTrace tailWord_2499438 prefixEnd_2499438 285202902247221593562289 := by
  unfold tailWord_2499438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11395249139871308858831371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60774662079313647247100645 11395249139871308858831371)
  ·
    refine ⟨17092873709806963288247057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11395249139871308858831371 17092873709806963288247057)
    ·
      refine ⟨12819655282355222466185293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17092873709806963288247057 12819655282355222466185293)
      ·
        refine ⟨4807370730883208424819485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12819655282355222466185293 4807370730883208424819485)
        ·
          refine ⟨1802764024081203159307307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4807370730883208424819485 1802764024081203159307307)
          ·
            refine ⟨2704146036121804738960961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802764024081203159307307 2704146036121804738960961)
            ·
              refine ⟨2028109527091353554220721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704146036121804738960961 2028109527091353554220721)
              ·
                refine ⟨1521082145318515165665541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2028109527091353554220721 1521082145318515165665541)
                ·
                  refine ⟨285202902247221593562289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1521082145318515165665541 285202902247221593562289)
                  ·
                    rfl

theorem cell22_2499438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_2499438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499438 prefixEnd_2499438 := by exact prefixLift 2499438
  have htrace : WordTrace (prefixWord ++ tailWord_2499438) baseStart_2499438 baseEnd_2499438 := by
    simpa [prefixWord, tailWord_2499438, baseEnd_2499438] using wordTrace_append hprefix tailTrace_2499438
  have hstable : (prefixWord ++ tailWord_2499438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499438).length < 2 ^ (prefixWord ++ tailWord_2499438).sum := by decide
  have hdescent : baseEnd_2499438 < baseStart_2499438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499443 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 7]
def baseStart_2499443 : Nat := 118140960795 + 2499443 * 2 ^ 59
def prefixEnd_2499443 : Nat := 4983230072969 + 3 ^ 40 * 2499443 * 2
def baseEnd_2499443 : Nat := 285203472781282144770617

theorem tailTrace_2499443 : CollatzResearch.WordTrace tailWord_2499443 prefixEnd_2499443 285203472781282144770617 := by
  unfold tailWord_2499443
  simp only [CollatzResearch.WordTrace]
  refine ⟨91162175483952356724582983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60774783655968237816388655 91162175483952356724582983)
  ·
    refine ⟨136743263225928535086874475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91162175483952356724582983 136743263225928535086874475)
    ·
      refine ⟨205114894838892802630311713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136743263225928535086874475 205114894838892802630311713)
      ·
        refine ⟨153836171129169601972733785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205114894838892802630311713 153836171129169601972733785)
        ·
          refine ⟨115377128346877201479550339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153836171129169601972733785 115377128346877201479550339)
          ·
            refine ⟨173065692520315802219325509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115377128346877201479550339 173065692520315802219325509)
            ·
              refine ⟨32449817347559212916123533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173065692520315802219325509 32449817347559212916123533)
              ·
                refine ⟨12168681505334704843546325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32449817347559212916123533 12168681505334704843546325)
                ·
                  refine ⟨285203472781282144770617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12168681505334704843546325 285203472781282144770617)
                  ·
                    rfl

theorem cell22_2499443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 7].length) (baseStart_2499443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499443 prefixEnd_2499443 := by exact prefixLift 2499443
  have htrace : WordTrace (prefixWord ++ tailWord_2499443) baseStart_2499443 baseEnd_2499443 := by
    simpa [prefixWord, tailWord_2499443, baseEnd_2499443] using wordTrace_append hprefix tailTrace_2499443
  have hstable : (prefixWord ++ tailWord_2499443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499443).length < 2 ^ (prefixWord ++ tailWord_2499443).sum := by decide
  have hdescent : baseEnd_2499443 < baseStart_2499443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499445 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2499445 : Nat := 118140960795 + 2499445 * 2 ^ 59
def prefixEnd_2499445 : Nat := 4983230072969 + 3 ^ 40 * 2499445 * 2
def baseEnd_2499445 : Nat := 855611102984719095761845

theorem tailTrace_2499445 : CollatzResearch.WordTrace tailWord_2499445 prefixEnd_2499445 855611102984719095761845 := by
  unfold tailWord_2499445
  simp only [CollatzResearch.WordTrace]
  refine ⟨91162248429945111066155789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60774832286630074044103859 91162248429945111066155789)
  ·
    refine ⟨34185843161229416649808421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91162248429945111066155789 34185843161229416649808421)
    ·
      refine ⟨6409845592730515621839079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34185843161229416649808421 6409845592730515621839079)
      ·
        refine ⟨9614768389095773432758619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6409845592730515621839079 9614768389095773432758619)
        ·
          refine ⟨14422152583643660149137929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9614768389095773432758619 14422152583643660149137929)
          ·
            refine ⟨10816614437732745111853447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14422152583643660149137929 10816614437732745111853447)
            ·
              refine ⟨16224921656599117667780171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10816614437732745111853447 16224921656599117667780171)
              ·
                refine ⟨24337382484898676501670257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16224921656599117667780171 24337382484898676501670257)
                ·
                  refine ⟨18253036863674007376252693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24337382484898676501670257 18253036863674007376252693)
                  ·
                    refine ⟨855611102984719095761845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18253036863674007376252693 855611102984719095761845)
                    ·
                      rfl

theorem cell22_2499445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2499445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499445 prefixEnd_2499445 := by exact prefixLift 2499445
  have htrace : WordTrace (prefixWord ++ tailWord_2499445) baseStart_2499445 baseEnd_2499445 := by
    simpa [prefixWord, tailWord_2499445, baseEnd_2499445] using wordTrace_append hprefix tailTrace_2499445
  have hstable : (prefixWord ++ tailWord_2499445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499445).length < 2 ^ (prefixWord ++ tailWord_2499445).sum := by decide
  have hdescent : baseEnd_2499445 < baseStart_2499445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499535 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 1, 6]
def baseStart_2499535 : Nat := 118140960795 + 2499535 * 2 ^ 59
def prefixEnd_2499535 : Nat := 4983230072969 + 3 ^ 40 * 2499535 * 2
def baseEnd_2499535 : Nat := 855641911823988861011569

theorem tailTrace_2499535 : CollatzResearch.WordTrace tailWord_2499535 prefixEnd_2499535 855641911823988861011569 := by
  unfold tailWord_2499535
  simp only [CollatzResearch.WordTrace]
  refine ⟨91165530999619056436932059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60777020666412704291288039 91165530999619056436932059)
  ·
    refine ⟨136748296499428584655398089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91165530999619056436932059 136748296499428584655398089)
    ·
      refine ⟨102561222374571438491548567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136748296499428584655398089 102561222374571438491548567)
      ·
        refine ⟨153841833561857157737322851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102561222374571438491548567 153841833561857157737322851)
        ·
          refine ⟨230762750342785736605984277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153841833561857157737322851 230762750342785736605984277)
          ·
            refine ⟨10817003922318081403405513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 230762750342785736605984277 10817003922318081403405513)
            ·
              refine ⟨8112752941738561052554135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10817003922318081403405513 8112752941738561052554135)
              ·
                refine ⟨12169129412607841578831203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8112752941738561052554135 12169129412607841578831203)
                ·
                  refine ⟨18253694118911762368246805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12169129412607841578831203 18253694118911762368246805)
                  ·
                    refine ⟨855641911823988861011569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18253694118911762368246805 855641911823988861011569)
                    ·
                      rfl

theorem cell22_2499535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_2499535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499535 prefixEnd_2499535 := by exact prefixLift 2499535
  have htrace : WordTrace (prefixWord ++ tailWord_2499535) baseStart_2499535 baseEnd_2499535 := by
    simpa [prefixWord, tailWord_2499535, baseEnd_2499535] using wordTrace_append hprefix tailTrace_2499535
  have hstable : (prefixWord ++ tailWord_2499535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499535).length < 2 ^ (prefixWord ++ tailWord_2499535).sum := by decide
  have hdescent : baseEnd_2499535 < baseStart_2499535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499642 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_2499642 : Nat := 118140960795 + 2499642 * 2 ^ 59
def prefixEnd_2499642 : Nat := 4983230072969 + 3 ^ 40 * 2499642 * 2
def baseEnd_2499642 : Nat := 855678540110676248586241

theorem tailTrace_2499642 : CollatzResearch.WordTrace tailWord_2499642 prefixEnd_2499642 855678540110676248586241 := by
  unfold tailWord_2499642
  simp only [CollatzResearch.WordTrace]
  refine ⟨22792358402557853427769295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60779622406820942474051453 22792358402557853427769295)
  ·
    refine ⟨34188537603836780141653943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22792358402557853427769295 34188537603836780141653943)
    ·
      refine ⟨51282806405755170212480915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34188537603836780141653943 51282806405755170212480915)
      ·
        refine ⟨76924209608632755318721373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51282806405755170212480915 76924209608632755318721373)
        ·
          refine ⟨28846578603237283244520515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76924209608632755318721373 28846578603237283244520515)
          ·
            refine ⟨43269867904855924866780773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28846578603237283244520515 43269867904855924866780773)
            ·
              refine ⟨8113100232160485912521395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43269867904855924866780773 8113100232160485912521395)
              ·
                refine ⟨12169650348240728868782093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8113100232160485912521395 12169650348240728868782093)
                ·
                  refine ⟨4563618880590273325793285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12169650348240728868782093 4563618880590273325793285)
                  ·
                    refine ⟨855678540110676248586241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4563618880590273325793285 855678540110676248586241)
                    ·
                      rfl

theorem cell22_2499642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_2499642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499642 prefixEnd_2499642 := by exact prefixLift 2499642
  have htrace : WordTrace (prefixWord ++ tailWord_2499642) baseStart_2499642 baseEnd_2499642 := by
    simpa [prefixWord, tailWord_2499642, baseEnd_2499642] using wordTrace_append hprefix tailTrace_2499642
  have hstable : (prefixWord ++ tailWord_2499642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499642).length < 2 ^ (prefixWord ++ tailWord_2499642).sum := by decide
  have hdescent : baseEnd_2499642 < baseStart_2499642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499687 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2499687 : Nat := 118140960795 + 2499687 * 2 ^ 59
def prefixEnd_2499687 : Nat := 4983230072969 + 3 ^ 40 * 2499687 * 2
def baseEnd_2499687 : Nat := 855693944530311131211103

theorem tailTrace_2499687 : CollatzResearch.WordTrace tailWord_2499687 prefixEnd_2499687 855693944530311131211103 := by
  unfold tailWord_2499687
  simp only [CollatzResearch.WordTrace]
  refine ⟨91171074895068386396465315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60780716596712257597643543 91171074895068386396465315)
  ·
    refine ⟨136756612342602579594697973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91171074895068386396465315 136756612342602579594697973)
    ·
      refine ⟨12820932407118991837002935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136756612342602579594697973 12820932407118991837002935)
      ·
        refine ⟨19231398610678487755504403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12820932407118991837002935 19231398610678487755504403)
        ·
          refine ⟨28847097916017731633256605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19231398610678487755504403 28847097916017731633256605)
          ·
            refine ⟨10817661718506649362471227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28847097916017731633256605 10817661718506649362471227)
            ·
              refine ⟨16226492577759974043706841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10817661718506649362471227 16226492577759974043706841)
              ·
                refine ⟨12169869433319980532780131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16226492577759974043706841 12169869433319980532780131)
                ·
                  refine ⟨18254804149979970799170197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12169869433319980532780131 18254804149979970799170197)
                  ·
                    refine ⟨855693944530311131211103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18254804149979970799170197 855693944530311131211103)
                    ·
                      rfl

theorem cell22_2499687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2499687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499687 prefixEnd_2499687 := by exact prefixLift 2499687
  have htrace : WordTrace (prefixWord ++ tailWord_2499687) baseStart_2499687 baseEnd_2499687 := by
    simpa [prefixWord, tailWord_2499687, baseEnd_2499687] using wordTrace_append hprefix tailTrace_2499687
  have hstable : (prefixWord ++ tailWord_2499687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499687).length < 2 ^ (prefixWord ++ tailWord_2499687).sum := by decide
  have hdescent : baseEnd_2499687 < baseStart_2499687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499689 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 1, 5]
def baseStart_2499689 : Nat := 118140960795 + 2499689 * 2 ^ 59
def prefixEnd_2499689 : Nat := 4983230072969 + 3 ^ 40 * 2499689 * 2
def baseEnd_2499689 : Nat := 855694629171183792661097

theorem tailTrace_2499689 : CollatzResearch.WordTrace tailWord_2499689 prefixEnd_2499689 855694629171183792661097 := by
  unfold tailWord_2499689
  simp only [CollatzResearch.WordTrace]
  refine ⟨91171147841061140738038121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60780765227374093825358747 91171147841061140738038121)
  ·
    refine ⟨68378360880795855553528591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91171147841061140738038121 68378360880795855553528591)
    ·
      refine ⟨102567541321193783330292887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68378360880795855553528591 102567541321193783330292887)
      ·
        refine ⟨153851311981790674995439331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102567541321193783330292887 153851311981790674995439331)
        ·
          refine ⟨230776967972686012493158997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153851311981790674995439331 230776967972686012493158997)
          ·
            refine ⟨2704417593429914208904207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 230776967972686012493158997 2704417593429914208904207)
            ·
              refine ⟨4056626390144871313356311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704417593429914208904207 4056626390144871313356311)
              ·
                refine ⟨6084939585217306970034467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056626390144871313356311 6084939585217306970034467)
                ·
                  refine ⟨9127409377825960455051701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6084939585217306970034467 9127409377825960455051701)
                  ·
                    refine ⟨855694629171183792661097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9127409377825960455051701 855694629171183792661097)
                    ·
                      rfl

theorem cell22_2499689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 5].length) (baseStart_2499689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499689 prefixEnd_2499689 := by exact prefixLift 2499689
  have htrace : WordTrace (prefixWord ++ tailWord_2499689) baseStart_2499689 baseEnd_2499689 := by
    simpa [prefixWord, tailWord_2499689, baseEnd_2499689] using wordTrace_append hprefix tailTrace_2499689
  have hstable : (prefixWord ++ tailWord_2499689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499689).length < 2 ^ (prefixWord ++ tailWord_2499689).sum := by decide
  have hdescent : baseEnd_2499689 < baseStart_2499689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499794 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2499794 : Nat := 118140960795 + 2499794 * 2 ^ 59
def prefixEnd_2499794 : Nat := 4983230072969 + 3 ^ 40 * 2499794 * 2
def baseEnd_2499794 : Nat := 855730572816998518785775

theorem tailTrace_2499794 : CollatzResearch.WordTrace tailWord_2499794 prefixEnd_2499794 855730572816998518785775 := by
  unfold tailWord_2499794
  simp only [CollatzResearch.WordTrace]
  refine ⟨22793744376420185917652609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60783318337120495780406957 22793744376420185917652609)
  ·
    refine ⟨17095308282315139438239457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22793744376420185917652609 17095308282315139438239457)
    ·
      refine ⟨12821481211736354578679593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17095308282315139438239457 12821481211736354578679593)
      ·
        refine ⟨9616110908802265934009695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12821481211736354578679593 9616110908802265934009695)
        ·
          refine ⟨14424166363203398901014543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9616110908802265934009695 14424166363203398901014543)
          ·
            refine ⟨21636249544805098351521815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14424166363203398901014543 21636249544805098351521815)
            ·
              refine ⟨32454374317207647527282723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21636249544805098351521815 32454374317207647527282723)
              ·
                refine ⟨48681561475811471290924085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32454374317207647527282723 48681561475811471290924085)
                ·
                  refine ⟨4563896388357325433524133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48681561475811471290924085 4563896388357325433524133)
                  ·
                    refine ⟨855730572816998518785775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4563896388357325433524133 855730572816998518785775)
                    ·
                      rfl

theorem cell22_2499794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2499794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499794 prefixEnd_2499794 := by exact prefixLift 2499794
  have htrace : WordTrace (prefixWord ++ tailWord_2499794) baseStart_2499794 baseEnd_2499794 := by
    simpa [prefixWord, tailWord_2499794, baseEnd_2499794] using wordTrace_append hprefix tailTrace_2499794
  have hstable : (prefixWord ++ tailWord_2499794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499794).length < 2 ^ (prefixWord ++ tailWord_2499794).sum := by decide
  have hdescent : baseEnd_2499794 < baseStart_2499794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499809 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 6]
def baseStart_2499809 : Nat := 118140960795 + 2499809 * 2 ^ 59
def prefixEnd_2499809 : Nat := 4983230072969 + 3 ^ 40 * 2499809 * 2
def baseEnd_2499809 : Nat := 285245235874514493220243

theorem tailTrace_2499809 : CollatzResearch.WordTrace tailWord_2499809 prefixEnd_2499809 285245235874514493220243 := by
  unfold tailWord_2499809
  simp only [CollatzResearch.WordTrace]
  refine ⟨91175524600626401232406481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60783683067084267488270987 91175524600626401232406481)
  ·
    refine ⟨68381643450469800924304861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91175524600626401232406481 68381643450469800924304861)
    ·
      refine ⟨25643116293926175346614323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68381643450469800924304861 25643116293926175346614323)
      ·
        refine ⟨38464674440889263019921485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25643116293926175346614323 38464674440889263019921485)
        ·
          refine ⟨14424252915333473632470557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38464674440889263019921485 14424252915333473632470557)
          ·
            refine ⟨5409094843250052612176459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14424252915333473632470557 5409094843250052612176459)
            ·
              refine ⟨8113642264875078918264689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5409094843250052612176459 8113642264875078918264689)
              ·
                refine ⟨6085231698656309188698517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8113642264875078918264689 6085231698656309188698517)
                ·
                  refine ⟨285245235874514493220243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6085231698656309188698517 285245235874514493220243)
                  ·
                    rfl

theorem cell22_2499809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_2499809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499809 prefixEnd_2499809 := by exact prefixLift 2499809
  have htrace : WordTrace (prefixWord ++ tailWord_2499809) baseStart_2499809 baseEnd_2499809 := by
    simpa [prefixWord, tailWord_2499809, baseEnd_2499809] using wordTrace_append hprefix tailTrace_2499809
  have hstable : (prefixWord ++ tailWord_2499809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499809).length < 2 ^ (prefixWord ++ tailWord_2499809).sum := by decide
  have hdescent : baseEnd_2499809 < baseStart_2499809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499841 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2499841 : Nat := 118140960795 + 2499841 * 2 ^ 59
def prefixEnd_2499841 : Nat := 4983230072969 + 3 ^ 40 * 2499841 * 2
def baseEnd_2499841 : Nat := 855746661877506062860631

theorem tailTrace_2499841 : CollatzResearch.WordTrace tailWord_2499841 prefixEnd_2499841 855746661877506062860631 := by
  unfold tailWord_2499841
  simp only [CollatzResearch.WordTrace]
  refine ⟨91176691736510470697571377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60784461157673647131714251 91176691736510470697571377)
  ·
    refine ⟨68382518802382853023178533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91176691736510470697571377 68382518802382853023178533)
    ·
      refine ⟨12821722275446784941845975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68382518802382853023178533 12821722275446784941845975)
      ·
        refine ⟨19232583413170177412768963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12821722275446784941845975 19232583413170177412768963)
        ·
          refine ⟨28848875119755266119153445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19232583413170177412768963 28848875119755266119153445)
          ·
            refine ⟨5409164084954112397341271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28848875119755266119153445 5409164084954112397341271)
            ·
              refine ⟨8113746127431168596011907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5409164084954112397341271 8113746127431168596011907)
              ·
                refine ⟨12170619191146752894017861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8113746127431168596011907 12170619191146752894017861)
                ·
                  refine ⟨2281991098340016167628349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12170619191146752894017861 2281991098340016167628349)
                  ·
                    refine ⟨855746661877506062860631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2281991098340016167628349 855746661877506062860631)
                    ·
                      rfl

theorem cell22_2499841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2499841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499841 prefixEnd_2499841 := by exact prefixLift 2499841
  have htrace : WordTrace (prefixWord ++ tailWord_2499841) baseStart_2499841 baseEnd_2499841 := by
    simpa [prefixWord, tailWord_2499841, baseEnd_2499841] using wordTrace_append hprefix tailTrace_2499841
  have hstable : (prefixWord ++ tailWord_2499841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499841).length < 2 ^ (prefixWord ++ tailWord_2499841).sum := by decide
  have hdescent : baseEnd_2499841 < baseStart_2499841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499903 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 3, 3]
def baseStart_2499903 : Nat := 118140960795 + 2499903 * 2 ^ 59
def prefixEnd_2499903 : Nat := 4983230072969 + 3 ^ 40 * 2499903 * 2
def baseEnd_2499903 : Nat := 855767885744558567810441

theorem tailTrace_2499903 : CollatzResearch.WordTrace tailWord_2499903 prefixEnd_2499903 855767885744558567810441 := by
  unfold tailWord_2499903
  simp only [CollatzResearch.WordTrace]
  refine ⟨91178953062285855286328363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60785968708190570190885575 91178953062285855286328363)
  ·
    refine ⟨136768429593428782929492545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91178953062285855286328363 136768429593428782929492545)
    ·
      refine ⟨102576322195071587197119409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136768429593428782929492545 102576322195071587197119409)
      ·
        refine ⟨76932241646303690397839557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102576322195071587197119409 76932241646303690397839557)
        ·
          refine ⟨14424795308681941949594917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76932241646303690397839557 14424795308681941949594917)
          ·
            refine ⟨2704649120377864115549047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14424795308681941949594917 2704649120377864115549047)
            ·
              refine ⟨4056973680566796173323571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704649120377864115549047 4056973680566796173323571)
              ·
                refine ⟨6085460520850194259985357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056973680566796173323571 6085460520850194259985357)
                ·
                  refine ⟨2282047695318822847494509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6085460520850194259985357 2282047695318822847494509)
                  ·
                    refine ⟨855767885744558567810441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2282047695318822847494509 855767885744558567810441)
                    ·
                      rfl

theorem cell22_2499903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_2499903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499903 prefixEnd_2499903 := by exact prefixLift 2499903
  have htrace : WordTrace (prefixWord ++ tailWord_2499903) baseStart_2499903 baseEnd_2499903 := by
    simpa [prefixWord, tailWord_2499903, baseEnd_2499903] using wordTrace_append hprefix tailTrace_2499903
  have hstable : (prefixWord ++ tailWord_2499903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499903).length < 2 ^ (prefixWord ++ tailWord_2499903).sum := by decide
  have hdescent : baseEnd_2499903 < baseStart_2499903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499914 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_2499914 : Nat := 118140960795 + 2499914 * 2 ^ 59
def prefixEnd_2499914 : Nat := 4983230072969 + 3 ^ 40 * 2499914 * 2
def baseEnd_2499914 : Nat := 855771651269358205785407

theorem tailTrace_2499914 : CollatzResearch.WordTrace tailWord_2499914 prefixEnd_2499914 855771651269358205785407 := by
  unfold tailWord_2499914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22794838566311501041244699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60786236176830669443319197 22794838566311501041244699)
  ·
    refine ⟨34192257849467251561867049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22794838566311501041244699 34192257849467251561867049)
    ·
      refine ⟨25644193387100438671400287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34192257849467251561867049 25644193387100438671400287)
      ·
        refine ⟨38466290080650658007100431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25644193387100438671400287 38466290080650658007100431)
        ·
          refine ⟨57699435120975987010650647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38466290080650658007100431 57699435120975987010650647)
          ·
            refine ⟨86549152681463980515975971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57699435120975987010650647 86549152681463980515975971)
            ·
              refine ⟨129823729022195970773963957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86549152681463980515975971 129823729022195970773963957)
              ·
                refine ⟨12170974595830872260059121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129823729022195970773963957 12170974595830872260059121)
                ·
                  refine ⟨9128230946873154195044341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12170974595830872260059121 9128230946873154195044341)
                  ·
                    refine ⟨855771651269358205785407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9128230946873154195044341 855771651269358205785407)
                    ·
                      rfl

theorem cell22_2499914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_2499914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499914 prefixEnd_2499914 := by exact prefixLift 2499914
  have htrace : WordTrace (prefixWord ++ tailWord_2499914) baseStart_2499914 baseEnd_2499914 := by
    simpa [prefixWord, tailWord_2499914, baseEnd_2499914] using wordTrace_append hprefix tailTrace_2499914
  have hstable : (prefixWord ++ tailWord_2499914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499914).length < 2 ^ (prefixWord ++ tailWord_2499914).sum := by decide
  have hdescent : baseEnd_2499914 < baseStart_2499914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499916 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 5]
def baseStart_2499916 : Nat := 118140960795 + 2499916 * 2 ^ 59
def prefixEnd_2499916 : Nat := 4983230072969 + 3 ^ 40 * 2499916 * 2
def baseEnd_2499916 : Nat := 285257445303410289078467

theorem tailTrace_2499916 : CollatzResearch.WordTrace tailWord_2499916 prefixEnd_2499916 285257445303410289078467 := by
  unfold tailWord_2499916
  simp only [CollatzResearch.WordTrace]
  refine ⟨45589713605619379253275801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60786284807492505671034401 45589713605619379253275801)
  ·
    refine ⟨34192285204214534439956851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45589713605619379253275801 34192285204214534439956851)
    ·
      refine ⟨51288427806321801659935277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34192285204214534439956851 51288427806321801659935277)
      ·
        refine ⟨19233160427370675622475729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51288427806321801659935277 19233160427370675622475729)
        ·
          refine ⟨14424870320528006716856797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19233160427370675622475729 14424870320528006716856797)
          ·
            refine ⟨5409326370198002518821299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14424870320528006716856797 5409326370198002518821299)
            ·
              refine ⟨8113989555297003778231949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5409326370198002518821299 8113989555297003778231949)
              ·
                refine ⟨3042746083236376416836981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8113989555297003778231949 3042746083236376416836981)
                ·
                  refine ⟨285257445303410289078467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3042746083236376416836981 285257445303410289078467)
                  ·
                    rfl

theorem cell22_2499916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_2499916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499916 prefixEnd_2499916 := by exact prefixLift 2499916
  have htrace : WordTrace (prefixWord ++ tailWord_2499916) baseStart_2499916 baseEnd_2499916 := by
    simpa [prefixWord, tailWord_2499916, baseEnd_2499916] using wordTrace_append hprefix tailTrace_2499916
  have hstable : (prefixWord ++ tailWord_2499916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499916).length < 2 ^ (prefixWord ++ tailWord_2499916).sum := by decide
  have hdescent : baseEnd_2499916 < baseStart_2499916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499950 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_2499950 : Nat := 118140960795 + 2499950 * 2 ^ 59
def prefixEnd_2499950 : Nat := 4983230072969 + 3 ^ 40 * 2499950 * 2
def baseEnd_2499950 : Nat := 285261324935022037295099

theorem tailTrace_2499950 : CollatzResearch.WordTrace tailWord_2499950 prefixEnd_2499950 285261324935022037295099 := by
  unfold tailWord_2499950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11397583411639447789161163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60787111528743721542192869 11397583411639447789161163)
  ·
    refine ⟨17096375117459171683741745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11397583411639447789161163 17096375117459171683741745)
    ·
      refine ⟨12822281338094378762806309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17096375117459171683741745 12822281338094378762806309)
      ·
        refine ⟨2404177750892696018026183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12822281338094378762806309 2404177750892696018026183)
        ·
          refine ⟨3606266626339044027039275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404177750892696018026183 3606266626339044027039275)
          ·
            refine ⟨5409399939508566040558913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606266626339044027039275 5409399939508566040558913)
            ·
              refine ⟨4057049954631424530419185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5409399939508566040558913 4057049954631424530419185)
              ·
                refine ⟨3042787465973568397814389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4057049954631424530419185 3042787465973568397814389)
                ·
                  refine ⟨285261324935022037295099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3042787465973568397814389 285261324935022037295099)
                  ·
                    rfl

theorem cell22_2499950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_2499950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499950 prefixEnd_2499950 := by exact prefixLift 2499950
  have htrace : WordTrace (prefixWord ++ tailWord_2499950) baseStart_2499950 baseEnd_2499950 := by
    simpa [prefixWord, tailWord_2499950, baseEnd_2499950] using wordTrace_append hprefix tailTrace_2499950
  have hstable : (prefixWord ++ tailWord_2499950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499950).length < 2 ^ (prefixWord ++ tailWord_2499950).sum := by decide
  have hdescent : baseEnd_2499950 < baseStart_2499950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499959 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 3, 5]
def baseStart_2499959 : Nat := 118140960795 + 2499959 * 2 ^ 59
def prefixEnd_2499959 : Nat := 4983230072969 + 3 ^ 40 * 2499959 * 2
def baseEnd_2499959 : Nat := 855787055688993088410269

theorem tailTrace_2499959 : CollatzResearch.WordTrace tailWord_2499959 prefixEnd_2499959 855787055688993088410269 := by
  unfold tailWord_2499959
  simp only [CollatzResearch.WordTrace]
  refine ⟨91180995550082976850366931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60787330366721984566911287 91180995550082976850366931)
  ·
    refine ⟨136771493325124465275550397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91180995550082976850366931 136771493325124465275550397)
    ·
      refine ⟨51289309996921674478331399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136771493325124465275550397 51289309996921674478331399)
      ·
        refine ⟨76933964995382511717497099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51289309996921674478331399 76933964995382511717497099)
        ·
          refine ⟨115400947493073767576245649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76933964995382511717497099 115400947493073767576245649)
          ·
            refine ⟨86550710619805325682184237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115400947493073767576245649 86550710619805325682184237)
            ·
              refine ⟨32456516482426997130819089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86550710619805325682184237 32456516482426997130819089)
              ·
                refine ⟨24342387361820247848114317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32456516482426997130819089 24342387361820247848114317)
                ·
                  refine ⟨9128395260682592943042869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24342387361820247848114317 9128395260682592943042869)
                  ·
                    refine ⟨855787055688993088410269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9128395260682592943042869 855787055688993088410269)
                    ·
                      rfl

theorem cell22_2499959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_2499959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499959 prefixEnd_2499959 := by exact prefixLift 2499959
  have htrace : WordTrace (prefixWord ++ tailWord_2499959) baseStart_2499959 baseEnd_2499959 := by
    simpa [prefixWord, tailWord_2499959, baseEnd_2499959] using wordTrace_append hprefix tailTrace_2499959
  have hstable : (prefixWord ++ tailWord_2499959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499959).length < 2 ^ (prefixWord ++ tailWord_2499959).sum := by decide
  have hdescent : baseEnd_2499959 < baseStart_2499959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499976 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_2499976 : Nat := 118140960795 + 2499976 * 2 ^ 59
def prefixEnd_2499976 : Nat := 4983230072969 + 3 ^ 40 * 2499976 * 2
def baseEnd_2499976 : Nat := 855792875136410710735217

theorem tailTrace_2499976 : CollatzResearch.WordTrace tailWord_2499976 prefixEnd_2499976 855792875136410710735217 := by
  unfold tailWord_2499976
  simp only [CollatzResearch.WordTrace]
  refine ⟨45590807795510694376867891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60787743727347592502490521 45590807795510694376867891)
  ·
    refine ⟨68386211693266041565301837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45590807795510694376867891 68386211693266041565301837)
    ·
      refine ⟨25644829384974765586988189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68386211693266041565301837 25644829384974765586988189)
      ·
        refine ⟨9616811019365537095120571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25644829384974765586988189 9616811019365537095120571)
        ·
          refine ⟨14425216529048305642680857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9616811019365537095120571 14425216529048305642680857)
          ·
            refine ⟨10818912396786229232010643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14425216529048305642680857 10818912396786229232010643)
            ·
              refine ⟨16228368595179343848015965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10818912396786229232010643 16228368595179343848015965)
              ·
                refine ⟨6085638223192253943005987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16228368595179343848015965 6085638223192253943005987)
                ·
                  refine ⟨9128457334788380914508981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6085638223192253943005987 9128457334788380914508981)
                  ·
                    refine ⟨855792875136410710735217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9128457334788380914508981 855792875136410710735217)
                    ·
                      rfl

theorem cell22_2499976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_2499976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499976 prefixEnd_2499976 := by exact prefixLift 2499976
  have htrace : WordTrace (prefixWord ++ tailWord_2499976) baseStart_2499976 baseEnd_2499976 := by
    simpa [prefixWord, tailWord_2499976, baseEnd_2499976] using wordTrace_append hprefix tailTrace_2499976
  have hstable : (prefixWord ++ tailWord_2499976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499976).length < 2 ^ (prefixWord ++ tailWord_2499976).sum := by decide
  have hdescent : baseEnd_2499976 < baseStart_2499976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2499989 : List Nat := [1, 3, 2, 1, 1, 2, 2, 10]
def baseStart_2499989 : Nat := 118140960795 + 2499989 * 2 ^ 59
def prefixEnd_2499989 : Nat := 4983230072969 + 3 ^ 40 * 2499989 * 2
def baseEnd_2499989 : Nat := 95088591700231445573353

theorem tailTrace_2499989 : CollatzResearch.WordTrace tailWord_2499989 prefixEnd_2499989 95088591700231445573353 := by
  unfold tailWord_2499989
  simp only [CollatzResearch.WordTrace]
  refine ⟨91182089739974291973959021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60788059826649527982639347 91182089739974291973959021)
  ·
    refine ⟨34193283652490359490234633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91182089739974291973959021 34193283652490359490234633)
    ·
      refine ⟨25644962739367769617675975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34193283652490359490234633 25644962739367769617675975)
      ·
        refine ⟨38467444109051654426513963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25644962739367769617675975 38467444109051654426513963)
        ·
          refine ⟨57701166163577481639770945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38467444109051654426513963 57701166163577481639770945)
          ·
            refine ⟨43275874622683111229828209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57701166163577481639770945 43275874622683111229828209)
            ·
              refine ⟨32456905967012333422371157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43275874622683111229828209 32456905967012333422371157)
              ·
                refine ⟨95088591700231445573353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32456905967012333422371157 95088591700231445573353)
                ·
                  rfl

theorem cell22_2499989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 10].length) (baseStart_2499989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2499989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2499989 prefixEnd_2499989 := by exact prefixLift 2499989
  have htrace : WordTrace (prefixWord ++ tailWord_2499989) baseStart_2499989 baseEnd_2499989 := by
    simpa [prefixWord, tailWord_2499989, baseEnd_2499989] using wordTrace_append hprefix tailTrace_2499989
  have hstable : (prefixWord ++ tailWord_2499989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2499989).length < 2 ^ (prefixWord ++ tailWord_2499989).sum := by decide
  have hdescent : baseEnd_2499989 < baseStart_2499989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2499989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500019 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 1, 8]
def baseStart_2500019 : Nat := 118140960795 + 2500019 * 2 ^ 59
def prefixEnd_2500019 : Nat := 4983230072969 + 3 ^ 40 * 2500019 * 2
def baseEnd_2500019 : Nat := 855807594915172931910085

theorem tailTrace_2500019 : CollatzResearch.WordTrace tailWord_2500019 prefixEnd_2500019 855807594915172931910085 := by
  unfold tailWord_2500019
  simp only [CollatzResearch.WordTrace]
  refine ⟨91183183929865607097551111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60788789286577071398367407 91183183929865607097551111)
  ·
    refine ⟨136774775894798410646326667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91183183929865607097551111 136774775894798410646326667)
    ·
      refine ⟨205162163842197615969490001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136774775894798410646326667 205162163842197615969490001)
      ·
        refine ⟨153871622881648211977117501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205162163842197615969490001 153871622881648211977117501)
        ·
          refine ⟨57701858580618079491419063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153871622881648211977117501 57701858580618079491419063)
          ·
            refine ⟨86552787870927119237128595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57701858580618079491419063 86552787870927119237128595)
            ·
              refine ⟨129829181806390678855692893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86552787870927119237128595 129829181806390678855692893)
              ·
                refine ⟨48685943177396504570884835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129829181806390678855692893 48685943177396504570884835)
                ·
                  refine ⟨73028914766094756856327253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48685943177396504570884835 73028914766094756856327253)
                  ·
                    refine ⟨855807594915172931910085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73028914766094756856327253 855807594915172931910085)
                    ·
                      rfl

theorem cell22_2500019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_2500019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500019 prefixEnd_2500019 := by exact prefixLift 2500019
  have htrace : WordTrace (prefixWord ++ tailWord_2500019) baseStart_2500019 baseEnd_2500019 := by
    simpa [prefixWord, tailWord_2500019, baseEnd_2500019] using wordTrace_append hprefix tailTrace_2500019
  have hstable : (prefixWord ++ tailWord_2500019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500019).length < 2 ^ (prefixWord ++ tailWord_2500019).sum := by decide
  have hdescent : baseEnd_2500019 < baseStart_2500019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500072 : List Nat := [2, 1, 4, 1, 1, 2, 5, 2, 1, 3]
def baseStart_2500072 : Nat := 118140960795 + 2500072 * 2 ^ 59
def prefixEnd_2500072 : Nat := 4983230072969 + 3 ^ 40 * 2500072 * 2
def baseEnd_2500072 : Nat := 855825737898298460334923

theorem tailTrace_2500072 : CollatzResearch.WordTrace tailWord_2500072 prefixEnd_2500072 855825737898298460334923 := by
  unfold tailWord_2500072
  simp only [CollatzResearch.WordTrace]
  refine ⟨45592558499336798574615235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60790077999115731432820313 45592558499336798574615235)
  ·
    refine ⟨68388837749005197861922853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45592558499336798574615235 68388837749005197861922853)
    ·
      refine ⟨12822907077938474599110535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68388837749005197861922853 12822907077938474599110535)
      ·
        refine ⟨19234360616907711898665803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12822907077938474599110535 19234360616907711898665803)
        ·
          refine ⟨28851540925361567847998705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19234360616907711898665803 28851540925361567847998705)
          ·
            refine ⟨21638655694021175885999029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28851540925361567847998705 21638655694021175885999029)
            ·
              refine ⟨2028623971314485239312409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21638655694021175885999029 2028623971314485239312409)
              ·
                refine ⟨1521467978485863929484307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2028623971314485239312409 1521467978485863929484307)
                ·
                  refine ⟨2282201967728795894226461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521467978485863929484307 2282201967728795894226461)
                  ·
                    refine ⟨855825737898298460334923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2282201967728795894226461 855825737898298460334923)
                    ·
                      rfl

theorem cell22_2500072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_2500072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500072 prefixEnd_2500072 := by exact prefixLift 2500072
  have htrace : WordTrace (prefixWord ++ tailWord_2500072) baseStart_2500072 baseEnd_2500072 := by
    simpa [prefixWord, tailWord_2500072, baseEnd_2500072] using wordTrace_append hprefix tailTrace_2500072
  have hstable : (prefixWord ++ tailWord_2500072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500072).length < 2 ^ (prefixWord ++ tailWord_2500072).sum := by decide
  have hdescent : baseEnd_2500072 < baseStart_2500072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500085 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 5]
def baseStart_2500085 : Nat := 118140960795 + 2500085 * 2 ^ 59
def prefixEnd_2500085 : Nat := 4983230072969 + 3 ^ 40 * 2500085 * 2
def baseEnd_2500085 : Nat := 285276729354656919919961

theorem tailTrace_2500085 : CollatzResearch.WordTrace tailWord_2500085 prefixEnd_2500085 285276729354656919919961 := by
  unfold tailWord_2500085
  simp only [CollatzResearch.WordTrace]
  refine ⟨91185591147626500369453709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60790394098417666912969139 91185591147626500369453709)
  ·
    refine ⟨34194596680359937638545141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91185591147626500369453709 34194596680359937638545141)
    ·
      refine ⟨3205743438783744153613607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34194596680359937638545141 3205743438783744153613607)
      ·
        refine ⟨4808615158175616230420411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3205743438783744153613607 4808615158175616230420411)
        ·
          refine ⟨7212922737263424345630617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4808615158175616230420411 7212922737263424345630617)
          ·
            refine ⟨5409692052947568259222963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7212922737263424345630617 5409692052947568259222963)
            ·
              refine ⟨8114538079421352388834445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5409692052947568259222963 8114538079421352388834445)
              ·
                refine ⟨3042951779783007145812917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8114538079421352388834445 3042951779783007145812917)
                ·
                  refine ⟨285276729354656919919961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3042951779783007145812917 285276729354656919919961)
                  ·
                    rfl

theorem cell22_2500085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_2500085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500085 prefixEnd_2500085 := by exact prefixLift 2500085
  have htrace : WordTrace (prefixWord ++ tailWord_2500085) baseStart_2500085 baseEnd_2500085 := by
    simpa [prefixWord, tailWord_2500085, baseEnd_2500085] using wordTrace_append hprefix tailTrace_2500085
  have hstable : (prefixWord ++ tailWord_2500085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500085).length < 2 ^ (prefixWord ++ tailWord_2500085).sum := by decide
  have hdescent : baseEnd_2500085 < baseStart_2500085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500113 : List Nat := [1, 2, 2, 1, 1, 2, 4, 5, 4]
def baseStart_2500113 : Nat := 118140960795 + 2500113 * 2 ^ 59
def prefixEnd_2500113 : Nat := 4983230072969 + 3 ^ 40 * 2500113 * 2
def baseEnd_2500113 : Nat := 285279924345396006686599

theorem tailTrace_2500113 : CollatzResearch.WordTrace tailWord_2500113 prefixEnd_2500113 285279924345396006686599 := by
  unfold tailWord_2500113
  simp only [CollatzResearch.WordTrace]
  refine ⟨91186612391525061151472993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60791074927683374100981995 91186612391525061151472993)
  ·
    refine ⟨68389959293643795863604745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91186612391525061151472993 68389959293643795863604745)
    ·
      refine ⟨51292469470232846897703559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68389959293643795863604745 51292469470232846897703559)
      ·
        refine ⟨76938704205349270346555339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51292469470232846897703559 76938704205349270346555339)
        ·
          refine ⟨115408056308023905519833009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76938704205349270346555339 115408056308023905519833009)
          ·
            refine ⟨86556042231017929139874757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115408056308023905519833009 86556042231017929139874757)
            ·
              refine ⟨16229257918315861713726517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86556042231017929139874757 16229257918315861713726517)
              ·
                refine ⟨1521492929842112035661861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16229257918315861713726517 1521492929842112035661861)
                ·
                  refine ⟨285279924345396006686599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1521492929842112035661861 285279924345396006686599)
                  ·
                    rfl

theorem cell22_2500113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 4].length) (baseStart_2500113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500113 prefixEnd_2500113 := by exact prefixLift 2500113
  have htrace : WordTrace (prefixWord ++ tailWord_2500113) baseStart_2500113 baseEnd_2500113 := by
    simpa [prefixWord, tailWord_2500113, baseEnd_2500113] using wordTrace_append hprefix tailTrace_2500113
  have hstable : (prefixWord ++ tailWord_2500113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500113).length < 2 ^ (prefixWord ++ tailWord_2500113).sum := by decide
  have hdescent : baseEnd_2500113 < baseStart_2500113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500115 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 1, 4]
def baseStart_2500115 : Nat := 118140960795 + 2500115 * 2 ^ 59
def prefixEnd_2500115 : Nat := 4983230072969 + 3 ^ 40 * 2500115 * 2
def baseEnd_2500115 : Nat := 855840457677060681509791

theorem tailTrace_2500115 : CollatzResearch.WordTrace tailWord_2500115 prefixEnd_2500115 855840457677060681509791 := by
  unfold tailWord_2500115
  simp only [CollatzResearch.WordTrace]
  refine ⟨91186685337517815493045799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60791123558345210328697199 91186685337517815493045799)
  ·
    refine ⟨136780028006276723239568699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91186685337517815493045799 136780028006276723239568699)
    ·
      refine ⟨205170042009415084859353049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136780028006276723239568699 205170042009415084859353049)
      ·
        refine ⟨153877531507061313644514787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205170042009415084859353049 153877531507061313644514787)
        ·
          refine ⟨230816297260591970466772181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153877531507061313644514787 230816297260591970466772181)
          ·
            refine ⟨5409756967045124307814973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 230816297260591970466772181 5409756967045124307814973)
            ·
              refine ⟨2028658862641921615430615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5409756967045124307814973 2028658862641921615430615)
              ·
                refine ⟨3042988293962882423145923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028658862641921615430615 3042988293962882423145923)
                ·
                  refine ⟨4564482440944323634718885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3042988293962882423145923 4564482440944323634718885)
                  ·
                    refine ⟨855840457677060681509791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4564482440944323634718885 855840457677060681509791)
                    ·
                      rfl

theorem cell22_2500115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 4].length) (baseStart_2500115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500115 prefixEnd_2500115 := by exact prefixLift 2500115
  have htrace : WordTrace (prefixWord ++ tailWord_2500115) baseStart_2500115 baseEnd_2500115 := by
    simpa [prefixWord, tailWord_2500115, baseEnd_2500115] using wordTrace_append hprefix tailTrace_2500115
  have hstable : (prefixWord ++ tailWord_2500115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500115).length < 2 ^ (prefixWord ++ tailWord_2500115).sum := by decide
  have hdescent : baseEnd_2500115 < baseStart_2500115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500166 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2500166 : Nat := 118140960795 + 2500166 * 2 ^ 59
def prefixEnd_2500166 : Nat := 4983230072969 + 3 ^ 40 * 2500166 * 2
def baseEnd_2500166 : Nat := 855857916019313548484635

theorem tailTrace_2500166 : CollatzResearch.WordTrace tailWord_2500166 prefixEnd_2500166 855857916019313548484635 := by
  unfold tailWord_2500166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849642045635407850098511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60792363640222034135434901 2849642045635407850098511)
  ·
    refine ⟨4274463068453111775147767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2849642045635407850098511 4274463068453111775147767)
    ·
      refine ⟨6411694602679667662721651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4274463068453111775147767 6411694602679667662721651)
      ·
        refine ⟨9617541904019501494082477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6411694602679667662721651 9617541904019501494082477)
        ·
          refine ⟨3606578214007313060280929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9617541904019501494082477 3606578214007313060280929)
          ·
            refine ⟨2704933660505484795210697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3606578214007313060280929 2704933660505484795210697)
            ·
              refine ⟨2028700245379113596408023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704933660505484795210697 2028700245379113596408023)
              ·
                refine ⟨3043050368068670394612035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028700245379113596408023 3043050368068670394612035)
                ·
                  refine ⟨4564575552103005591918053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043050368068670394612035 4564575552103005591918053)
                  ·
                    refine ⟨855857916019313548484635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4564575552103005591918053 855857916019313548484635)
                    ·
                      rfl

theorem cell22_2500166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2500166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500166 prefixEnd_2500166 := by exact prefixLift 2500166
  have htrace : WordTrace (prefixWord ++ tailWord_2500166) baseStart_2500166 baseEnd_2500166 := by
    simpa [prefixWord, tailWord_2500166, baseEnd_2500166] using wordTrace_append hprefix tailTrace_2500166
  have hstable : (prefixWord ++ tailWord_2500166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500166).length < 2 ^ (prefixWord ++ tailWord_2500166).sum := by decide
  have hdescent : baseEnd_2500166 < baseStart_2500166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500254 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2500254 : Nat := 118140960795 + 2500254 * 2 ^ 59
def prefixEnd_2500254 : Nat := 4983230072969 + 3 ^ 40 * 2500254 * 2
def baseEnd_2500254 : Nat := 285296013405903550761455

theorem tailTrace_2500254 : CollatzResearch.WordTrace tailWord_2500254 prefixEnd_2500254 285296013405903550761455 := by
  unfold tailWord_2500254
  simp only [CollatzResearch.WordTrace]
  refine ⟨11398969385501780279044477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60794503389342828154903877 11398969385501780279044477)
  ·
    refine ⟨4274613519563167604641679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11398969385501780279044477 4274613519563167604641679)
    ·
      refine ⟨6411920279344751406962519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4274613519563167604641679 6411920279344751406962519)
      ·
        refine ⟨9617880419017127110443779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6411920279344751406962519 9617880419017127110443779)
        ·
          refine ⟨14426820628525690665665669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9617880419017127110443779 14426820628525690665665669)
          ·
            refine ⟨2705028867848566999812313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14426820628525690665665669 2705028867848566999812313)
            ·
              refine ⟨2028771650886425249859235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2705028867848566999812313 2028771650886425249859235)
              ·
                refine ⟨3043157476329637874788853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028771650886425249859235 3043157476329637874788853)
                ·
                  refine ⟨285296013405903550761455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3043157476329637874788853 285296013405903550761455)
                  ·
                    rfl

theorem cell22_2500254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2500254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500254 prefixEnd_2500254 := by exact prefixLift 2500254
  have htrace : WordTrace (prefixWord ++ tailWord_2500254) baseStart_2500254 baseEnd_2500254 := by
    simpa [prefixWord, tailWord_2500254, baseEnd_2500254] using wordTrace_append hprefix tailTrace_2500254
  have hstable : (prefixWord ++ tailWord_2500254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500254).length < 2 ^ (prefixWord ++ tailWord_2500254).sum := by decide
  have hdescent : baseEnd_2500254 < baseStart_2500254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500355 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 5]
def baseStart_2500355 : Nat := 118140960795 + 2500355 * 2 ^ 59
def prefixEnd_2500355 : Nat := 4983230072969 + 3 ^ 40 * 2500355 * 2
def baseEnd_2500355 : Nat := 285307538193926685169685

theorem tailTrace_2500355 : CollatzResearch.WordTrace tailWord_2500355 prefixEnd_2500355 285307538193926685169685 := by
  unfold tailWord_2500355
  simp only [CollatzResearch.WordTrace]
  refine ⟨91195438856648336481782519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60796959237765557654521679 91195438856648336481782519)
  ·
    refine ⟨136793158284972504722673779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91195438856648336481782519 136793158284972504722673779)
    ·
      refine ⟨205189737427458757084010669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136793158284972504722673779 205189737427458757084010669)
      ·
        refine ⟨76946151535297033906504001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205189737427458757084010669 76946151535297033906504001)
        ·
          refine ⟨57709613651472775429878001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76946151535297033906504001 57709613651472775429878001)
          ·
            refine ⟨43282210238604581572408501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57709613651472775429878001 43282210238604581572408501)
            ·
              refine ⟨4057707209869179522413297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43282210238604581572408501 4057707209869179522413297)
              ·
                refine ⟨3043280407401884641809973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4057707209869179522413297 3043280407401884641809973)
                ·
                  refine ⟨285307538193926685169685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3043280407401884641809973 285307538193926685169685)
                  ·
                    rfl

theorem cell22_2500355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 5].length) (baseStart_2500355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500355 prefixEnd_2500355 := by exact prefixLift 2500355
  have htrace : WordTrace (prefixWord ++ tailWord_2500355) baseStart_2500355 baseEnd_2500355 := by
    simpa [prefixWord, tailWord_2500355, baseEnd_2500355] using wordTrace_append hprefix tailTrace_2500355
  have hstable : (prefixWord ++ tailWord_2500355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500355).length < 2 ^ (prefixWord ++ tailWord_2500355).sum := by decide
  have hdescent : baseEnd_2500355 < baseStart_2500355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500359 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 3, 3]
def baseStart_2500359 : Nat := 118140960795 + 2500359 * 2 ^ 59
def prefixEnd_2500359 : Nat := 4983230072969 + 3 ^ 40 * 2500359 * 2
def baseEnd_2500359 : Nat := 855923983863525378409043

theorem tailTrace_2500359 : CollatzResearch.WordTrace tailWord_2500359 prefixEnd_2500359 855923983863525378409043 := by
  unfold tailWord_2500359
  simp only [CollatzResearch.WordTrace]
  refine ⟨91195584748633845164928131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60797056499089230109952087 91195584748633845164928131)
  ·
    refine ⟨136793377122950767747392197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91195584748633845164928131 136793377122950767747392197)
    ·
      refine ⟨25648758210553268952636037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136793377122950767747392197 25648758210553268952636037)
      ·
        refine ⟨4809142164478737928619257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25648758210553268952636037 4809142164478737928619257)
        ·
          refine ⟨3606856623359053446464443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4809142164478737928619257 3606856623359053446464443)
          ·
            refine ⟨5410284935038580169696665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606856623359053446464443 5410284935038580169696665)
            ·
              refine ⟨4057713701278935127272499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5410284935038580169696665 4057713701278935127272499)
              ·
                refine ⟨6086570551918402690908749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057713701278935127272499 6086570551918402690908749)
                ·
                  refine ⟨2282463956969401009090781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6086570551918402690908749 2282463956969401009090781)
                  ·
                    refine ⟨855923983863525378409043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2282463956969401009090781 855923983863525378409043)
                    ·
                      rfl

theorem cell22_2500359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_2500359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500359 prefixEnd_2500359 := by exact prefixLift 2500359
  have htrace : WordTrace (prefixWord ++ tailWord_2500359) baseStart_2500359 baseEnd_2500359 := by
    simpa [prefixWord, tailWord_2500359, baseEnd_2500359] using wordTrace_append hprefix tailTrace_2500359
  have hstable : (prefixWord ++ tailWord_2500359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500359).length < 2 ^ (prefixWord ++ tailWord_2500359).sum := by decide
  have hdescent : baseEnd_2500359 < baseStart_2500359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500365 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2500365 : Nat := 118140960795 + 2500365 * 2 ^ 59
def prefixEnd_2500365 : Nat := 4983230072969 + 3 ^ 40 * 2500365 * 2
def baseEnd_2500365 : Nat := 855926037786143362759025

theorem tailTrace_2500365 : CollatzResearch.WordTrace tailWord_2500365 prefixEnd_2500365 855926037786143362759025 := by
  unfold tailWord_2500365
  simp only [CollatzResearch.WordTrace]
  refine ⟨91195803586612108189646549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60797202391074738793097699 91195803586612108189646549)
  ·
    refine ⟨2137401646561221285694841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 91195803586612108189646549 2137401646561221285694841)
    ·
      refine ⟨1603051234920915964271131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2137401646561221285694841 1603051234920915964271131)
      ·
        refine ⟨2404576852381373946406697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603051234920915964271131 2404576852381373946406697)
        ·
          refine ⟨1803432639286030459805023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2404576852381373946406697 1803432639286030459805023)
          ·
            refine ⟨2705148958929045689707535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1803432639286030459805023 2705148958929045689707535)
            ·
              refine ⟨4057723438393568534561303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705148958929045689707535 4057723438393568534561303)
              ·
                refine ⟨6086585157590352801841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057723438393568534561303 6086585157590352801841955)
                ·
                  refine ⟨9129877736385529202762933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6086585157590352801841955 9129877736385529202762933)
                  ·
                    refine ⟨855926037786143362759025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9129877736385529202762933 855926037786143362759025)
                    ·
                      rfl

theorem cell22_2500365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2500365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500365 prefixEnd_2500365 := by exact prefixLift 2500365
  have htrace : WordTrace (prefixWord ++ tailWord_2500365) baseStart_2500365 baseEnd_2500365 := by
    simpa [prefixWord, tailWord_2500365, baseEnd_2500365] using wordTrace_append hprefix tailTrace_2500365
  have hstable : (prefixWord ++ tailWord_2500365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500365).length < 2 ^ (prefixWord ++ tailWord_2500365).sum := by decide
  have hdescent : baseEnd_2500365 < baseStart_2500365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500402 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_2500402 : Nat := 118140960795 + 2500402 * 2 ^ 59
def prefixEnd_2500402 : Nat := 4983230072969 + 3 ^ 40 * 2500402 * 2
def baseEnd_2500402 : Nat := 855938703642287599583911

theorem tailTrace_2500402 : CollatzResearch.WordTrace tailWord_2500402 prefixEnd_2500402 855938703642287599583911 := by
  unfold tailWord_2500402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22799288271869515877185865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60798102058318709005828973 22799288271869515877185865)
  ·
    refine ⟨17099466203902136907889399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22799288271869515877185865 17099466203902136907889399)
    ·
      refine ⟨25649199305853205361834099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17099466203902136907889399 25649199305853205361834099)
      ·
        refine ⟨38473798958779808042751149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25649199305853205361834099 38473798958779808042751149)
        ·
          refine ⟨14427674609542428016031681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38473798958779808042751149 14427674609542428016031681)
          ·
            refine ⟨10820755957156821012023761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14427674609542428016031681 10820755957156821012023761)
            ·
              refine ⟨8115566967867615759017821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10820755957156821012023761 8115566967867615759017821)
              ·
                refine ⟨3043337612950355909631683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8115566967867615759017821 3043337612950355909631683)
                ·
                  refine ⟨4565006419425533864447525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043337612950355909631683 4565006419425533864447525)
                  ·
                    refine ⟨855938703642287599583911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4565006419425533864447525 855938703642287599583911)
                    ·
                      rfl

theorem cell22_2500402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_2500402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500402 prefixEnd_2500402 := by exact prefixLift 2500402
  have htrace : WordTrace (prefixWord ++ tailWord_2500402) baseStart_2500402 baseEnd_2500402 := by
    simpa [prefixWord, tailWord_2500402, baseEnd_2500402] using wordTrace_append hprefix tailTrace_2500402
  have hstable : (prefixWord ++ tailWord_2500402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500402).length < 2 ^ (prefixWord ++ tailWord_2500402).sum := by decide
  have hdescent : baseEnd_2500402 < baseStart_2500402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500447 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 2, 4]
def baseStart_2500447 : Nat := 118140960795 + 2500447 * 2 ^ 59
def prefixEnd_2500447 : Nat := 4983230072969 + 3 ^ 40 * 2500447 * 2
def baseEnd_2500447 : Nat := 855954108061922482208773

theorem tailTrace_2500447 : CollatzResearch.WordTrace tailWord_2500447 prefixEnd_2500447 855954108061922482208773 := by
  unfold tailWord_2500447
  simp only [CollatzResearch.WordTrace]
  refine ⟨91198794372315036194131595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60799196248210024129421063 91198794372315036194131595)
  ·
    refine ⟨136798191558472554291197393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91198794372315036194131595 136798191558472554291197393)
    ·
      refine ⟨102598643668854415718398045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136798191558472554291197393 102598643668854415718398045)
      ·
        refine ⟨38474491375820405894399267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102598643668854415718398045 38474491375820405894399267)
        ·
          refine ⟨57711737063730608841598901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38474491375820405894399267 57711737063730608841598901)
          ·
            refine ⟨5410475349724744578899897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57711737063730608841598901 5410475349724744578899897)
            ·
              refine ⟨4057856512293558434174923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5410475349724744578899897 4057856512293558434174923)
              ·
                refine ⟨6086784768440337651262385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057856512293558434174923 6086784768440337651262385)
                ·
                  refine ⟨4565088576330253238446789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6086784768440337651262385 4565088576330253238446789)
                  ·
                    refine ⟨855954108061922482208773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4565088576330253238446789 855954108061922482208773)
                    ·
                      rfl

theorem cell22_2500447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_2500447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500447 prefixEnd_2500447 := by exact prefixLift 2500447
  have htrace : WordTrace (prefixWord ++ tailWord_2500447) baseStart_2500447 baseEnd_2500447 := by
    simpa [prefixWord, tailWord_2500447, baseEnd_2500447] using wordTrace_append hprefix tailTrace_2500447
  have hstable : (prefixWord ++ tailWord_2500447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500447).length < 2 ^ (prefixWord ++ tailWord_2500447).sum := by decide
  have hdescent : baseEnd_2500447 < baseStart_2500447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500477 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_2500477 : Nat := 118140960795 + 2500477 * 2 ^ 59
def prefixEnd_2500477 : Nat := 4983230072969 + 3 ^ 40 * 2500477 * 2
def baseEnd_2500477 : Nat := 855964377675012403958681

theorem tailTrace_2500477 : CollatzResearch.WordTrace tailWord_2500477 prefixEnd_2500477 855964377675012403958681 := by
  unfold tailWord_2500477
  simp only [CollatzResearch.WordTrace]
  refine ⟨91199888562206351317723685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60799925708137567545149123 91199888562206351317723685)
  ·
    refine ⟨17099979105413690872073191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91199888562206351317723685 17099979105413690872073191)
    ·
      refine ⟨25649968658120536308109787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17099979105413690872073191 25649968658120536308109787)
      ·
        refine ⟨38474952987180804462164681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25649968658120536308109787 38474952987180804462164681)
        ·
          refine ⟨28856214740385603346623511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38474952987180804462164681 28856214740385603346623511)
          ·
            refine ⟨43284322110578405019935267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28856214740385603346623511 43284322110578405019935267)
            ·
              refine ⟨64926483165867607529902901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43284322110578405019935267 64926483165867607529902901)
              ·
                refine ⟨6086857796800088205928397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64926483165867607529902901 6086857796800088205928397)
                ·
                  refine ⟨2282571673800033077223149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6086857796800088205928397 2282571673800033077223149)
                  ·
                    refine ⟨855964377675012403958681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2282571673800033077223149 855964377675012403958681)
                    ·
                      rfl

theorem cell22_2500477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_2500477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500477 prefixEnd_2500477 := by exact prefixLift 2500477
  have htrace : WordTrace (prefixWord ++ tailWord_2500477) baseStart_2500477 baseEnd_2500477 := by
    simpa [prefixWord, tailWord_2500477, baseEnd_2500477] using wordTrace_append hprefix tailTrace_2500477
  have hstable : (prefixWord ++ tailWord_2500477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500477).length < 2 ^ (prefixWord ++ tailWord_2500477).sum := by decide
  have hdescent : baseEnd_2500477 < baseStart_2500477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500552 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 6]
def baseStart_2500552 : Nat := 118140960795 + 2500552 * 2 ^ 59
def prefixEnd_2500552 : Nat := 4983230072969 + 3 ^ 40 * 2500552 * 2
def baseEnd_2500552 : Nat := 285330017235912402777817

theorem tailTrace_2500552 : CollatzResearch.WordTrace tailWord_2500552 prefixEnd_2500552 285330017235912402777817 := by
  unfold tailWord_2500552
  simp only [CollatzResearch.WordTrace]
  refine ⟨45601312018467319563351955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60801749357956426084469273 45601312018467319563351955)
  ·
    refine ⟨68401968027700979345027933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45601312018467319563351955 68401968027700979345027933)
    ·
      refine ⟨25650738010387867254385475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68401968027700979345027933 25650738010387867254385475)
      ·
        refine ⟨38476107015581800881578213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25650738010387867254385475 38476107015581800881578213)
        ·
          refine ⟨7214270065421587665295915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38476107015581800881578213 7214270065421587665295915)
          ·
            refine ⟨10821405098132381497943873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7214270065421587665295915 10821405098132381497943873)
            ·
              refine ⟨8116053823599286123457905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10821405098132381497943873 8116053823599286123457905)
              ·
                refine ⟨6087040367699464592593429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8116053823599286123457905 6087040367699464592593429)
                ·
                  refine ⟨285330017235912402777817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6087040367699464592593429 285330017235912402777817)
                  ·
                    rfl

theorem cell22_2500552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_2500552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500552 prefixEnd_2500552 := by exact prefixLift 2500552
  have htrace : WordTrace (prefixWord ++ tailWord_2500552) baseStart_2500552 baseEnd_2500552 := by
    simpa [prefixWord, tailWord_2500552, baseEnd_2500552] using wordTrace_append hprefix tailTrace_2500552
  have hstable : (prefixWord ++ tailWord_2500552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500552).length < 2 ^ (prefixWord ++ tailWord_2500552).sum := by decide
  have hdescent : baseEnd_2500552 < baseStart_2500552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500567 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 6, 3]
def baseStart_2500567 : Nat := 118140960795 + 2500567 * 2 ^ 59
def prefixEnd_2500567 : Nat := 4983230072969 + 3 ^ 40 * 2500567 * 2
def baseEnd_2500567 : Nat := 855995186514282169208405

theorem tailTrace_2500567 : CollatzResearch.WordTrace tailWord_2500567 prefixEnd_2500567 855995186514282169208405 := by
  unfold tailWord_2500567
  simp only [CollatzResearch.WordTrace]
  refine ⟨91203171131880296688499955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60802114087920197792333303 91203171131880296688499955)
  ·
    refine ⟨136804756697820445032749933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91203171131880296688499955 136804756697820445032749933)
    ·
      refine ⟨51301783761682666887281225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136804756697820445032749933 51301783761682666887281225)
      ·
        refine ⟨38476337821262000165460919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51301783761682666887281225 38476337821262000165460919)
        ·
          refine ⟨57714506731893000248191379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38476337821262000165460919 57714506731893000248191379)
          ·
            refine ⟨86571760097839500372287069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57714506731893000248191379 86571760097839500372287069)
            ·
              refine ⟨32464410036689812639607651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86571760097839500372287069 32464410036689812639607651)
              ·
                refine ⟨48696615055034718959411477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32464410036689812639607651 48696615055034718959411477)
                ·
                  refine ⟨2282653830704752451222413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48696615055034718959411477 2282653830704752451222413)
                  ·
                    refine ⟨855995186514282169208405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2282653830704752451222413 855995186514282169208405)
                    ·
                      rfl

theorem cell22_2500567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_2500567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500567 prefixEnd_2500567 := by exact prefixLift 2500567
  have htrace : WordTrace (prefixWord ++ tailWord_2500567) baseStart_2500567 baseEnd_2500567 := by
    simpa [prefixWord, tailWord_2500567, baseEnd_2500567] using wordTrace_append hprefix tailTrace_2500567
  have hstable : (prefixWord ++ tailWord_2500567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500567).length < 2 ^ (prefixWord ++ tailWord_2500567).sum := by decide
  have hdescent : baseEnd_2500567 < baseStart_2500567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500584 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 2, 3]
def baseStart_2500584 : Nat := 118140960795 + 2500584 * 2 ^ 59
def prefixEnd_2500584 : Nat := 4983230072969 + 3 ^ 40 * 2500584 * 2
def baseEnd_2500584 : Nat := 856001005961699791533353

theorem tailTrace_2500584 : CollatzResearch.WordTrace tailWord_2500584 prefixEnd_2500584 856001005961699791533353 := by
  unfold tailWord_2500584
  simp only [CollatzResearch.WordTrace]
  refine ⟨45601895586409354295934403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60802527448545805727912537 45601895586409354295934403)
  ·
    refine ⟨68402843379614031443901605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45601895586409354295934403 68402843379614031443901605)
    ·
      refine ⟨12825533133677630895731551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68402843379614031443901605 12825533133677630895731551)
      ·
        refine ⟨19238299700516446343597327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12825533133677630895731551 19238299700516446343597327)
        ·
          refine ⟨28857449550774669515395991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19238299700516446343597327 28857449550774669515395991)
          ·
            refine ⟨43286174326162004273093987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28857449550774669515395991 43286174326162004273093987)
            ·
              refine ⟨64929261489243006409640981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43286174326162004273093987 64929261489243006409640981)
              ·
                refine ⟨3043559132308265925451921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64929261489243006409640981 3043559132308265925451921)
                ·
                  refine ⟨2282669349231199444088941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3043559132308265925451921 2282669349231199444088941)
                  ·
                    refine ⟨856001005961699791533353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2282669349231199444088941 856001005961699791533353)
                    ·
                      rfl

theorem cell22_2500584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_2500584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500584 prefixEnd_2500584 := by exact prefixLift 2500584
  have htrace : WordTrace (prefixWord ++ tailWord_2500584) baseStart_2500584 baseEnd_2500584 := by
    simpa [prefixWord, tailWord_2500584, baseEnd_2500584] using wordTrace_append hprefix tailTrace_2500584
  have hstable : (prefixWord ++ tailWord_2500584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500584).length < 2 ^ (prefixWord ++ tailWord_2500584).sum := by decide
  have hdescent : baseEnd_2500584 < baseStart_2500584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500586 : List Nat := [3, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_2500586 : Nat := 118140960795 + 2500586 * 2 ^ 59
def prefixEnd_2500586 : Nat := 4983230072969 + 3 ^ 40 * 2500586 * 2
def baseEnd_2500586 : Nat := 285333896867524150994449

theorem tailTrace_2500586 : CollatzResearch.WordTrace tailWord_2500586 prefixEnd_2500586 285333896867524150994449 := by
  unfold tailWord_2500586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22800966029702865733360403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60802576079207641955627741 22800966029702865733360403)
  ·
    refine ⟨34201449044554298600040605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22800966029702865733360403 34201449044554298600040605)
    ·
      refine ⟨12825543391707861975015227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34201449044554298600040605 12825543391707861975015227)
      ·
        refine ⟨19238315087561792962522841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12825543391707861975015227 19238315087561792962522841)
        ·
          refine ⟨14428736315671344721892131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19238315087561792962522841 14428736315671344721892131)
          ·
            refine ⟨21643104473507017082838197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14428736315671344721892131 21643104473507017082838197)
            ·
              refine ⟨2029041044391282851516081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21643104473507017082838197 2029041044391282851516081)
              ·
                refine ⟨1521780783293462138637061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2029041044391282851516081 1521780783293462138637061)
                ·
                  refine ⟨285333896867524150994449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1521780783293462138637061 285333896867524150994449)
                  ·
                    rfl

theorem cell22_2500586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_2500586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500586 prefixEnd_2500586 := by exact prefixLift 2500586
  have htrace : WordTrace (prefixWord ++ tailWord_2500586) baseStart_2500586 baseEnd_2500586 := by
    simpa [prefixWord, tailWord_2500586, baseEnd_2500586] using wordTrace_append hprefix tailTrace_2500586
  have hstable : (prefixWord ++ tailWord_2500586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500586).length < 2 ^ (prefixWord ++ tailWord_2500586).sum := by decide
  have hdescent : baseEnd_2500586 < baseStart_2500586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500601 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 2, 3]
def baseStart_2500601 : Nat := 118140960795 + 2500601 * 2 ^ 59
def prefixEnd_2500601 : Nat := 4983230072969 + 3 ^ 40 * 2500601 * 2
def baseEnd_2500601 : Nat := 856006825409117413858301

theorem tailTrace_2500601 : CollatzResearch.WordTrace tailWord_2500601 prefixEnd_2500601 856006825409117413858301 := by
  unfold tailWord_2500601
  simp only [CollatzResearch.WordTrace]
  refine ⟨91204411213757120495237657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60802940809171413663491771 91204411213757120495237657)
  ·
    refine ⟨68403308410317840371428243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91204411213757120495237657 68403308410317840371428243)
    ·
      refine ⟨102604962615476760557142365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68403308410317840371428243 102604962615476760557142365)
      ·
        refine ⟨38476860980803785208928387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102604962615476760557142365 38476860980803785208928387)
        ·
          refine ⟨57715291471205677813392581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38476860980803785208928387 57715291471205677813392581)
          ·
            refine ⟨10821617150851064590011109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57715291471205677813392581 10821617150851064590011109)
            ·
              refine ⟨2029053215784574610627083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10821617150851064590011109 2029053215784574610627083)
              ·
                refine ⟨3043579823676861915940625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029053215784574610627083 3043579823676861915940625)
                ·
                  refine ⟨2282684867757646436955469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3043579823676861915940625 2282684867757646436955469)
                  ·
                    refine ⟨856006825409117413858301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2282684867757646436955469 856006825409117413858301)
                    ·
                      rfl

theorem cell22_2500601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 2, 3].length) (baseStart_2500601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500601 prefixEnd_2500601 := by exact prefixLift 2500601
  have htrace : WordTrace (prefixWord ++ tailWord_2500601) baseStart_2500601 baseEnd_2500601 := by
    simpa [prefixWord, tailWord_2500601, baseEnd_2500601] using wordTrace_append hprefix tailTrace_2500601
  have hstable : (prefixWord ++ tailWord_2500601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500601).length < 2 ^ (prefixWord ++ tailWord_2500601).sum := by decide
  have hdescent : baseEnd_2500601 < baseStart_2500601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500648 : List Nat := [2, 1, 5, 3, 2, 1, 1, 7]
def baseStart_2500648 : Nat := 118140960795 + 2500648 * 2 ^ 59
def prefixEnd_2500648 : Nat := 4983230072969 + 3 ^ 40 * 2500648 * 2
def baseEnd_2500648 : Nat := 95113657163291661992573

theorem tailTrace_2500648 : CollatzResearch.WordTrace tailWord_2500648 prefixEnd_2500648 95113657163291661992573 := by
  unfold tailWord_2500648
  simp only [CollatzResearch.WordTrace]
  refine ⟨45603062722293423761099299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60804083629724565014799065 45603062722293423761099299)
  ·
    refine ⟨68404594083440135641648949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45603062722293423761099299 68404594083440135641648949)
    ·
      refine ⟨6412930695322512716404589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68404594083440135641648949 6412930695322512716404589)
      ·
        refine ⟨2404849010745942268651721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6412930695322512716404589 2404849010745942268651721)
        ·
          refine ⟨1803636758059456701488791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2404849010745942268651721 1803636758059456701488791)
          ·
            refine ⟨2705455137089185052233187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1803636758059456701488791 2705455137089185052233187)
            ·
              refine ⟨4058182705633777578349781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705455137089185052233187 4058182705633777578349781)
              ·
                refine ⟨95113657163291661992573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4058182705633777578349781 95113657163291661992573)
                ·
                  rfl

theorem cell22_2500648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 7].length) (baseStart_2500648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500648 prefixEnd_2500648 := by exact prefixLift 2500648
  have htrace : WordTrace (prefixWord ++ tailWord_2500648) baseStart_2500648 baseEnd_2500648 := by
    simpa [prefixWord, tailWord_2500648, baseEnd_2500648] using wordTrace_append hprefix tailTrace_2500648
  have hstable : (prefixWord ++ tailWord_2500648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500648).length < 2 ^ (prefixWord ++ tailWord_2500648).sum := by decide
  have hdescent : baseEnd_2500648 < baseStart_2500648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500657 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_2500657 : Nat := 118140960795 + 2500657 * 2 ^ 59
def prefixEnd_2500657 : Nat := 4983230072969 + 3 ^ 40 * 2500657 * 2
def baseEnd_2500657 : Nat := 856025995353551934458129

theorem tailTrace_2500657 : CollatzResearch.WordTrace tailWord_2500657 prefixEnd_2500657 856025995353551934458129 := by
  unfold tailWord_2500657
  simp only [CollatzResearch.WordTrace]
  refine ⟨91206453701554242059276225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60804302467702828039517483 91206453701554242059276225)
  ·
    refine ⟨68404840276165681544457169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91206453701554242059276225 68404840276165681544457169)
    ·
      refine ⟨51303630207124261158342877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68404840276165681544457169 51303630207124261158342877)
      ·
        refine ⟨19238861327671597934378579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51303630207124261158342877 19238861327671597934378579)
        ·
          refine ⟨28858291991507396901567869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19238861327671597934378579 28858291991507396901567869)
          ·
            refine ⟨10821859496815273838087951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28858291991507396901567869 10821859496815273838087951)
            ·
              refine ⟨16232789245222910757131927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10821859496815273838087951 16232789245222910757131927)
              ·
                refine ⟨24349183867834366135697891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16232789245222910757131927 24349183867834366135697891)
                ·
                  refine ⟨36523775801751549203546837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24349183867834366135697891 36523775801751549203546837)
                  ·
                    refine ⟨856025995353551934458129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36523775801751549203546837 856025995353551934458129)
                    ·
                      rfl

theorem cell22_2500657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_2500657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500657 prefixEnd_2500657 := by exact prefixLift 2500657
  have htrace : WordTrace (prefixWord ++ tailWord_2500657) baseStart_2500657 baseEnd_2500657 := by
    simpa [prefixWord, tailWord_2500657, baseEnd_2500657] using wordTrace_append hprefix tailTrace_2500657
  have hstable : (prefixWord ++ tailWord_2500657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500657).length < 2 ^ (prefixWord ++ tailWord_2500657).sum := by decide
  have hdescent : baseEnd_2500657 < baseStart_2500657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500704 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 6]
def baseStart_2500704 : Nat := 118140960795 + 2500704 * 2 ^ 59
def prefixEnd_2500704 : Nat := 4983230072969 + 3 ^ 40 * 2500704 * 2
def baseEnd_2500704 : Nat := 285347361471353159510995

theorem tailTrace_2500704 : CollatzResearch.WordTrace tailWord_2500704 prefixEnd_2500704 285347361471353159510995 := by
  unfold tailWord_2500704
  simp only [CollatzResearch.WordTrace]
  refine ⟨45604083966191984543118583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60805445288255979390824777 45604083966191984543118583)
  ·
    refine ⟨68406125949287976814677875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45604083966191984543118583 68406125949287976814677875)
    ·
      refine ⟨102609188923931965222016813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68406125949287976814677875 102609188923931965222016813)
      ·
        refine ⟨38478445846474486958256305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102609188923931965222016813 38478445846474486958256305)
        ·
          refine ⟨28858834384855865218692229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38478445846474486958256305 28858834384855865218692229)
          ·
            refine ⟨5411031447160474728504793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28858834384855865218692229 5411031447160474728504793)
            ·
              refine ⟨4058273585370356046378595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5411031447160474728504793 4058273585370356046378595)
              ·
                refine ⟨6087410378055534069567893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058273585370356046378595 6087410378055534069567893)
                ·
                  refine ⟨285347361471353159510995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6087410378055534069567893 285347361471353159510995)
                  ·
                    rfl

theorem cell22_2500704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_2500704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500704 prefixEnd_2500704 := by exact prefixLift 2500704
  have htrace : WordTrace (prefixWord ++ tailWord_2500704) baseStart_2500704 baseEnd_2500704 := by
    simpa [prefixWord, tailWord_2500704, baseEnd_2500704] using wordTrace_append hprefix tailTrace_2500704
  have hstable : (prefixWord ++ tailWord_2500704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500704).length < 2 ^ (prefixWord ++ tailWord_2500704).sum := by decide
  have hdescent : baseEnd_2500704 < baseStart_2500704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500719 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 1, 5]
def baseStart_2500719 : Nat := 118140960795 + 2500719 * 2 ^ 59
def prefixEnd_2500719 : Nat := 4983230072969 + 3 ^ 40 * 2500719 * 2
def baseEnd_2500719 : Nat := 856047219220604439407939

theorem tailTrace_2500719 : CollatzResearch.WordTrace tailWord_2500719 prefixEnd_2500719 856047219220604439407939 := by
  unfold tailWord_2500719
  simp only [CollatzResearch.WordTrace]
  refine ⟨91208715027329626648033211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60805810018219751098688807 91208715027329626648033211)
  ·
    refine ⟨136813072540994439972049817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91208715027329626648033211 136813072540994439972049817)
    ·
      refine ⟨102609804405745829979037363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136813072540994439972049817 102609804405745829979037363)
      ·
        refine ⟨153914706608618744968556045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102609804405745829979037363 153914706608618744968556045)
        ·
          refine ⟨57718014978232029363208517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153914706608618744968556045 57718014978232029363208517)
          ·
            refine ⟨10822127808418505505601597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57718014978232029363208517 10822127808418505505601597)
            ·
              refine ⟨4058297928156939564600599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10822127808418505505601597 4058297928156939564600599)
              ·
                refine ⟨6087446892235409346900899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058297928156939564600599 6087446892235409346900899)
                ·
                  refine ⟨9131170338353114020351349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6087446892235409346900899 9131170338353114020351349)
                  ·
                    refine ⟨856047219220604439407939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9131170338353114020351349 856047219220604439407939)
                    ·
                      rfl

theorem cell22_2500719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_2500719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500719 prefixEnd_2500719 := by exact prefixLift 2500719
  have htrace : WordTrace (prefixWord ++ tailWord_2500719) baseStart_2500719 baseEnd_2500719 := by
    simpa [prefixWord, tailWord_2500719, baseEnd_2500719] using wordTrace_append hprefix tailTrace_2500719
  have hstable : (prefixWord ++ tailWord_2500719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500719).length < 2 ^ (prefixWord ++ tailWord_2500719).sum := by decide
  have hdescent : baseEnd_2500719 < baseStart_2500719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500770 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2500770 : Nat := 118140960795 + 2500770 * 2 ^ 59
def prefixEnd_2500770 : Nat := 4983230072969 + 3 ^ 40 * 2500770 * 2
def baseEnd_2500770 : Nat := 856064677562857306382783

theorem tailTrace_2500770 : CollatzResearch.WordTrace tailWord_2500770 prefixEnd_2500770 856064677562857306382783 := by
  unfold tailWord_2500770
  simp only [CollatzResearch.WordTrace]
  refine ⟨22802643787536215589534941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60807050100096574905426509 22802643787536215589534941)
  ·
    refine ⟨8550991420326080846075603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22802643787536215589534941 8550991420326080846075603)
    ·
      refine ⟨12826487130489121269113405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8550991420326080846075603 12826487130489121269113405)
      ·
        refine ⟨4809932673933420475917527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12826487130489121269113405 4809932673933420475917527)
        ·
          refine ⟨7214899010900130713876291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4809932673933420475917527 7214899010900130713876291)
          ·
            refine ⟨10822348516350196070814437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7214899010900130713876291 10822348516350196070814437)
            ·
              refine ⟨2029190346815661763277707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10822348516350196070814437 2029190346815661763277707)
              ·
                refine ⟨3043785520223492644916561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029190346815661763277707 3043785520223492644916561)
                ·
                  refine ⟨2282839140167619483687421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3043785520223492644916561 2282839140167619483687421)
                  ·
                    refine ⟨856064677562857306382783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2282839140167619483687421 856064677562857306382783)
                    ·
                      rfl

theorem cell22_2500770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2500770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500770 prefixEnd_2500770 := by exact prefixLift 2500770
  have htrace : WordTrace (prefixWord ++ tailWord_2500770) baseStart_2500770 baseEnd_2500770 := by
    simpa [prefixWord, tailWord_2500770, baseEnd_2500770] using wordTrace_append hprefix tailTrace_2500770
  have hstable : (prefixWord ++ tailWord_2500770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500770).length < 2 ^ (prefixWord ++ tailWord_2500770).sum := by decide
  have hdescent : baseEnd_2500770 < baseStart_2500770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500858 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_2500858 : Nat := 118140960795 + 2500858 * 2 ^ 59
def prefixEnd_2500858 : Nat := 4983230072969 + 3 ^ 40 * 2500858 * 2
def baseEnd_2500858 : Nat := 856094801761254410182513

theorem tailTrace_2500858 : CollatzResearch.WordTrace tailWord_2500858 prefixEnd_2500858 856094801761254410182513 := by
  unfold tailWord_2500858
  simp only [CollatzResearch.WordTrace]
  refine ⟨22803446193456513346835807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60809189849217368924895485 22803446193456513346835807)
  ·
    refine ⟨34205169290184770020253711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22803446193456513346835807 34205169290184770020253711)
    ·
      refine ⟨51307753935277155030380567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34205169290184770020253711 51307753935277155030380567)
      ·
        refine ⟨76961630902915732545570851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51307753935277155030380567 76961630902915732545570851)
        ·
          refine ⟨115442446354373598818356277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76961630902915732545570851 115442446354373598818356277)
          ·
            refine ⟨10822729345722524889220901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115442446354373598818356277 10822729345722524889220901)
            ·
              refine ⟨2029261752322973416728919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10822729345722524889220901 2029261752322973416728919)
              ·
                refine ⟨3043892628484460125093379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029261752322973416728919 3043892628484460125093379)
                ·
                  refine ⟨4565838942726690187640069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043892628484460125093379 4565838942726690187640069)
                  ·
                    refine ⟨856094801761254410182513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4565838942726690187640069 856094801761254410182513)
                    ·
                      rfl

theorem cell22_2500858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_2500858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500858 prefixEnd_2500858 := by exact prefixLift 2500858
  have htrace : WordTrace (prefixWord ++ tailWord_2500858) baseStart_2500858 baseEnd_2500858 := by
    simpa [prefixWord, tailWord_2500858, baseEnd_2500858] using wordTrace_append hprefix tailTrace_2500858
  have hstable : (prefixWord ++ tailWord_2500858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500858).length < 2 ^ (prefixWord ++ tailWord_2500858).sum := by decide
  have hdescent : baseEnd_2500858 < baseStart_2500858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500899 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 2, 7]
def baseStart_2500899 : Nat := 118140960795 + 2500899 * 2 ^ 59
def prefixEnd_2500899 : Nat := 4983230072969 + 3 ^ 40 * 2500899 * 2
def baseEnd_2500899 : Nat := 856108836899143969907387

theorem tailTrace_2500899 : CollatzResearch.WordTrace tailWord_2500899 prefixEnd_2500899 856108836899143969907387 := by
  unfold tailWord_2500899
  simp only [CollatzResearch.WordTrace]
  refine ⟨91215280166677517389585751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60810186777785011593057167 91215280166677517389585751)
  ·
    refine ⟨136822920250016276084378627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91215280166677517389585751 136822920250016276084378627)
    ·
      refine ⟨205234380375024414126567941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136822920250016276084378627 205234380375024414126567941)
      ·
        refine ⟨38481446320317077648731489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205234380375024414126567941 38481446320317077648731489)
        ·
          refine ⟨28861084740237808236548617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38481446320317077648731489 28861084740237808236548617)
          ·
            refine ⟨21645813555178356177411463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28861084740237808236548617 21645813555178356177411463)
            ·
              refine ⟨32468720332767534266117195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21645813555178356177411463 32468720332767534266117195)
              ·
                refine ⟨48703080499151301399175793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32468720332767534266117195 48703080499151301399175793)
                ·
                  refine ⟨36527310374363476049381845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48703080499151301399175793 36527310374363476049381845)
                  ·
                    refine ⟨856108836899143969907387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36527310374363476049381845 856108836899143969907387)
                    ·
                      rfl

theorem cell22_2500899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_2500899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500899 prefixEnd_2500899 := by exact prefixLift 2500899
  have htrace : WordTrace (prefixWord ++ tailWord_2500899) baseStart_2500899 baseEnd_2500899 := by
    simpa [prefixWord, tailWord_2500899, baseEnd_2500899] using wordTrace_append hprefix tailTrace_2500899
  have hstable : (prefixWord ++ tailWord_2500899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500899).length < 2 ^ (prefixWord ++ tailWord_2500899).sum := by decide
  have hdescent : baseEnd_2500899 < baseStart_2500899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500901 : List Nat := [1, 3, 1, 2, 5, 1, 1, 8]
def baseStart_2500901 : Nat := 118140960795 + 2500901 * 2 ^ 59
def prefixEnd_2500901 : Nat := 4983230072969 + 3 ^ 40 * 2500901 * 2
def baseEnd_2500901 : Nat := 95123280171112959039709

theorem tailTrace_2500901 : CollatzResearch.WordTrace tailWord_2500901 prefixEnd_2500901 95123280171112959039709 := by
  unfold tailWord_2500901
  simp only [CollatzResearch.WordTrace]
  refine ⟨91215353112670271731158557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60810235408446847820772371 91215353112670271731158557)
  ·
    refine ⟨34205757417251351899184459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91215353112670271731158557 34205757417251351899184459)
    ·
      refine ⟨51308636125877027848776689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34205757417251351899184459 51308636125877027848776689)
      ·
        refine ⟨38481477094407770886582517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51308636125877027848776689 38481477094407770886582517)
        ·
          refine ⟨3607638477600728520617111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38481477094407770886582517 3607638477600728520617111)
          ·
            refine ⟨5411457716401092780925667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607638477600728520617111 5411457716401092780925667)
            ·
              refine ⟨8117186574601639171388501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411457716401092780925667 8117186574601639171388501)
              ·
                refine ⟨95123280171112959039709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8117186574601639171388501 95123280171112959039709)
                ·
                  rfl

theorem cell22_2500901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 8].length) (baseStart_2500901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500901 prefixEnd_2500901 := by exact prefixLift 2500901
  have htrace : WordTrace (prefixWord ++ tailWord_2500901) baseStart_2500901 baseEnd_2500901 := by
    simpa [prefixWord, tailWord_2500901, baseEnd_2500901] using wordTrace_append hprefix tailTrace_2500901
  have hstable : (prefixWord ++ tailWord_2500901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500901).length < 2 ^ (prefixWord ++ tailWord_2500901).sum := by decide
  have hdescent : baseEnd_2500901 < baseStart_2500901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2500993 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2500993 : Nat := 118140960795 + 2500993 * 2 ^ 59
def prefixEnd_2500993 : Nat := 4983230072969 + 3 ^ 40 * 2500993 * 2
def baseEnd_2500993 : Nat := 856141015020159058057099

theorem tailTrace_2500993 : CollatzResearch.WordTrace tailWord_2500993 prefixEnd_2500993 856141015020159058057099 := by
  unfold tailWord_2500993
  simp only [CollatzResearch.WordTrace]
  refine ⟨91218708628336971443507633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60812472418891314295671755 91218708628336971443507633)
  ·
    refine ⟨68414031471252728582630725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91218708628336971443507633 68414031471252728582630725)
    ·
      refine ⟨12827630900859886609243261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68414031471252728582630725 12827630900859886609243261)
      ·
        refine ⟨4810361587822457478466223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12827630900859886609243261 4810361587822457478466223)
        ·
          refine ⟨7215542381733686217699335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4810361587822457478466223 7215542381733686217699335)
          ·
            refine ⟨10823313572600529326549003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215542381733686217699335 10823313572600529326549003)
            ·
              refine ⟨16234970358900793989823505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10823313572600529326549003 16234970358900793989823505)
              ·
                refine ⟨12176227769175595492367629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16234970358900793989823505 12176227769175595492367629)
                ·
                  refine ⟨4566085413440848309637861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12176227769175595492367629 4566085413440848309637861)
                  ·
                    refine ⟨856141015020159058057099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566085413440848309637861 856141015020159058057099)
                    ·
                      rfl

theorem cell22_2500993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2500993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2500993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2500993 prefixEnd_2500993 := by exact prefixLift 2500993
  have htrace : WordTrace (prefixWord ++ tailWord_2500993) baseStart_2500993 baseEnd_2500993 := by
    simpa [prefixWord, tailWord_2500993, baseEnd_2500993] using wordTrace_append hprefix tailTrace_2500993
  have hstable : (prefixWord ++ tailWord_2500993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2500993).length < 2 ^ (prefixWord ++ tailWord_2500993).sum := by decide
  have hdescent : baseEnd_2500993 < baseStart_2500993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2500993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501023 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 4, 3]
def baseStart_2501023 : Nat := 118140960795 + 2501023 * 2 ^ 59
def prefixEnd_2501023 : Nat := 4983230072969 + 3 ^ 40 * 2501023 * 2
def baseEnd_2501023 : Nat := 856151284633248979807007

theorem tailTrace_2501023 : CollatzResearch.WordTrace tailWord_2501023 prefixEnd_2501023 856151284633248979807007 := by
  unfold tailWord_2501023
  simp only [CollatzResearch.WordTrace]
  refine ⟨91219802818228286567099723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60813201878818857711399815 91219802818228286567099723)
  ·
    refine ⟨136829704227342429850649585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91219802818228286567099723 136829704227342429850649585)
    ·
      refine ⟨102622278170506822387987189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136829704227342429850649585 102622278170506822387987189)
      ·
        refine ⟨9620838578485014598873799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102622278170506822387987189 9620838578485014598873799)
        ·
          refine ⟨14431257867727521898310699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9620838578485014598873799 14431257867727521898310699)
          ·
            refine ⟨21646886801591282847466049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14431257867727521898310699 21646886801591282847466049)
            ·
              refine ⟨16235165101193462135599537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21646886801591282847466049 16235165101193462135599537)
              ·
                refine ⟨12176373825895096601699653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16235165101193462135599537 12176373825895096601699653)
                ·
                  refine ⟨2283070092355330612818685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12176373825895096601699653 2283070092355330612818685)
                  ·
                    refine ⟨856151284633248979807007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2283070092355330612818685 856151284633248979807007)
                    ·
                      rfl

theorem cell22_2501023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_2501023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501023 prefixEnd_2501023 := by exact prefixLift 2501023
  have htrace : WordTrace (prefixWord ++ tailWord_2501023) baseStart_2501023 baseEnd_2501023 := by
    simpa [prefixWord, tailWord_2501023, baseEnd_2501023] using wordTrace_append hprefix tailTrace_2501023
  have hstable : (prefixWord ++ tailWord_2501023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501023).length < 2 ^ (prefixWord ++ tailWord_2501023).sum := by decide
  have hdescent : baseEnd_2501023 < baseStart_2501023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501081 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 9]
def baseStart_2501081 : Nat := 118140960795 + 2501081 * 2 ^ 59
def prefixEnd_2501081 : Nat := 4983230072969 + 3 ^ 40 * 2501081 * 2
def baseEnd_2501081 : Nat := 285390379739518720618943

theorem tailTrace_2501081 : CollatzResearch.WordTrace tailWord_2501081 prefixEnd_2501081 285390379739518720618943 := by
  unfold tailWord_2501081
  simp only [CollatzResearch.WordTrace]
  refine ⟨91221918252018162472711097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60814612168012108315140731 91221918252018162472711097)
  ·
    refine ⟨68416438689013621854533323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91221918252018162472711097 68416438689013621854533323)
    ·
      refine ⟨102624658033520432781799985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68416438689013621854533323 102624658033520432781799985)
      ·
        refine ⟨76968493525140324586349989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102624658033520432781799985 76968493525140324586349989)
        ·
          refine ⟨14431592535963810859940623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76968493525140324586349989 14431592535963810859940623)
          ·
            refine ⟨21647388803945716289910935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14431592535963810859940623 21647388803945716289910935)
            ·
              refine ⟨32471083205918574434866403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21647388803945716289910935 32471083205918574434866403)
              ·
                refine ⟨48706624808877861652299605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32471083205918574434866403 48706624808877861652299605)
                ·
                  refine ⟨285390379739518720618943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48706624808877861652299605 285390379739518720618943)
                  ·
                    rfl

theorem cell22_2501081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_2501081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501081 prefixEnd_2501081 := by exact prefixLift 2501081
  have htrace : WordTrace (prefixWord ++ tailWord_2501081) baseStart_2501081 baseEnd_2501081 := by
    simpa [prefixWord, tailWord_2501081, baseEnd_2501081] using wordTrace_append hprefix tailTrace_2501081
  have hstable : (prefixWord ++ tailWord_2501081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501081).length < 2 ^ (prefixWord ++ tailWord_2501081).sum := by decide
  have hdescent : baseEnd_2501081 < baseStart_2501081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501098 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_2501098 : Nat := 118140960795 + 2501098 * 2 ^ 59
def prefixEnd_2501098 : Nat := 4983230072969 + 3 ^ 40 * 2501098 * 2
def baseEnd_2501098 : Nat := 285392319555324594727259

theorem tailTrace_2501098 : CollatzResearch.WordTrace tailWord_2501098 prefixEnd_2501098 285392319555324594727259 := by
  unfold tailWord_2501098
  simp only [CollatzResearch.WordTrace]
  refine ⟨22805634573239143594019987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60815025528637716250719965 22805634573239143594019987)
  ·
    refine ⟨34208451859858715391029981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22805634573239143594019987 34208451859858715391029981)
    ·
      refine ⟨12828169447447018271636243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34208451859858715391029981 12828169447447018271636243)
      ·
        refine ⟨19242254171170527407454365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12828169447447018271636243 19242254171170527407454365)
        ·
          refine ⟨7215845314188947777795387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19242254171170527407454365 7215845314188947777795387)
          ·
            refine ⟨10823767971283421666693081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215845314188947777795387 10823767971283421666693081)
            ·
              refine ⟨8117825978462566250019811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10823767971283421666693081 8117825978462566250019811)
              ·
                refine ⟨12176738967693849375029717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8117825978462566250019811 12176738967693849375029717)
                ·
                  refine ⟨285392319555324594727259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12176738967693849375029717 285392319555324594727259)
                  ·
                    rfl

theorem cell22_2501098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_2501098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501098 prefixEnd_2501098 := by exact prefixLift 2501098
  have htrace : WordTrace (prefixWord ++ tailWord_2501098) baseStart_2501098 baseEnd_2501098 := by
    simpa [prefixWord, tailWord_2501098, baseEnd_2501098] using wordTrace_append hprefix tailTrace_2501098
  have hstable : (prefixWord ++ tailWord_2501098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501098).length < 2 ^ (prefixWord ++ tailWord_2501098).sum := by decide
  have hdescent : baseEnd_2501098 < baseStart_2501098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501102 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_2501102 : Nat := 118140960795 + 2501102 * 2 ^ 59
def prefixEnd_2501102 : Nat := 4983230072969 + 3 ^ 40 * 2501102 * 2
def baseEnd_2501102 : Nat := 856178327947719107081765

theorem tailTrace_2501102 : CollatzResearch.WordTrace tailWord_2501102 prefixEnd_2501102 856178327947719107081765 := by
  unfold tailWord_2501102
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402835523117760382403195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60815122789961388706150373 11402835523117760382403195)
  ·
    refine ⟨17104253284676640573604793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11402835523117760382403195 17104253284676640573604793)
    ·
      refine ⟨12828189963507480430203595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17104253284676640573604793 12828189963507480430203595)
      ·
        refine ⟨19242284945261220645305393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12828189963507480430203595 19242284945261220645305393)
        ·
          refine ⟨14431713708945915483979045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19242284945261220645305393 14431713708945915483979045)
          ·
            refine ⟨2705946320427359153246071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14431713708945915483979045 2705946320427359153246071)
            ·
              refine ⟨4058919480641038729869107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705946320427359153246071 4058919480641038729869107)
              ·
                refine ⟨6088379220961558094803661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058919480641038729869107 6088379220961558094803661)
                ·
                  refine ⟨2283142207860584285551373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6088379220961558094803661 2283142207860584285551373)
                  ·
                    refine ⟨856178327947719107081765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2283142207860584285551373 856178327947719107081765)
                    ·
                      rfl

theorem cell22_2501102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_2501102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501102 prefixEnd_2501102 := by exact prefixLift 2501102
  have htrace : WordTrace (prefixWord ++ tailWord_2501102) baseStart_2501102 baseEnd_2501102 := by
    simpa [prefixWord, tailWord_2501102, baseEnd_2501102] using wordTrace_append hprefix tailTrace_2501102
  have hstable : (prefixWord ++ tailWord_2501102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501102).length < 2 ^ (prefixWord ++ tailWord_2501102).sum := by decide
  have hdescent : baseEnd_2501102 < baseStart_2501102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501173 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2501173 : Nat := 118140960795 + 2501173 * 2 ^ 59
def prefixEnd_2501173 : Nat := 4983230072969 + 3 ^ 40 * 2501173 * 2
def baseEnd_2501173 : Nat := 856202632698698588556547

theorem tailTrace_2501173 : CollatzResearch.WordTrace tailWord_2501173 prefixEnd_2501173 856202632698698588556547 := by
  unfold tailWord_2501173
  simp only [CollatzResearch.WordTrace]
  refine ⟨91225273767684862185060173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60816849178456574790040115 91225273767684862185060173)
  ·
    refine ⟨34209477662881823319397565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91225273767684862185060173 34209477662881823319397565)
    ·
      refine ⟨12828554123580683744774087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34209477662881823319397565 12828554123580683744774087)
      ·
        refine ⟨19242831185371025617161131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12828554123580683744774087 19242831185371025617161131)
        ·
          refine ⟨28864246778056538425741697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19242831185371025617161131 28864246778056538425741697)
          ·
            refine ⟨21648185083542403819306273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28864246778056538425741697 21648185083542403819306273)
            ·
              refine ⟨16236138812656802864479705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21648185083542403819306273 16236138812656802864479705)
              ·
                refine ⟨12177104109492602148359779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16236138812656802864479705 12177104109492602148359779)
                ·
                  refine ⟨18265656164238903222539669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12177104109492602148359779 18265656164238903222539669)
                  ·
                    refine ⟨856202632698698588556547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18265656164238903222539669 856202632698698588556547)
                    ·
                      rfl

theorem cell22_2501173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2501173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501173 prefixEnd_2501173 := by exact prefixLift 2501173
  have htrace : WordTrace (prefixWord ++ tailWord_2501173) baseStart_2501173 baseEnd_2501173 := by
    simpa [prefixWord, tailWord_2501173, baseEnd_2501173] using wordTrace_append hprefix tailTrace_2501173
  have hstable : (prefixWord ++ tailWord_2501173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501173).length < 2 ^ (prefixWord ++ tailWord_2501173).sum := by decide
  have hdescent : baseEnd_2501173 < baseStart_2501173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501175 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 2, 3]
def baseStart_2501175 : Nat := 118140960795 + 2501175 * 2 ^ 59
def prefixEnd_2501175 : Nat := 4983230072969 + 3 ^ 40 * 2501175 * 2
def baseEnd_2501175 : Nat := 856203317339571250006541

theorem tailTrace_2501175 : CollatzResearch.WordTrace tailWord_2501175 prefixEnd_2501175 856203317339571250006541 := by
  unfold tailWord_2501175
  simp only [CollatzResearch.WordTrace]
  refine ⟨91225346713677616526632979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60816897809118411017755319 91225346713677616526632979)
  ·
    refine ⟨136838020070516424789949469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91225346713677616526632979 136838020070516424789949469)
    ·
      refine ⟨51314257526443659296231051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136838020070516424789949469 51314257526443659296231051)
      ·
        refine ⟨76971386289665488944346577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51314257526443659296231051 76971386289665488944346577)
        ·
          refine ⟨57728539717249116708259933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76971386289665488944346577 57728539717249116708259933)
          ·
            refine ⟨21648202393968418765597475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57728539717249116708259933 21648202393968418765597475)
            ·
              refine ⟨32472303590952628148396213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21648202393968418765597475 32472303590952628148396213)
              ·
                refine ⟨3044278461651808888912145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32472303590952628148396213 3044278461651808888912145)
                ·
                  refine ⟨2283208846238856666684109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3044278461651808888912145 2283208846238856666684109)
                  ·
                    refine ⟨856203317339571250006541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2283208846238856666684109 856203317339571250006541)
                    ·
                      rfl

theorem cell22_2501175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_2501175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501175 prefixEnd_2501175 := by exact prefixLift 2501175
  have htrace : WordTrace (prefixWord ++ tailWord_2501175) baseStart_2501175 baseEnd_2501175 := by
    simpa [prefixWord, tailWord_2501175, baseEnd_2501175] using wordTrace_append hprefix tailTrace_2501175
  have hstable : (prefixWord ++ tailWord_2501175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501175).length < 2 ^ (prefixWord ++ tailWord_2501175).sum := by decide
  have hdescent : baseEnd_2501175 < baseStart_2501175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501357 : List Nat := [1, 5, 1, 2, 1, 1, 5, 6]
def baseStart_2501357 : Nat := 118140960795 + 2501357 * 2 ^ 59
def prefixEnd_2501357 : Nat := 4983230072969 + 3 ^ 40 * 2501357 * 2
def baseEnd_2501357 : Nat := 95140624406553715772887

theorem tailTrace_2501357 : CollatzResearch.WordTrace tailWord_2501357 prefixEnd_2501357 95140624406553715772887 := by
  unfold tailWord_2501357
  simp only [CollatzResearch.WordTrace]
  refine ⟨91231984799018261609758325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60821323199345507739838883 91231984799018261609758325)
  ·
    refine ⟨8552998574907962025914843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91231984799018261609758325 8552998574907962025914843)
    ·
      refine ⟨12829497862361943038872265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8552998574907962025914843 12829497862361943038872265)
      ·
        refine ⟨9622123396771457279154199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12829497862361943038872265 9622123396771457279154199)
        ·
          refine ⟨14433185095157185918731299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9622123396771457279154199 14433185095157185918731299)
          ·
            refine ⟨21649777642735778878096949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14433185095157185918731299 21649777642735778878096949)
            ·
              refine ⟨2029666654006479269821589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21649777642735778878096949 2029666654006479269821589)
              ·
                refine ⟨95140624406553715772887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2029666654006479269821589 95140624406553715772887)
                ·
                  rfl

theorem cell22_2501357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 6].length) (baseStart_2501357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501357 prefixEnd_2501357 := by exact prefixLift 2501357
  have htrace : WordTrace (prefixWord ++ tailWord_2501357) baseStart_2501357 baseEnd_2501357 := by
    simpa [prefixWord, tailWord_2501357, baseEnd_2501357] using wordTrace_append hprefix tailTrace_2501357
  have hstable : (prefixWord ++ tailWord_2501357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501357).length < 2 ^ (prefixWord ++ tailWord_2501357).sum := by decide
  have hdescent : baseEnd_2501357 < baseStart_2501357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501365 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2501365 : Nat := 118140960795 + 2501365 * 2 ^ 59
def prefixEnd_2501365 : Nat := 4983230072969 + 3 ^ 40 * 2501365 * 2
def baseEnd_2501365 : Nat := 856268358222474087755959

theorem tailTrace_2501365 : CollatzResearch.WordTrace tailWord_2501365 prefixEnd_2501365 856268358222474087755959 := by
  unfold tailWord_2501365
  simp only [CollatzResearch.WordTrace]
  refine ⟨91232276582989278976049549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60821517721992852650699699 91232276582989278976049549)
  ·
    refine ⟨34212103718620979616018581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91232276582989278976049549 34212103718620979616018581)
    ·
      refine ⟨1603692361810358419500871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34212103718620979616018581 1603692361810358419500871)
      ·
        refine ⟨2405538542715537629251307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603692361810358419500871 2405538542715537629251307)
        ·
          refine ⟨3608307814073306443876961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405538542715537629251307 3608307814073306443876961)
          ·
            refine ⟨2706230860554979832907721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3608307814073306443876961 2706230860554979832907721)
            ·
              refine ⟨2029673145416234874680791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2706230860554979832907721 2029673145416234874680791)
              ·
                refine ⟨3044509718124352312021187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029673145416234874680791 3044509718124352312021187)
                ·
                  refine ⟨4566764577186528468031781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044509718124352312021187 4566764577186528468031781)
                  ·
                    refine ⟨856268358222474087755959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566764577186528468031781 856268358222474087755959)
                    ·
                      rfl

theorem cell22_2501365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2501365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501365 prefixEnd_2501365 := by exact prefixLift 2501365
  have htrace : WordTrace (prefixWord ++ tailWord_2501365) baseStart_2501365 baseEnd_2501365 := by
    simpa [prefixWord, tailWord_2501365, baseEnd_2501365] using wordTrace_append hprefix tailTrace_2501365
  have hstable : (prefixWord ++ tailWord_2501365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501365).length < 2 ^ (prefixWord ++ tailWord_2501365).sum := by decide
  have hdescent : baseEnd_2501365 < baseStart_2501365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501432 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_2501432 : Nat := 118140960795 + 2501432 * 2 ^ 59
def prefixEnd_2501432 : Nat := 4983230072969 + 3 ^ 40 * 2501432 * 2
def baseEnd_2501432 : Nat := 856291293691708246330753

theorem tailTrace_2501432 : CollatzResearch.WordTrace tailWord_2501432 prefixEnd_2501432 856291293691708246330753 := by
  unfold tailWord_2501432
  simp only [CollatzResearch.WordTrace]
  refine ⟨45617360136873274709369275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60823146849164366279159033 45617360136873274709369275)
  ·
    refine ⟨68426040205309912064053913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45617360136873274709369275 68426040205309912064053913)
    ·
      refine ⟨51319530153982434048040435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68426040205309912064053913 51319530153982434048040435)
      ·
        refine ⟨76979295230973651072060653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51319530153982434048040435 76979295230973651072060653)
        ·
          refine ⟨28867235711615119152022745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76979295230973651072060653 28867235711615119152022745)
          ·
            refine ⟨21650426783711339364017059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28867235711615119152022745 21650426783711339364017059)
            ·
              refine ⟨32475640175567009046025589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21650426783711339364017059 32475640175567009046025589)
              ·
                refine ⟨3044591266459407098064899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32475640175567009046025589 3044591266459407098064899)
                ·
                  refine ⟨4566886899689110647097349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044591266459407098064899 4566886899689110647097349)
                  ·
                    refine ⟨856291293691708246330753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566886899689110647097349 856291293691708246330753)
                    ·
                      rfl

theorem cell22_2501432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_2501432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501432 prefixEnd_2501432 := by exact prefixLift 2501432
  have htrace : WordTrace (prefixWord ++ tailWord_2501432) baseStart_2501432 baseEnd_2501432 := by
    simpa [prefixWord, tailWord_2501432, baseEnd_2501432] using wordTrace_append hprefix tailTrace_2501432
  have hstable : (prefixWord ++ tailWord_2501432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501432).length < 2 ^ (prefixWord ++ tailWord_2501432).sum := by decide
  have hdescent : baseEnd_2501432 < baseStart_2501432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501445 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_2501445 : Nat := 118140960795 + 2501445 * 2 ^ 59
def prefixEnd_2501445 : Nat := 4983230072969 + 3 ^ 40 * 2501445 * 2
def baseEnd_2501445 : Nat := 856295743857380545755713

theorem tailTrace_2501445 : CollatzResearch.WordTrace tailWord_2501445 prefixEnd_2501445 856295743857380545755713 := by
  unfold tailWord_2501445
  simp only [CollatzResearch.WordTrace]
  refine ⟨91235194422699452638961789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60823462948466301759307859 91235194422699452638961789)
  ·
    refine ⟨34213197908512294739610671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91235194422699452638961789 34213197908512294739610671)
    ·
      refine ⟨51319796862768442109416007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34213197908512294739610671 51319796862768442109416007)
      ·
        refine ⟨76979695294152663164124011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51319796862768442109416007 76979695294152663164124011)
        ·
          refine ⟨115469542941228994746186017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76979695294152663164124011 115469542941228994746186017)
          ·
            refine ⟨86602157205921746059639513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115469542941228994746186017 86602157205921746059639513)
            ·
              refine ⟨64951617904441309544729635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86602157205921746059639513 64951617904441309544729635)
              ·
                refine ⟨97427426856661964317094453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64951617904441309544729635 97427426856661964317094453)
                ·
                  refine ⟨9133821267812059154727605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97427426856661964317094453 9133821267812059154727605)
                  ·
                    refine ⟨856295743857380545755713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9133821267812059154727605 856295743857380545755713)
                    ·
                      rfl

theorem cell22_2501445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_2501445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501445 prefixEnd_2501445 := by exact prefixLift 2501445
  have htrace : WordTrace (prefixWord ++ tailWord_2501445) baseStart_2501445 baseEnd_2501445 := by
    simpa [prefixWord, tailWord_2501445, baseEnd_2501445] using wordTrace_append hprefix tailTrace_2501445
  have hstable : (prefixWord ++ tailWord_2501445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501445).length < 2 ^ (prefixWord ++ tailWord_2501445).sum := by decide
  have hdescent : baseEnd_2501445 < baseStart_2501445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501453 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2501453 : Nat := 118140960795 + 2501453 * 2 ^ 59
def prefixEnd_2501453 : Nat := 4983230072969 + 3 ^ 40 * 2501453 * 2
def baseEnd_2501453 : Nat := 285432827473623730518563

theorem tailTrace_2501453 : CollatzResearch.WordTrace tailWord_2501453 prefixEnd_2501453 285432827473623730518563 := by
  unfold tailWord_2501453
  simp only [CollatzResearch.WordTrace]
  refine ⟨91235486206670470005253013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60823657471113646670168675 91235486206670470005253013)
  ·
    refine ⟨4276663415937678281496235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91235486206670470005253013 4276663415937678281496235)
    ·
      refine ⟨6414995123906517422244353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4276663415937678281496235 6414995123906517422244353)
      ·
        refine ⟨4811246342929888066683265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6414995123906517422244353 4811246342929888066683265)
        ·
          refine ⟨3608434757197416050012449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4811246342929888066683265 3608434757197416050012449)
          ·
            refine ⟨2706326067898062037509337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3608434757197416050012449 2706326067898062037509337)
            ·
              refine ⟨2029744550923546528132003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2706326067898062037509337 2029744550923546528132003)
              ·
                refine ⟨3044616826385319792198005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029744550923546528132003 3044616826385319792198005)
                ·
                  refine ⟨285432827473623730518563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3044616826385319792198005 285432827473623730518563)
                  ·
                    rfl

theorem cell22_2501453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2501453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501453 prefixEnd_2501453 := by exact prefixLift 2501453
  have htrace : WordTrace (prefixWord ++ tailWord_2501453) baseStart_2501453 baseEnd_2501453 := by
    simpa [prefixWord, tailWord_2501453, baseEnd_2501453] using wordTrace_append hprefix tailTrace_2501453
  have hstable : (prefixWord ++ tailWord_2501453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501453).length < 2 ^ (prefixWord ++ tailWord_2501453).sum := by decide
  have hdescent : baseEnd_2501453 < baseStart_2501453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501477 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_2501477 : Nat := 118140960795 + 2501477 * 2 ^ 59
def prefixEnd_2501477 : Nat := 4983230072969 + 3 ^ 40 * 2501477 * 2
def baseEnd_2501477 : Nat := 856306698111343128955615

theorem tailTrace_2501477 : CollatzResearch.WordTrace tailWord_2501477 prefixEnd_2501477 856306698111343128955615 := by
  unfold tailWord_2501477
  simp only [CollatzResearch.WordTrace]
  refine ⟨91236361558583522104126685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60824241039055681402751123 91236361558583522104126685)
  ·
    refine ⟨34213635584468820789047507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91236361558583522104126685 34213635584468820789047507)
    ·
      refine ⟨51320453376703231183571261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34213635584468820789047507 51320453376703231183571261)
      ·
        refine ⟨19245170016263711693839223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51320453376703231183571261 19245170016263711693839223)
        ·
          refine ⟨28867755024395567540758835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19245170016263711693839223 28867755024395567540758835)
          ·
            refine ⟨43301632536593351311138253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28867755024395567540758835 43301632536593351311138253)
            ·
              refine ⟨16238112201222506741676845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43301632536593351311138253 16238112201222506741676845)
              ·
                refine ⟨6089292075458440028128817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16238112201222506741676845 6089292075458440028128817)
                ·
                  refine ⟨4566969056593830021096613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6089292075458440028128817 4566969056593830021096613)
                  ·
                    refine ⟨856306698111343128955615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566969056593830021096613 856306698111343128955615)
                    ·
                      rfl

theorem cell22_2501477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_2501477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501477 prefixEnd_2501477 := by exact prefixLift 2501477
  have htrace : WordTrace (prefixWord ++ tailWord_2501477) baseStart_2501477 baseEnd_2501477 := by
    simpa [prefixWord, tailWord_2501477, baseEnd_2501477] using wordTrace_append hprefix tailTrace_2501477
  have hstable : (prefixWord ++ tailWord_2501477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501477).length < 2 ^ (prefixWord ++ tailWord_2501477).sum := by decide
  have hdescent : baseEnd_2501477 < baseStart_2501477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501567 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 3, 4]
def baseStart_2501567 : Nat := 118140960795 + 2501567 * 2 ^ 59
def prefixEnd_2501567 : Nat := 4983230072969 + 3 ^ 40 * 2501567 * 2
def baseEnd_2501567 : Nat := 856337506950612894205339

theorem tailTrace_2501567 : CollatzResearch.WordTrace tailWord_2501567 prefixEnd_2501567 856337506950612894205339 := by
  unfold tailWord_2501567
  simp only [CollatzResearch.WordTrace]
  refine ⟨91239644128257467474902955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60826429418838311649935303 91239644128257467474902955)
  ·
    refine ⟨136859466192386201212354433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91239644128257467474902955 136859466192386201212354433)
    ·
      refine ⟨102644599644289650909265825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136859466192386201212354433 102644599644289650909265825)
      ·
        refine ⟨76983449733217238181949369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102644599644289650909265825 76983449733217238181949369)
        ·
          refine ⟨57737587299912928636462027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76983449733217238181949369 57737587299912928636462027)
          ·
            refine ⟨86606380949869392954693041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57737587299912928636462027 86606380949869392954693041)
            ·
              refine ⟨64954785712402044716019781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86606380949869392954693041 64954785712402044716019781)
              ·
                refine ⟨12179022321075383384253709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64954785712402044716019781 12179022321075383384253709)
                ·
                  refine ⟨4567133370403268769095141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12179022321075383384253709 4567133370403268769095141)
                  ·
                    refine ⟨856337506950612894205339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4567133370403268769095141 856337506950612894205339)
                    ·
                      rfl

theorem cell22_2501567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_2501567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501567 prefixEnd_2501567 := by exact prefixLift 2501567
  have htrace : WordTrace (prefixWord ++ tailWord_2501567) baseStart_2501567 baseEnd_2501567 := by
    simpa [prefixWord, tailWord_2501567, baseEnd_2501567] using wordTrace_append hprefix tailTrace_2501567
  have hstable : (prefixWord ++ tailWord_2501567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501567).length < 2 ^ (prefixWord ++ tailWord_2501567).sum := by decide
  have hdescent : baseEnd_2501567 < baseStart_2501567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501646 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_2501646 : Nat := 118140960795 + 2501646 * 2 ^ 59
def prefixEnd_2501646 : Nat := 4983230072969 + 3 ^ 40 * 2501646 * 2
def baseEnd_2501646 : Nat := 856364550265083021480097

theorem tailTrace_2501646 : CollatzResearch.WordTrace tailWord_2501646 prefixEnd_2501646 856364550265083021480097 := by
  unfold tailWord_2501646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405315686871407995878599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60828350329980842644685861 11405315686871407995878599)
  ·
    refine ⟨17107973530307111993817899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11405315686871407995878599 17107973530307111993817899)
    ·
      refine ⟨25661960295460667990726849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17107973530307111993817899 25661960295460667990726849)
      ·
        refine ⟨19246470221595500993045137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25661960295460667990726849 19246470221595500993045137)
        ·
          refine ⟨14434852666196625744783853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19246470221595500993045137 14434852666196625744783853)
          ·
            refine ⟨5413069749823734654293945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14434852666196625744783853 5413069749823734654293945)
            ·
              refine ⟨4059802312367800990720459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5413069749823734654293945 4059802312367800990720459)
              ·
                refine ⟨6089703468551701486080689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4059802312367800990720459 6089703468551701486080689)
                ·
                  refine ⟨4567277601413776114560517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6089703468551701486080689 4567277601413776114560517)
                  ·
                    refine ⟨856364550265083021480097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4567277601413776114560517 856364550265083021480097)
                    ·
                      rfl

theorem cell22_2501646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_2501646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501646 prefixEnd_2501646 := by exact prefixLift 2501646
  have htrace : WordTrace (prefixWord ++ tailWord_2501646) baseStart_2501646 baseEnd_2501646 := by
    simpa [prefixWord, tailWord_2501646, baseEnd_2501646] using wordTrace_append hprefix tailTrace_2501646
  have hstable : (prefixWord ++ tailWord_2501646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501646).length < 2 ^ (prefixWord ++ tailWord_2501646).sum := by decide
  have hdescent : baseEnd_2501646 < baseStart_2501646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501753 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_2501753 : Nat := 118140960795 + 2501753 * 2 ^ 59
def prefixEnd_2501753 : Nat := 4983230072969 + 3 ^ 40 * 2501753 * 2
def baseEnd_2501753 : Nat := 856401178551770409054769

theorem tailTrace_2501753 : CollatzResearch.WordTrace tailWord_2501753 prefixEnd_2501753 856401178551770409054769 := by
  unfold tailWord_2501753
  simp only [CollatzResearch.WordTrace]
  refine ⟨91246428105583621241173913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60830952070389080827449275 91246428105583621241173913)
  ·
    refine ⟨68434821079187715930880435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91246428105583621241173913 68434821079187715930880435)
    ·
      refine ⟨102652231618781573896320653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68434821079187715930880435 102652231618781573896320653)
      ·
        refine ⟨38494586857043090211120245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102652231618781573896320653 38494586857043090211120245)
        ·
          refine ⟨3608867517847789707292523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38494586857043090211120245 3608867517847789707292523)
          ·
            refine ⟨5413301276771684560938785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608867517847789707292523 5413301276771684560938785)
            ·
              refine ⟨4059975957578763420704089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5413301276771684560938785 4059975957578763420704089)
              ·
                refine ⟨3044981968184072565528067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4059975957578763420704089 3044981968184072565528067)
                ·
                  refine ⟨4567472952276108848292101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044981968184072565528067 4567472952276108848292101)
                  ·
                    refine ⟨856401178551770409054769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4567472952276108848292101 856401178551770409054769)
                    ·
                      rfl

theorem cell22_2501753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_2501753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501753 prefixEnd_2501753 := by exact prefixLift 2501753
  have htrace : WordTrace (prefixWord ++ tailWord_2501753) baseStart_2501753 baseEnd_2501753 := by
    simpa [prefixWord, tailWord_2501753, baseEnd_2501753] using wordTrace_append hprefix tailTrace_2501753
  have hstable : (prefixWord ++ tailWord_2501753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501753).length < 2 ^ (prefixWord ++ tailWord_2501753).sum := by decide
  have hdescent : baseEnd_2501753 < baseStart_2501753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501796 : List Nat := [2, 3, 1, 2, 3, 2, 2, 7]
def baseStart_2501796 : Nat := 118140960795 + 2501796 * 2 ^ 59
def prefixEnd_2501796 : Nat := 4983230072969 + 3 ^ 40 * 2501796 * 2
def baseEnd_2501796 : Nat := 95157322036725847803293

theorem tailTrace_2501796 : CollatzResearch.WordTrace tailWord_2501796 prefixEnd_2501796 95157322036725847803293 := by
  unfold tailWord_2501796
  simp only [CollatzResearch.WordTrace]
  refine ⟨45623998222213919792494621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60831997629618559723326161 45623998222213919792494621)
  ·
    refine ⟨17108999333330219922185483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45623998222213919792494621 17108999333330219922185483)
    ·
      refine ⟨25663498999995329883278225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17108999333330219922185483 25663498999995329883278225)
      ·
        refine ⟨19247624249996497412458669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25663498999995329883278225 19247624249996497412458669)
        ·
          refine ⟨7217859093748686529672001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19247624249996497412458669 7217859093748686529672001)
          ·
            refine ⟨5413394320311514897254001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7217859093748686529672001 5413394320311514897254001)
            ·
              refine ⟨4060045740233636172940501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5413394320311514897254001 4060045740233636172940501)
              ·
                refine ⟨95157322036725847803293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4060045740233636172940501 95157322036725847803293)
                ·
                  rfl

theorem cell22_2501796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 7].length) (baseStart_2501796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501796 prefixEnd_2501796 := by exact prefixLift 2501796
  have htrace : WordTrace (prefixWord ++ tailWord_2501796) baseStart_2501796 baseEnd_2501796 := by
    simpa [prefixWord, tailWord_2501796, baseEnd_2501796] using wordTrace_append hprefix tailTrace_2501796
  have hstable : (prefixWord ++ tailWord_2501796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501796).length < 2 ^ (prefixWord ++ tailWord_2501796).sum := by decide
  have hdescent : baseEnd_2501796 < baseStart_2501796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501811 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 3, 3]
def baseStart_2501811 : Nat := 118140960795 + 2501811 * 2 ^ 59
def prefixEnd_2501811 : Nat := 4983230072969 + 3 ^ 40 * 2501811 * 2
def baseEnd_2501811 : Nat := 856421033137077591104591

theorem tailTrace_2501811 : CollatzResearch.WordTrace tailWord_2501811 prefixEnd_2501811 856421033137077591104591 := by
  unfold tailWord_2501811
  simp only [CollatzResearch.WordTrace]
  refine ⟨91248543539373497146785287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60832362359582331431190191 91248543539373497146785287)
  ·
    refine ⟨136872815309060245720177931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91248543539373497146785287 136872815309060245720177931)
    ·
      refine ⟨205309222963590368580266897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136872815309060245720177931 205309222963590368580266897)
      ·
        refine ⟨153981917222692776435200173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205309222963590368580266897 153981917222692776435200173)
        ·
          refine ⟨57743218958509791163200065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153981917222692776435200173 57743218958509791163200065)
          ·
            refine ⟨43307414218882343372400049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57743218958509791163200065 43307414218882343372400049)
            ·
              refine ⟨32480560664161757529300037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43307414218882343372400049 32480560664161757529300037)
              ·
                refine ⟨6090105124530329536743757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32480560664161757529300037 6090105124530329536743757)
                ·
                  refine ⟨2283789421698873576278909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6090105124530329536743757 2283789421698873576278909)
                  ·
                    refine ⟨856421033137077591104591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2283789421698873576278909 856421033137077591104591)
                    ·
                      rfl

theorem cell22_2501811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 3].length) (baseStart_2501811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501811 prefixEnd_2501811 := by exact prefixLift 2501811
  have htrace : WordTrace (prefixWord ++ tailWord_2501811) baseStart_2501811 baseEnd_2501811 := by
    simpa [prefixWord, tailWord_2501811, baseEnd_2501811] using wordTrace_append hprefix tailTrace_2501811
  have hstable : (prefixWord ++ tailWord_2501811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501811).length < 2 ^ (prefixWord ++ tailWord_2501811).sum := by decide
  have hdescent : baseEnd_2501811 < baseStart_2501811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501830 : List Nat := [6, 1, 2, 2, 1, 10]
def baseStart_2501830 : Nat := 118140960795 + 2501830 * 2 ^ 59
def prefixEnd_2501830 : Nat := 4983230072969 + 3 ^ 40 * 2501830 * 2
def baseEnd_2501830 : Nat := 10573179471918121912093

theorem tailTrace_2501830 : CollatzResearch.WordTrace tailWord_2501830 prefixEnd_2501830 10573179471918121912093 := by
  unfold tailWord_2501830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2851538641447020730991467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60832824350869775594484629 2851538641447020730991467)
  ·
    refine ⟨4277307962170531096487201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2851538641447020730991467 4277307962170531096487201)
    ·
      refine ⟨3207980971627898322365401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4277307962170531096487201 3207980971627898322365401)
      ·
        refine ⟨2405985728720923741774051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3207980971627898322365401 2405985728720923741774051)
        ·
          refine ⟨3608978593081385612661077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405985728720923741774051 3608978593081385612661077)
          ·
            refine ⟨10573179471918121912093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3608978593081385612661077 10573179471918121912093)
            ·
              rfl

theorem cell22_2501830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 10].length) (baseStart_2501830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501830 prefixEnd_2501830 := by exact prefixLift 2501830
  have htrace : WordTrace (prefixWord ++ tailWord_2501830) baseStart_2501830 baseEnd_2501830 := by
    simpa [prefixWord, tailWord_2501830, baseEnd_2501830] using wordTrace_append hprefix tailTrace_2501830
  have hstable : (prefixWord ++ tailWord_2501830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501830).length < 2 ^ (prefixWord ++ tailWord_2501830).sum := by decide
  have hdescent : baseEnd_2501830 < baseStart_2501830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501856 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_2501856 : Nat := 118140960795 + 2501856 * 2 ^ 59
def prefixEnd_2501856 : Nat := 4983230072969 + 3 ^ 40 * 2501856 * 2
def baseEnd_2501856 : Nat := 856436437556712473729453

theorem tailTrace_2501856 : CollatzResearch.WordTrace tailWord_2501856 prefixEnd_2501856 856436437556712473729453 := by
  unfold tailWord_2501856
  simp only [CollatzResearch.WordTrace]
  refine ⟨45625092412105234916086711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60833456549473646554782281 45625092412105234916086711)
  ·
    refine ⟨68437638618157852374130067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45625092412105234916086711 68437638618157852374130067)
    ·
      refine ⟨102656457927236778561195101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68437638618157852374130067 102656457927236778561195101)
      ·
        refine ⟨38496171722713791960448163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102656457927236778561195101 38496171722713791960448163)
        ·
          refine ⟨57744257584070687940672245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38496171722713791960448163 57744257584070687940672245)
          ·
            refine ⟨5413524148506626994438023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57744257584070687940672245 5413524148506626994438023)
            ·
              refine ⟨8120286222759940491657035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5413524148506626994438023 8120286222759940491657035)
              ·
                refine ⟨12180429334139910737485553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8120286222759940491657035 12180429334139910737485553)
                ·
                  refine ⟨9135322000604933053114165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12180429334139910737485553 9135322000604933053114165)
                  ·
                    refine ⟨856436437556712473729453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9135322000604933053114165 856436437556712473729453)
                    ·
                      rfl

theorem cell22_2501856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_2501856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501856 prefixEnd_2501856 := by exact prefixLift 2501856
  have htrace : WordTrace (prefixWord ++ tailWord_2501856) baseStart_2501856 baseEnd_2501856 := by
    simpa [prefixWord, tailWord_2501856, baseEnd_2501856] using wordTrace_append hprefix tailTrace_2501856
  have hstable : (prefixWord ++ tailWord_2501856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501856).length < 2 ^ (prefixWord ++ tailWord_2501856).sum := by decide
  have hdescent : baseEnd_2501856 < baseStart_2501856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2501916 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2501916 : Nat := 118140960795 + 2501916 * 2 ^ 59
def prefixEnd_2501916 : Nat := 4983230072969 + 3 ^ 40 * 2501916 * 2
def baseEnd_2501916 : Nat := 856456976782892317229269

theorem tailTrace_2501916 : CollatzResearch.WordTrace tailWord_2501916 prefixEnd_2501916 856456976782892317229269 := by
  unfold tailWord_2501916
  simp only [CollatzResearch.WordTrace]
  refine ⟨45626186601996550039678801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60834915469328733386238401 45626186601996550039678801)
  ·
    refine ⟨34219639951497412529759101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45626186601996550039678801 34219639951497412529759101)
    ·
      refine ⟨12832364981811529698659663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34219639951497412529759101 12832364981811529698659663)
      ·
        refine ⟨19248547472717294547989495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12832364981811529698659663 19248547472717294547989495)
        ·
          refine ⟨28872821209075941821984243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19248547472717294547989495 28872821209075941821984243)
          ·
            refine ⟨43309231813613912732976365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28872821209075941821984243 43309231813613912732976365)
            ·
              refine ⟨16240961930105217274866137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43309231813613912732976365 16240961930105217274866137)
              ·
                refine ⟨12180721447578912956149603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16240961930105217274866137 12180721447578912956149603)
                ·
                  refine ⟨18271082171368369434224405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12180721447578912956149603 18271082171368369434224405)
                  ·
                    refine ⟨856456976782892317229269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18271082171368369434224405 856456976782892317229269)
                    ·
                      rfl

theorem cell22_2501916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2501916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2501916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2501916 prefixEnd_2501916 := by exact prefixLift 2501916
  have htrace : WordTrace (prefixWord ++ tailWord_2501916) baseStart_2501916 baseEnd_2501916 := by
    simpa [prefixWord, tailWord_2501916, baseEnd_2501916] using wordTrace_append hprefix tailTrace_2501916
  have hstable : (prefixWord ++ tailWord_2501916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2501916).length < 2 ^ (prefixWord ++ tailWord_2501916).sum := by decide
  have hdescent : baseEnd_2501916 < baseStart_2501916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2501916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502023 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2502023 : Nat := 118140960795 + 2502023 * 2 ^ 59
def prefixEnd_2502023 : Nat := 4983230072969 + 3 ^ 40 * 2502023 * 2
def baseEnd_2502023 : Nat := 856493605069579704803941

theorem tailTrace_2502023 : CollatzResearch.WordTrace tailWord_2502023 prefixEnd_2502023 856493605069579704803941 := by
  unfold tailWord_2502023
  simp only [CollatzResearch.WordTrace]
  refine ⟨91256275814605457353502723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60837517209736971569001815 91256275814605457353502723)
  ·
    refine ⟨136884413721908186030254085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91256275814605457353502723 136884413721908186030254085)
    ·
      refine ⟨25665827572857784880672641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136884413721908186030254085 25665827572857784880672641)
      ·
        refine ⟨19249370679643338660504481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25665827572857784880672641 19249370679643338660504481)
        ·
          refine ⟨14437028009732503995378361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19249370679643338660504481 14437028009732503995378361)
          ·
            refine ⟨10827771007299377996533771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14437028009732503995378361 10827771007299377996533771)
            ·
              refine ⟨16241656510949066994800657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10827771007299377996533771 16241656510949066994800657)
              ·
                refine ⟨12181242383211800246100493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16241656510949066994800657 12181242383211800246100493)
                ·
                  refine ⟨4567965893704425092287685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12181242383211800246100493 4567965893704425092287685)
                  ·
                    refine ⟨856493605069579704803941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4567965893704425092287685 856493605069579704803941)
                    ·
                      rfl

theorem cell22_2502023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2502023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502023 prefixEnd_2502023 := by exact prefixLift 2502023
  have htrace : WordTrace (prefixWord ++ tailWord_2502023) baseStart_2502023 baseEnd_2502023 := by
    simpa [prefixWord, tailWord_2502023, baseEnd_2502023] using wordTrace_append hprefix tailTrace_2502023
  have hstable : (prefixWord ++ tailWord_2502023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502023).length < 2 ^ (prefixWord ++ tailWord_2502023).sum := by decide
  have hdescent : baseEnd_2502023 < baseStart_2502023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502087 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 2, 3]
def baseStart_2502087 : Nat := 118140960795 + 2502087 * 2 ^ 59
def prefixEnd_2502087 : Nat := 4983230072969 + 3 ^ 40 * 2502087 * 2
def baseEnd_2502087 : Nat := 856515513577504871203745

theorem tailTrace_2502087 : CollatzResearch.WordTrace tailWord_2502087 prefixEnd_2502087 856515513577504871203745 := by
  unfold tailWord_2502087
  simp only [CollatzResearch.WordTrace]
  refine ⟨91258610086373596283832515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60839073390915730855888343 91258610086373596283832515)
  ·
    refine ⟨136887915129560394425748773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91258610086373596283832515 136887915129560394425748773)
    ·
      refine ⟨25666484086792573954827895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136887915129560394425748773 25666484086792573954827895)
      ·
        refine ⟨38499726130188860932241843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25666484086792573954827895 38499726130188860932241843)
        ·
          refine ⟨57749589195283291398362765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38499726130188860932241843 57749589195283291398362765)
          ·
            refine ⟨21656095948231234274386037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57749589195283291398362765 21656095948231234274386037)
            ·
              refine ⟨2030258995146678213223691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21656095948231234274386037 2030258995146678213223691)
              ·
                refine ⟨3045388492720017319835537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030258995146678213223691 3045388492720017319835537)
                ·
                  refine ⟨2284041369540012989876653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3045388492720017319835537 2284041369540012989876653)
                  ·
                    refine ⟨856515513577504871203745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2284041369540012989876653 856515513577504871203745)
                    ·
                      rfl

theorem cell22_2502087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_2502087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502087 prefixEnd_2502087 := by exact prefixLift 2502087
  have htrace : WordTrace (prefixWord ++ tailWord_2502087) baseStart_2502087 baseEnd_2502087 := by
    simpa [prefixWord, tailWord_2502087, baseEnd_2502087] using wordTrace_append hprefix tailTrace_2502087
  have hstable : (prefixWord ++ tailWord_2502087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502087).length < 2 ^ (prefixWord ++ tailWord_2502087).sum := by decide
  have hdescent : baseEnd_2502087 < baseStart_2502087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502100 : List Nat := [2, 4, 1, 2, 3, 1, 1, 8]
def baseStart_2502100 : Nat := 118140960795 + 2502100 * 2 ^ 59
def prefixEnd_2502100 : Nat := 4983230072969 + 3 ^ 40 * 2502100 * 2
def baseEnd_2502100 : Nat := 95168884860353018958745

theorem tailTrace_2502100 : CollatzResearch.WordTrace tailWord_2502100 prefixEnd_2502100 95168884860353018958745 := by
  unfold tailWord_2502100
  simp only [CollatzResearch.WordTrace]
  refine ⟨45629542117663249752027877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60839389490217666336037169 45629542117663249752027877)
  ·
    refine ⟨8555539147061859328505227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45629542117663249752027877 8555539147061859328505227)
    ·
      refine ⟨12833308720592788992757841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8555539147061859328505227 12833308720592788992757841)
      ·
        refine ⟨9624981540444591744568381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12833308720592788992757841 9624981540444591744568381)
        ·
          refine ⟨3609368077666721904213143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9624981540444591744568381 3609368077666721904213143)
          ·
            refine ⟨5414052116500082856319715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609368077666721904213143 5414052116500082856319715)
            ·
              refine ⟨8121078174750124284479573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414052116500082856319715 8121078174750124284479573)
              ·
                refine ⟨95168884860353018958745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8121078174750124284479573 95168884860353018958745)
                ·
                  rfl

theorem cell22_2502100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 8].length) (baseStart_2502100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502100 prefixEnd_2502100 := by exact prefixLift 2502100
  have htrace : WordTrace (prefixWord ++ tailWord_2502100) baseStart_2502100 baseEnd_2502100 := by
    simpa [prefixWord, tailWord_2502100, baseEnd_2502100] using wordTrace_append hprefix tailTrace_2502100
  have hstable : (prefixWord ++ tailWord_2502100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502100).length < 2 ^ (prefixWord ++ tailWord_2502100).sum := by decide
  have hdescent : baseEnd_2502100 < baseStart_2502100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502128 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 7]
def baseStart_2502128 : Nat := 118140960795 + 2502128 * 2 ^ 59
def prefixEnd_2502128 : Nat := 4983230072969 + 3 ^ 40 * 2502128 * 2
def baseEnd_2502128 : Nat := 285509849571798143642873

theorem tailTrace_2502128 : CollatzResearch.WordTrace tailWord_2502128 prefixEnd_2502128 285509849571798143642873 := by
  unfold tailWord_2502128
  simp only [CollatzResearch.WordTrace]
  refine ⟨45630052739612530143037519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60840070319483373524050025 45630052739612530143037519)
  ·
    refine ⟨68445079109418795214556279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45630052739612530143037519 68445079109418795214556279)
    ·
      refine ⟨102667618664128192821834419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68445079109418795214556279 102667618664128192821834419)
      ·
        refine ⟨154001427996192289232751629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102667618664128192821834419 154001427996192289232751629)
        ·
          refine ⟨57750535498572108462281861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154001427996192289232751629 57750535498572108462281861)
          ·
            refine ⟨10828225405982270336677849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57750535498572108462281861 10828225405982270336677849)
            ·
              refine ⟨8121169054486702752508387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10828225405982270336677849 8121169054486702752508387)
              ·
                refine ⟨12181753581730054128762581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121169054486702752508387 12181753581730054128762581)
                ·
                  refine ⟨285509849571798143642873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12181753581730054128762581 285509849571798143642873)
                  ·
                    rfl

theorem cell22_2502128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_2502128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502128 prefixEnd_2502128 := by exact prefixLift 2502128
  have htrace : WordTrace (prefixWord ++ tailWord_2502128) baseStart_2502128 baseEnd_2502128 := by
    simpa [prefixWord, tailWord_2502128, baseEnd_2502128] using wordTrace_append hprefix tailTrace_2502128
  have hstable : (prefixWord ++ tailWord_2502128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502128).length < 2 ^ (prefixWord ++ tailWord_2502128).sum := by decide
  have hdescent : baseEnd_2502128 < baseStart_2502128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502175 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 1, 4]
def baseStart_2502175 : Nat := 118140960795 + 2502175 * 2 ^ 59
def prefixEnd_2502175 : Nat := 4983230072969 + 3 ^ 40 * 2502175 * 2
def baseEnd_2502175 : Nat := 856545637775901975003475

theorem tailTrace_2502175 : CollatzResearch.WordTrace tailWord_2502175 prefixEnd_2502175 856545637775901975003475 := by
  unfold tailWord_2502175
  simp only [CollatzResearch.WordTrace]
  refine ⟨91261819710054787313035979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60841213140036524875357319 91261819710054787313035979)
  ·
    refine ⟨136892729565082180969553969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91261819710054787313035979 136892729565082180969553969)
    ·
      refine ⟨102669547173811635727165477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136892729565082180969553969 102669547173811635727165477)
      ·
        refine ⟨19250540095089681698843527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102669547173811635727165477 19250540095089681698843527)
        ·
          refine ⟨28875810142634522548265291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19250540095089681698843527 28875810142634522548265291)
          ·
            refine ⟨43313715213951783822397937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28875810142634522548265291 43313715213951783822397937)
            ·
              refine ⟨32485286410463837866798453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43313715213951783822397937 32485286410463837866798453)
              ·
                refine ⟨3045495600980984800012355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32485286410463837866798453 3045495600980984800012355)
                ·
                  refine ⟨4568243401471477200018533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045495600980984800012355 4568243401471477200018533)
                  ·
                    refine ⟨856545637775901975003475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4568243401471477200018533 856545637775901975003475)
                    ·
                      rfl

theorem cell22_2502175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_2502175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502175 prefixEnd_2502175 := by exact prefixLift 2502175
  have htrace : WordTrace (prefixWord ++ tailWord_2502175) baseStart_2502175 baseEnd_2502175 := by
    simpa [prefixWord, tailWord_2502175, baseEnd_2502175] using wordTrace_append hprefix tailTrace_2502175
  have hstable : (prefixWord ++ tailWord_2502175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502175).length < 2 ^ (prefixWord ++ tailWord_2502175).sum := by decide
  have hdescent : baseEnd_2502175 < baseStart_2502175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502220 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_2502220 : Nat := 118140960795 + 2502220 * 2 ^ 59
def prefixEnd_2502220 : Nat := 4983230072969 + 3 ^ 40 * 2502220 * 2
def baseEnd_2502220 : Nat := 856561042195536857628337

theorem tailTrace_2502220 : CollatzResearch.WordTrace tailWord_2502220 prefixEnd_2502220 856561042195536857628337 := by
  unfold tailWord_2502220
  simp only [CollatzResearch.WordTrace]
  refine ⟨45631730497445879999212057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60842307329927839998949409 45631730497445879999212057)
  ·
    refine ⟨34223797873084409999409043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45631730497445879999212057 34223797873084409999409043)
    ·
      refine ⟨51335696809626614999113565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34223797873084409999409043 51335696809626614999113565)
      ·
        refine ⟨19250886303609980624667587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51335696809626614999113565 19250886303609980624667587)
        ·
          refine ⟨28876329455414970937001381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19250886303609980624667587 28876329455414970937001381)
          ·
            refine ⟨5414311772890307050687759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28876329455414970937001381 5414311772890307050687759)
            ·
              refine ⟨8121467659335460576031639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414311772890307050687759 8121467659335460576031639)
              ·
                refine ⟨12182201489003190864047459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121467659335460576031639 12182201489003190864047459)
                ·
                  refine ⟨18273302233504786296071189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12182201489003190864047459 18273302233504786296071189)
                  ·
                    refine ⟨856561042195536857628337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18273302233504786296071189 856561042195536857628337)
                    ·
                      rfl

theorem cell22_2502220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_2502220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502220 prefixEnd_2502220 := by exact prefixLift 2502220
  have htrace : WordTrace (prefixWord ++ tailWord_2502220) baseStart_2502220 baseEnd_2502220 := by
    simpa [prefixWord, tailWord_2502220, baseEnd_2502220] using wordTrace_append hprefix tailTrace_2502220
  have hstable : (prefixWord ++ tailWord_2502220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502220).length < 2 ^ (prefixWord ++ tailWord_2502220).sum := by decide
  have hdescent : baseEnd_2502220 < baseStart_2502220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502233 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_2502233 : Nat := 118140960795 + 2502233 * 2 ^ 59
def prefixEnd_2502233 : Nat := 4983230072969 + 3 ^ 40 * 2502233 * 2
def baseEnd_2502233 : Nat := 856565492361209157053297

theorem tailTrace_2502233 : CollatzResearch.WordTrace tailWord_2502233 prefixEnd_2502233 856565492361209157053297 := by
  unfold tailWord_2502233
  simp only [CollatzResearch.WordTrace]
  refine ⟨91263935143844663218647353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60842623429229775479098235 91263935143844663218647353)
  ·
    refine ⟨68447951357883497413985515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91263935143844663218647353 68447951357883497413985515)
    ·
      refine ⟨102671927036825246120978273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68447951357883497413985515 102671927036825246120978273)
      ·
        refine ⟨77003945277618934590733705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102671927036825246120978273 77003945277618934590733705)
        ·
          refine ⟨57752958958214200943050279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77003945277618934590733705 57752958958214200943050279)
          ·
            refine ⟨86629438437321301414575419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57752958958214200943050279 86629438437321301414575419)
            ·
              refine ⟨129944157655981952121863129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86629438437321301414575419 129944157655981952121863129)
              ·
                refine ⟨97458118241986464091397347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129944157655981952121863129 97458118241986464091397347)
                ·
                  refine ⟨146187177362979696137096021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97458118241986464091397347 146187177362979696137096021)
                  ·
                    refine ⟨856565492361209157053297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 146187177362979696137096021 856565492361209157053297)
                    ·
                      rfl

theorem cell22_2502233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_2502233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502233 prefixEnd_2502233 := by exact prefixLift 2502233
  have htrace : WordTrace (prefixWord ++ tailWord_2502233) baseStart_2502233 baseEnd_2502233 := by
    simpa [prefixWord, tailWord_2502233, baseEnd_2502233] using wordTrace_append hprefix tailTrace_2502233
  have hstable : (prefixWord ++ tailWord_2502233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502233).length < 2 ^ (prefixWord ++ tailWord_2502233).sum := by decide
  have hdescent : baseEnd_2502233 < baseStart_2502233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502327 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 3, 4]
def baseStart_2502327 : Nat := 118140960795 + 2502327 * 2 ^ 59
def prefixEnd_2502327 : Nat := 4983230072969 + 3 ^ 40 * 2502327 * 2
def baseEnd_2502327 : Nat := 856597670482224245203009

theorem tailTrace_2502327 : CollatzResearch.WordTrace tailWord_2502327 prefixEnd_2502327 856597670482224245203009 := by
  unfold tailWord_2502327
  simp only [CollatzResearch.WordTrace]
  refine ⟨91267363605504117272569235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60844909070336078181712823 91267363605504117272569235)
  ·
    refine ⟨136901045408256175908853853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91267363605504117272569235 136901045408256175908853853)
    ·
      refine ⟨51337892028096065965820195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136901045408256175908853853 51337892028096065965820195)
      ·
        refine ⟨77006838042144098948730293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51337892028096065965820195 77006838042144098948730293)
        ·
          refine ⟨7219391066451009276443465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77006838042144098948730293 7219391066451009276443465)
          ·
            refine ⟨5414543299838256957332599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7219391066451009276443465 5414543299838256957332599)
            ·
              refine ⟨8121814949757385435998899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414543299838256957332599 8121814949757385435998899)
              ·
                refine ⟨12182722424636078153998349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121814949757385435998899 12182722424636078153998349)
                ·
                  refine ⟨4568520909238529307749381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12182722424636078153998349 4568520909238529307749381)
                  ·
                    refine ⟨856597670482224245203009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4568520909238529307749381 856597670482224245203009)
                    ·
                      rfl

theorem cell22_2502327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_2502327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502327 prefixEnd_2502327 := by exact prefixLift 2502327
  have htrace : WordTrace (prefixWord ++ tailWord_2502327) baseStart_2502327 baseEnd_2502327 := by
    simpa [prefixWord, tailWord_2502327, baseEnd_2502327] using wordTrace_append hprefix tailTrace_2502327
  have hstable : (prefixWord ++ tailWord_2502327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502327).length < 2 ^ (prefixWord ++ tailWord_2502327).sum := by decide
  have hdescent : baseEnd_2502327 < baseStart_2502327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502344 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 1, 4]
def baseStart_2502344 : Nat := 118140960795 + 2502344 * 2 ^ 59
def prefixEnd_2502344 : Nat := 4983230072969 + 3 ^ 40 * 2502344 * 2
def baseEnd_2502344 : Nat := 856603489929641867527957

theorem tailTrace_2502344 : CollatzResearch.WordTrace tailWord_2502344 prefixEnd_2502344 856603489929641867527957 := by
  unfold tailWord_2502344
  simp only [CollatzResearch.WordTrace]
  refine ⟨45633991823221264587969043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60845322430961686117292057 45633991823221264587969043)
  ·
    refine ⟨68450987734831896881953565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45633991823221264587969043 68450987734831896881953565)
    ·
      refine ⟨25669120400561961330732587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68450987734831896881953565 25669120400561961330732587)
      ·
        refine ⟨38503680600842941996098881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25669120400561961330732587 38503680600842941996098881)
        ·
          refine ⟨28877760450632206497074161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38503680600842941996098881 28877760450632206497074161)
          ·
            refine ⟨21658320337974154872805621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28877760450632206497074161 21658320337974154872805621)
            ·
              refine ⟨2030467531685077019325527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21658320337974154872805621 2030467531685077019325527)
              ·
                refine ⟨3045701297527615528988291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030467531685077019325527 3045701297527615528988291)
                ·
                  refine ⟨4568551946291423293482437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045701297527615528988291 4568551946291423293482437)
                  ·
                    refine ⟨856603489929641867527957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4568551946291423293482437 856603489929641867527957)
                    ·
                      rfl

theorem cell22_2502344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_2502344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502344 prefixEnd_2502344 := by exact prefixLift 2502344
  have htrace : WordTrace (prefixWord ++ tailWord_2502344) baseStart_2502344 baseEnd_2502344 := by
    simpa [prefixWord, tailWord_2502344, baseEnd_2502344] using wordTrace_append hprefix tailTrace_2502344
  have hstable : (prefixWord ++ tailWord_2502344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502344).length < 2 ^ (prefixWord ++ tailWord_2502344).sum := by decide
  have hdescent : baseEnd_2502344 < baseStart_2502344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502355 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 8, 4]
def baseStart_2502355 : Nat := 118140960795 + 2502355 * 2 ^ 59
def prefixEnd_2502355 : Nat := 4983230072969 + 3 ^ 40 * 2502355 * 2
def baseEnd_2502355 : Nat := 856607255454441505502923

theorem tailTrace_2502355 : CollatzResearch.WordTrace tailWord_2502355 prefixEnd_2502355 856607255454441505502923 := by
  unfold tailWord_2502355
  simp only [CollatzResearch.WordTrace]
  refine ⟨91268384849402678054588519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60845589899601785369725679 91268384849402678054588519)
  ·
    refine ⟨136902577274104017081882779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91268384849402678054588519 136902577274104017081882779)
    ·
      refine ⟨205353865911156025622824169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136902577274104017081882779 205353865911156025622824169)
      ·
        refine ⟨154015399433367019217118127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205353865911156025622824169 154015399433367019217118127)
        ·
          refine ⟨231023099150050528825677191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154015399433367019217118127 231023099150050528825677191)
          ·
            refine ⟨346534648725075793238515787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231023099150050528825677191 346534648725075793238515787)
            ·
              refine ⟨519801973087613689857773681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346534648725075793238515787 519801973087613689857773681)
              ·
                refine ⟨389851479815710267393330261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519801973087613689857773681 389851479815710267393330261)
                ·
                  refine ⟨4568572029090354696015589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 389851479815710267393330261 4568572029090354696015589)
                  ·
                    refine ⟨856607255454441505502923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4568572029090354696015589 856607255454441505502923)
                    ·
                      rfl

theorem cell22_2502355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 4].length) (baseStart_2502355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502355 prefixEnd_2502355 := by exact prefixLift 2502355
  have htrace : WordTrace (prefixWord ++ tailWord_2502355) baseStart_2502355 baseEnd_2502355 := by
    simpa [prefixWord, tailWord_2502355, baseEnd_2502355] using wordTrace_append hprefix tailTrace_2502355
  have hstable : (prefixWord ++ tailWord_2502355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502355).length < 2 ^ (prefixWord ++ tailWord_2502355).sum := by decide
  have hdescent : baseEnd_2502355 < baseStart_2502355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502400 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_2502400 : Nat := 118140960795 + 2502400 * 2 ^ 59
def prefixEnd_2502400 : Nat := 4983230072969 + 3 ^ 40 * 2502400 * 2
def baseEnd_2502400 : Nat := 856622659874076388127785

theorem tailTrace_2502400 : CollatzResearch.WordTrace tailWord_2502400 prefixEnd_2502400 856622659874076388127785 := by
  unfold tailWord_2502400
  simp only [CollatzResearch.WordTrace]
  refine ⟨45635013067119825369988327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60846684089493100493317769 45635013067119825369988327)
  ·
    refine ⟨68452519600679738054982491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45635013067119825369988327 68452519600679738054982491)
    ·
      refine ⟨102678779401019607082473737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68452519600679738054982491 102678779401019607082473737)
      ·
        refine ⟨77009084550764705311855303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102678779401019607082473737 77009084550764705311855303)
        ·
          refine ⟨115513626826147057967782955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77009084550764705311855303 115513626826147057967782955)
          ·
            refine ⟨173270440239220586951674433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115513626826147057967782955 173270440239220586951674433)
            ·
              refine ⟨129952830179415440213755825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173270440239220586951674433 129952830179415440213755825)
              ·
                refine ⟨97464622634561580160316869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129952830179415440213755825 97464622634561580160316869)
                ·
                  refine ⟨18274616743980296280059413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97464622634561580160316869 18274616743980296280059413)
                  ·
                    refine ⟨856622659874076388127785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18274616743980296280059413 856622659874076388127785)
                    ·
                      rfl

theorem cell22_2502400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_2502400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502400 prefixEnd_2502400 := by exact prefixLift 2502400
  have htrace : WordTrace (prefixWord ++ tailWord_2502400) baseStart_2502400 baseEnd_2502400 := by
    simpa [prefixWord, tailWord_2502400, baseEnd_2502400] using wordTrace_append hprefix tailTrace_2502400
  have hstable : (prefixWord ++ tailWord_2502400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502400).length < 2 ^ (prefixWord ++ tailWord_2502400).sum := by decide
  have hdescent : baseEnd_2502400 < baseStart_2502400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502470 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2502470 : Nat := 118140960795 + 2502470 * 2 ^ 59
def prefixEnd_2502470 : Nat := 4983230072969 + 3 ^ 40 * 2502470 * 2
def baseEnd_2502470 : Nat := 856646622304619538877571

theorem tailTrace_2502470 : CollatzResearch.WordTrace tailWord_2502470 prefixEnd_2502470 856646622304619538877571 := by
  unfold tailWord_2502470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852268101374564146719527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60848386162657368463349909 2852268101374564146719527)
  ·
    refine ⟨4278402152061846220079291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2852268101374564146719527 4278402152061846220079291)
    ·
      refine ⟨6417603228092769330118937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278402152061846220079291 6417603228092769330118937)
      ·
        refine ⟨4813202421069576997589203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6417603228092769330118937 4813202421069576997589203)
        ·
          refine ⟨7219803631604365496383805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4813202421069576997589203 7219803631604365496383805)
          ·
            refine ⟨2707426361851637061143927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7219803631604365496383805 2707426361851637061143927)
            ·
              refine ⟨4061139542777455591715891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707426361851637061143927 4061139542777455591715891)
              ·
                refine ⟨6091709314166183387573837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4061139542777455591715891 6091709314166183387573837)
                ·
                  refine ⟨2284390992812318770340189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6091709314166183387573837 2284390992812318770340189)
                  ·
                    refine ⟨856646622304619538877571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2284390992812318770340189 856646622304619538877571)
                    ·
                      rfl

theorem cell22_2502470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2502470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502470 prefixEnd_2502470 := by exact prefixLift 2502470
  have htrace : WordTrace (prefixWord ++ tailWord_2502470) baseStart_2502470 baseEnd_2502470 := by
    simpa [prefixWord, tailWord_2502470, baseEnd_2502470] using wordTrace_append hprefix tailTrace_2502470
  have hstable : (prefixWord ++ tailWord_2502470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502470).length < 2 ^ (prefixWord ++ tailWord_2502470).sum := by decide
  have hdescent : baseEnd_2502470 < baseStart_2502470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502496 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 1, 4]
def baseStart_2502496 : Nat := 118140960795 + 2502496 * 2 ^ 59
def prefixEnd_2502496 : Nat := 4983230072969 + 3 ^ 40 * 2502496 * 2
def baseEnd_2502496 : Nat := 856655522635964137727491

theorem tailTrace_2502496 : CollatzResearch.WordTrace tailWord_2502496 prefixEnd_2502496 856655522635964137727491 := by
  unfold tailWord_2502496
  simp only [CollatzResearch.WordTrace]
  refine ⟨45636763770945929567735671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60849018361261239423647561 45636763770945929567735671)
  ·
    refine ⟨68455145656418894351603507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45636763770945929567735671 68455145656418894351603507)
    ·
      refine ⟨102682718484628341527405261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68455145656418894351603507 102682718484628341527405261)
      ·
        refine ⟨38506019431735628072776973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102682718484628341527405261 38506019431735628072776973)
        ·
          refine ⟨14439757286900860527291365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38506019431735628072776973 14439757286900860527291365)
          ·
            refine ⟨2707454491293911348867131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14439757286900860527291365 2707454491293911348867131)
            ·
              refine ⟨4061181736940867023300697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707454491293911348867131 4061181736940867023300697)
              ·
                refine ⟨3045886302705650267475523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4061181736940867023300697 3045886302705650267475523)
                ·
                  refine ⟨4568829454058475401213285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045886302705650267475523 4568829454058475401213285)
                  ·
                    refine ⟨856655522635964137727491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4568829454058475401213285 856655522635964137727491)
                    ·
                      rfl

theorem cell22_2502496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_2502496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502496 prefixEnd_2502496 := by exact prefixLift 2502496
  have htrace : WordTrace (prefixWord ++ tailWord_2502496) baseStart_2502496 baseEnd_2502496 := by
    simpa [prefixWord, tailWord_2502496, baseEnd_2502496] using wordTrace_append hprefix tailTrace_2502496
  have hstable : (prefixWord ++ tailWord_2502496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502496).length < 2 ^ (prefixWord ++ tailWord_2502496).sum := by decide
  have hdescent : baseEnd_2502496 < baseStart_2502496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502509 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_2502509 : Nat := 118140960795 + 2502509 * 2 ^ 59
def prefixEnd_2502509 : Nat := 4983230072969 + 3 ^ 40 * 2502509 * 2
def baseEnd_2502509 : Nat := 856659972801636437152451

theorem tailTrace_2502509 : CollatzResearch.WordTrace tailWord_2502509 prefixEnd_2502509 856659972801636437152451 := by
  unfold tailWord_2502509
  simp only [CollatzResearch.WordTrace]
  refine ⟨91274001690844762355694581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60849334460563174903796387 91274001690844762355694581)
  ·
    refine ⟨8556937658516696470846367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91274001690844762355694581 8556937658516696470846367)
    ·
      refine ⟨12835406487775044706269551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8556937658516696470846367 12835406487775044706269551)
      ·
        refine ⟨19253109731662567059404327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12835406487775044706269551 19253109731662567059404327)
        ·
          refine ⟨28879664597493850589106491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19253109731662567059404327 28879664597493850589106491)
          ·
            refine ⟨43319496896240775883659737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28879664597493850589106491 43319496896240775883659737)
            ·
              refine ⟨32489622672180581912744803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43319496896240775883659737 32489622672180581912744803)
              ·
                refine ⟨48734434008270872869117205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32489622672180581912744803 48734434008270872869117205)
                ·
                  refine ⟨2284426594137697165739869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48734434008270872869117205 2284426594137697165739869)
                  ·
                    refine ⟨856659972801636437152451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2284426594137697165739869 856659972801636437152451)
                    ·
                      rfl

theorem cell22_2502509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_2502509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502509 prefixEnd_2502509 := by exact prefixLift 2502509
  have htrace : WordTrace (prefixWord ++ tailWord_2502509) baseStart_2502509 baseEnd_2502509 := by
    simpa [prefixWord, tailWord_2502509, baseEnd_2502509] using wordTrace_append hprefix tailTrace_2502509
  have hstable : (prefixWord ++ tailWord_2502509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502509).length < 2 ^ (prefixWord ++ tailWord_2502509).sum := by decide
  have hdescent : baseEnd_2502509 < baseStart_2502509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502556 : List Nat := [2, 2, 3, 3, 1, 2, 3, 6]
def baseStart_2502556 : Nat := 118140960795 + 2502556 * 2 ^ 59
def prefixEnd_2502556 : Nat := 4983230072969 + 3 ^ 40 * 2502556 * 2
def baseEnd_2502556 : Nat := 95186229095793775691923

theorem tailTrace_2502556 : CollatzResearch.WordTrace tailWord_2502556 prefixEnd_2502556 95186229095793775691923 := by
  unfold tailWord_2502556
  simp only [CollatzResearch.WordTrace]
  refine ⟨45637857960837244691327761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60850477281116326255103681 45637857960837244691327761)
  ·
    refine ⟨34228393470627933518495821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45637857960837244691327761 34228393470627933518495821)
    ·
      refine ⟨12835647551485475069435933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34228393470627933518495821 12835647551485475069435933)
      ·
        refine ⟨4813367831807053151038475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12835647551485475069435933 4813367831807053151038475)
        ·
          refine ⟨7220051747710579726557713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4813367831807053151038475 7220051747710579726557713)
          ·
            refine ⟨5415038810782934794918285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7220051747710579726557713 5415038810782934794918285)
            ·
              refine ⟨2030639554043600548094357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5415038810782934794918285 2030639554043600548094357)
              ·
                refine ⟨95186229095793775691923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2030639554043600548094357 95186229095793775691923)
                ·
                  rfl

theorem cell22_2502556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 6].length) (baseStart_2502556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502556 prefixEnd_2502556 := by exact prefixLift 2502556
  have htrace : WordTrace (prefixWord ++ tailWord_2502556) baseStart_2502556 baseEnd_2502556 := by
    simpa [prefixWord, tailWord_2502556, baseEnd_2502556] using wordTrace_append hprefix tailTrace_2502556
  have hstable : (prefixWord ++ tailWord_2502556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502556).length < 2 ^ (prefixWord ++ tailWord_2502556).sum := by decide
  have hdescent : baseEnd_2502556 < baseStart_2502556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502558 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2502558 : Nat := 118140960795 + 2502558 * 2 ^ 59
def prefixEnd_2502558 : Nat := 4983230072969 + 3 ^ 40 * 2502558 * 2
def baseEnd_2502558 : Nat := 856676746503016642677301

theorem tailTrace_2502558 : CollatzResearch.WordTrace tailWord_2502558 prefixEnd_2502558 856676746503016642677301 := by
  unfold tailWord_2502558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11409473608458405465528541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60850525911778162482818885 11409473608458405465528541)
  ·
    refine ⟨4278552603171902049573203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11409473608458405465528541 4278552603171902049573203)
    ·
      refine ⟨6417828904757853074359805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278552603171902049573203 6417828904757853074359805)
      ·
        refine ⟨2406685839284194902884927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6417828904757853074359805 2406685839284194902884927)
        ·
          refine ⟨3610028758926292354327391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406685839284194902884927 3610028758926292354327391)
          ·
            refine ⟨5415043138389438531491087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610028758926292354327391 5415043138389438531491087)
            ·
              refine ⟨8122564707584157797236631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5415043138389438531491087 8122564707584157797236631)
              ·
                refine ⟨12183847061376236695854947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8122564707584157797236631 12183847061376236695854947)
                ·
                  refine ⟨18275770592064355043782421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12183847061376236695854947 18275770592064355043782421)
                  ·
                    refine ⟨856676746503016642677301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18275770592064355043782421 856676746503016642677301)
                    ·
                      rfl

theorem cell22_2502558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2502558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502558 prefixEnd_2502558 := by exact prefixLift 2502558
  have htrace : WordTrace (prefixWord ++ tailWord_2502558) baseStart_2502558 baseEnd_2502558 := by
    simpa [prefixWord, tailWord_2502558, baseEnd_2502558] using wordTrace_append hprefix tailTrace_2502558
  have hstable : (prefixWord ++ tailWord_2502558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502558).length < 2 ^ (prefixWord ++ tailWord_2502558).sum := by decide
  have hdescent : baseEnd_2502558 < baseStart_2502558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502597 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_2502597 : Nat := 118140960795 + 2502597 * 2 ^ 59
def prefixEnd_2502597 : Nat := 4983230072969 + 3 ^ 40 * 2502597 * 2
def baseEnd_2502597 : Nat := 856690097000033540952181

theorem tailTrace_2502597 : CollatzResearch.WordTrace tailWord_2502597 prefixEnd_2502597 856690097000033540952181 := by
  unfold tailWord_2502597
  simp only [CollatzResearch.WordTrace]
  refine ⟨91277211314525953384898045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60851474209683968923265363 91277211314525953384898045)
  ·
    refine ⟨34228954242947232519336767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91277211314525953384898045 34228954242947232519336767)
    ·
      refine ⟨51343431364420848779005151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34228954242947232519336767 51343431364420848779005151)
      ·
        refine ⟨77015147046631273168507727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51343431364420848779005151 77015147046631273168507727)
        ·
          refine ⟨115522720569946909752761591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77015147046631273168507727 115522720569946909752761591)
          ·
            refine ⟨173284080854920364629142387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115522720569946909752761591 173284080854920364629142387)
            ·
              refine ⟨259926121282380546943713581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173284080854920364629142387 259926121282380546943713581)
              ·
                refine ⟨97472295480892705103892593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259926121282380546943713581 97472295480892705103892593)
                ·
                  refine ⟨73104221610669528827919445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97472295480892705103892593 73104221610669528827919445)
                  ·
                    refine ⟨856690097000033540952181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73104221610669528827919445 856690097000033540952181)
                    ·
                      rfl

theorem cell22_2502597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_2502597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502597 prefixEnd_2502597 := by exact prefixLift 2502597
  have htrace : WordTrace (prefixWord ++ tailWord_2502597) baseStart_2502597 baseEnd_2502597 := by
    simpa [prefixWord, tailWord_2502597, baseEnd_2502597] using wordTrace_append hprefix tailTrace_2502597
  have hstable : (prefixWord ++ tailWord_2502597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502597).length < 2 ^ (prefixWord ++ tailWord_2502597).sum := by decide
  have hdescent : baseEnd_2502597 < baseStart_2502597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502704 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_2502704 : Nat := 118140960795 + 2502704 * 2 ^ 59
def prefixEnd_2502704 : Nat := 4983230072969 + 3 ^ 40 * 2502704 * 2
def baseEnd_2502704 : Nat := 856726725286720928526853

theorem tailTrace_2502704 : CollatzResearch.WordTrace tailWord_2502704 prefixEnd_2502704 856726725286720928526853 := by
  unfold tailWord_2502704
  simp only [CollatzResearch.WordTrace]
  refine ⟨45640556962569155329521583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60854075950092207106028777 45640556962569155329521583)
  ·
    refine ⟨68460835443853732994282375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45640556962569155329521583 68460835443853732994282375)
    ·
      refine ⟨102691253165780599491423563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68460835443853732994282375 102691253165780599491423563)
      ·
        refine ⟨154036879748670899237135345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102691253165780599491423563 154036879748670899237135345)
        ·
          refine ⟨115527659811503174427851509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154036879748670899237135345 115527659811503174427851509)
          ·
            refine ⟨10830718107328422602611079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115527659811503174427851509 10830718107328422602611079)
            ·
              refine ⟨16246077160992633903916619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10830718107328422602611079 16246077160992633903916619)
              ·
                refine ⟨24369115741488950855874929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16246077160992633903916619 24369115741488950855874929)
                ·
                  refine ⟨18276836806116713141906197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24369115741488950855874929 18276836806116713141906197)
                  ·
                    refine ⟨856726725286720928526853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18276836806116713141906197 856726725286720928526853)
                    ·
                      rfl

theorem cell22_2502704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_2502704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502704 prefixEnd_2502704 := by exact prefixLift 2502704
  have htrace : WordTrace (prefixWord ++ tailWord_2502704) baseStart_2502704 baseEnd_2502704 := by
    simpa [prefixWord, tailWord_2502704, baseEnd_2502704] using wordTrace_append hprefix tailTrace_2502704
  have hstable : (prefixWord ++ tailWord_2502704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502704).length < 2 ^ (prefixWord ++ tailWord_2502704).sum := by decide
  have hdescent : baseEnd_2502704 < baseStart_2502704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502781 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 6]
def baseStart_2502781 : Nat := 118140960795 + 2502781 * 2 ^ 59
def prefixEnd_2502781 : Nat := 4983230072969 + 3 ^ 40 * 2502781 * 2
def baseEnd_2502781 : Nat := 285584361320106131450539

theorem tailTrace_2502781 : CollatzResearch.WordTrace tailWord_2502781 prefixEnd_2502781 285584361320106131450539 := by
  unfold tailWord_2502781
  simp only [CollatzResearch.WordTrace]
  refine ⟨91283922345859352809596197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60855948230572901873064131 91283922345859352809596197)
  ·
    refine ⟨17115735439848628651799287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91283922345859352809596197 17115735439848628651799287)
    ·
      refine ⟨25673603159772942977698931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17115735439848628651799287 25673603159772942977698931)
      ·
        refine ⟨38510404739659414466548397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25673603159772942977698931 38510404739659414466548397)
        ·
          refine ⟨14441401777372280424955649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38510404739659414466548397 14441401777372280424955649)
          ·
            refine ⟨10831051333029210318716737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14441401777372280424955649 10831051333029210318716737)
            ·
              refine ⟨8123288499771907739037553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10831051333029210318716737 8123288499771907739037553)
              ·
                refine ⟨6092466374828930804278165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8123288499771907739037553 6092466374828930804278165)
                ·
                  refine ⟨285584361320106131450539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6092466374828930804278165 285584361320106131450539)
                  ·
                    rfl

theorem cell22_2502781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_2502781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502781 prefixEnd_2502781 := by exact prefixLift 2502781
  have htrace : WordTrace (prefixWord ++ tailWord_2502781) baseStart_2502781 baseEnd_2502781 := by
    simpa [prefixWord, tailWord_2502781, baseEnd_2502781] using wordTrace_append hprefix tailTrace_2502781
  have hstable : (prefixWord ++ tailWord_2502781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502781).length < 2 ^ (prefixWord ++ tailWord_2502781).sum := by decide
  have hdescent : baseEnd_2502781 < baseStart_2502781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502813 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2502813 : Nat := 118140960795 + 2502813 * 2 ^ 59
def prefixEnd_2502813 : Nat := 4983230072969 + 3 ^ 40 * 2502813 * 2
def baseEnd_2502813 : Nat := 856764038214280977551519

theorem tailTrace_2502813 : CollatzResearch.WordTrace tailWord_2502813 prefixEnd_2502813 856764038214280977551519 := by
  unfold tailWord_2502813
  simp only [CollatzResearch.WordTrace]
  refine ⟨91285089481743422274761093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60856726321162281516507395 91285089481743422274761093)
  ·
    refine ⟨17115954277826891676517705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91285089481743422274761093 17115954277826891676517705)
    ·
      refine ⟨12836965708370168757388279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17115954277826891676517705 12836965708370168757388279)
      ·
        refine ⟨19255448562555253136082419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12836965708370168757388279 19255448562555253136082419)
        ·
          refine ⟨28883172843832879704123629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19255448562555253136082419 28883172843832879704123629)
          ·
            refine ⟨10831189816437329889046361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28883172843832879704123629 10831189816437329889046361)
            ·
              refine ⟨8123392362327997416784771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10831189816437329889046361 8123392362327997416784771)
              ·
                refine ⟨12185088543491996125177157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8123392362327997416784771 12185088543491996125177157)
                ·
                  refine ⟨2284704101904749273470717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12185088543491996125177157 2284704101904749273470717)
                  ·
                    refine ⟨856764038214280977551519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2284704101904749273470717 856764038214280977551519)
                    ·
                      rfl

theorem cell22_2502813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2502813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502813 prefixEnd_2502813 := by exact prefixLift 2502813
  have htrace : WordTrace (prefixWord ++ tailWord_2502813) baseStart_2502813 baseEnd_2502813 := by
    simpa [prefixWord, tailWord_2502813, baseEnd_2502813] using wordTrace_append hprefix tailTrace_2502813
  have hstable : (prefixWord ++ tailWord_2502813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502813).length < 2 ^ (prefixWord ++ tailWord_2502813).sum := by decide
  have hdescent : baseEnd_2502813 < baseStart_2502813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502888 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 5]
def baseStart_2502888 : Nat := 118140960795 + 2502888 * 2 ^ 59
def prefixEnd_2502888 : Nat := 4983230072969 + 3 ^ 40 * 2502888 * 2
def baseEnd_2502888 : Nat := 285596570749001927308763

theorem tailTrace_2502888 : CollatzResearch.WordTrace tailWord_2502888 prefixEnd_2502888 285596570749001927308763 := by
  unfold tailWord_2502888
  simp only [CollatzResearch.WordTrace]
  refine ⟨45643912478235855041870659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60858549970981140055827545 45643912478235855041870659)
  ·
    refine ⟨68465868717353782562805989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45643912478235855041870659 68465868717353782562805989)
    ·
      refine ⟨12837350384503834230526123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68465868717353782562805989 12837350384503834230526123)
      ·
        refine ⟨19256025576755751345789185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12837350384503834230526123 19256025576755751345789185)
        ·
          refine ⟨14442019182566813509341889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19256025576755751345789185 14442019182566813509341889)
          ·
            refine ⟨10831514386925110132006417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14442019182566813509341889 10831514386925110132006417)
            ·
              refine ⟨8123635790193832599004813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10831514386925110132006417 8123635790193832599004813)
              ·
                refine ⟨3046363421322687224626805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8123635790193832599004813 3046363421322687224626805)
                ·
                  refine ⟨285596570749001927308763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3046363421322687224626805 285596570749001927308763)
                  ·
                    rfl

theorem cell22_2502888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_2502888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502888 prefixEnd_2502888 := by exact prefixLift 2502888
  have htrace : WordTrace (prefixWord ++ tailWord_2502888) baseStart_2502888 baseEnd_2502888 := by
    simpa [prefixWord, tailWord_2502888, baseEnd_2502888] using wordTrace_append hprefix tailTrace_2502888
  have hstable : (prefixWord ++ tailWord_2502888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502888).length < 2 ^ (prefixWord ++ tailWord_2502888).sum := by decide
  have hdescent : baseEnd_2502888 < baseStart_2502888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502931 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 3, 5]
def baseStart_2502931 : Nat := 118140960795 + 2502931 * 2 ^ 59
def prefixEnd_2502931 : Nat := 4983230072969 + 3 ^ 40 * 2502931 * 2
def baseEnd_2502931 : Nat := 856804432025768003101157

theorem tailTrace_2502931 : CollatzResearch.WordTrace tailWord_2502931 prefixEnd_2502931 856804432025768003101157 := by
  unfold tailWord_2502931
  simp only [CollatzResearch.WordTrace]
  refine ⟨91289393295315928427556647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60859595530210618951704431 91289393295315928427556647)
  ·
    refine ⟨136934089942973892641334971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91289393295315928427556647 136934089942973892641334971)
    ·
      refine ⟨205401134914460838962002457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136934089942973892641334971 205401134914460838962002457)
      ·
        refine ⟨154050851185845629221501843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205401134914460838962002457 154050851185845629221501843)
        ·
          refine ⟨231076276778768443832252765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154050851185845629221501843 231076276778768443832252765)
          ·
            refine ⟨86653603792038166437094787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231076276778768443832252765 86653603792038166437094787)
            ·
              refine ⟨129980405688057249655642181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86653603792038166437094787 129980405688057249655642181)
              ·
                refine ⟨24371326066510734310432909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129980405688057249655642181 24371326066510734310432909)
                ·
                  refine ⟨9139247274941525366412341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24371326066510734310432909 9139247274941525366412341)
                  ·
                    refine ⟨856804432025768003101157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9139247274941525366412341 856804432025768003101157)
                    ·
                      rfl

theorem cell22_2502931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_2502931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502931 prefixEnd_2502931 := by exact prefixLift 2502931
  have htrace : WordTrace (prefixWord ++ tailWord_2502931) baseStart_2502931 baseEnd_2502931 := by
    simpa [prefixWord, tailWord_2502931, baseEnd_2502931] using wordTrace_append hprefix tailTrace_2502931
  have hstable : (prefixWord ++ tailWord_2502931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502931).length < 2 ^ (prefixWord ++ tailWord_2502931).sum := by decide
  have hdescent : baseEnd_2502931 < baseStart_2502931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502952 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2502952 : Nat := 118140960795 + 2502952 * 2 ^ 59
def prefixEnd_2502952 : Nat := 4983230072969 + 3 ^ 40 * 2502952 * 2
def baseEnd_2502952 : Nat := 856811620754930948326093

theorem tailTrace_2502952 : CollatzResearch.WordTrace tailWord_2502952 prefixEnd_2502952 856811620754930948326093 := by
  unfold tailWord_2502952
  simp only [CollatzResearch.WordTrace]
  refine ⟨45645079614119924507035555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60860106152159899342714073 45645079614119924507035555)
  ·
    refine ⟨68467619421179886760553333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45645079614119924507035555 68467619421179886760553333)
    ·
      refine ⟨6418839320735614383801875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68467619421179886760553333 6418839320735614383801875)
      ·
        refine ⟨9628258981103421575702813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6418839320735614383801875 9628258981103421575702813)
        ·
          refine ⟨3610597117913783090888555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9628258981103421575702813 3610597117913783090888555)
          ·
            refine ⟨5415895676870674636332833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610597117913783090888555 5415895676870674636332833)
            ·
              refine ⟨4061921757653005977249625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5415895676870674636332833 4061921757653005977249625)
              ·
                refine ⟨3046441318239754482937219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4061921757653005977249625 3046441318239754482937219)
                ·
                  refine ⟨4569661977359631724405829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046441318239754482937219 4569661977359631724405829)
                  ·
                    refine ⟨856811620754930948326093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4569661977359631724405829 856811620754930948326093)
                    ·
                      rfl

theorem cell22_2502952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2502952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502952 prefixEnd_2502952 := by exact prefixLift 2502952
  have htrace : WordTrace (prefixWord ++ tailWord_2502952) baseStart_2502952 baseEnd_2502952 := by
    simpa [prefixWord, tailWord_2502952, baseEnd_2502952] using wordTrace_append hprefix tailTrace_2502952
  have hstable : (prefixWord ++ tailWord_2502952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502952).length < 2 ^ (prefixWord ++ tailWord_2502952).sum := by decide
  have hdescent : baseEnd_2502952 < baseStart_2502952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2502963 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 2, 4]
def baseStart_2502963 : Nat := 118140960795 + 2502963 * 2 ^ 59
def prefixEnd_2502963 : Nat := 4983230072969 + 3 ^ 40 * 2502963 * 2
def baseEnd_2502963 : Nat := 856815386279730586301059

theorem tailTrace_2502963 : CollatzResearch.WordTrace tailWord_2502963 prefixEnd_2502963 856815386279730586301059 := by
  unfold tailWord_2502963
  simp only [CollatzResearch.WordTrace]
  refine ⟨91290560431199997892721543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60860373620799998595147695 91290560431199997892721543)
  ·
    refine ⟨136935840646799996839082315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91290560431199997892721543 136935840646799996839082315)
    ·
      refine ⟨205403760970199995258623473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136935840646799996839082315 205403760970199995258623473)
      ·
        refine ⟨154052820727649996443967605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205403760970199995258623473 154052820727649996443967605)
        ·
          refine ⟨14442451943217187166621963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154052820727649996443967605 14442451943217187166621963)
          ·
            refine ⟨21663677914825780749932945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14442451943217187166621963 21663677914825780749932945)
            ·
              refine ⟨16247758436119335562449709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21663677914825780749932945 16247758436119335562449709)
              ·
                refine ⟨6092909413544750835918641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16247758436119335562449709 6092909413544750835918641)
                ·
                  refine ⟨4569682060158563126938981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6092909413544750835918641 4569682060158563126938981)
                  ·
                    refine ⟨856815386279730586301059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4569682060158563126938981 856815386279730586301059)
                    ·
                      rfl

theorem cell22_2502963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 4].length) (baseStart_2502963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2502963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2502963 prefixEnd_2502963 := by exact prefixLift 2502963
  have htrace : WordTrace (prefixWord ++ tailWord_2502963) baseStart_2502963 baseEnd_2502963 := by
    simpa [prefixWord, tailWord_2502963, baseEnd_2502963] using wordTrace_append hprefix tailTrace_2502963
  have hstable : (prefixWord ++ tailWord_2502963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2502963).length < 2 ^ (prefixWord ++ tailWord_2502963).sum := by decide
  have hdescent : baseEnd_2502963 < baseStart_2502963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2502963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503102 : List Nat := [4, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_2503102 : Nat := 118140960795 + 2503102 * 2 ^ 59
def prefixEnd_2503102 : Nat := 4983230072969 + 3 ^ 40 * 2503102 * 2
def baseEnd_2503102 : Nat := 285620989606793519025211

theorem tailTrace_2503102 : CollatzResearch.WordTrace tailWord_2503102 prefixEnd_2503102 285620989606793519025211 := by
  unfold tailWord_2503102
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411953772212053079003945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60863753451797616421354373 11411953772212053079003945)
  ·
    refine ⟨8558965329159039809252959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11411953772212053079003945 8558965329159039809252959)
    ·
      refine ⟨12838447993738559713879439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8558965329159039809252959 12838447993738559713879439)
      ·
        refine ⟨19257671990607839570819159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12838447993738559713879439 19257671990607839570819159)
        ·
          refine ⟨28886507985911759356228739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19257671990607839570819159 28886507985911759356228739)
          ·
            refine ⟨43329761978867639034343109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28886507985911759356228739 43329761978867639034343109)
            ·
              refine ⟨8124330371037682318939333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43329761978867639034343109 8124330371037682318939333)
              ·
                refine ⟨1523311944569565434801125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8124330371037682318939333 1523311944569565434801125)
                ·
                  refine ⟨285620989606793519025211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523311944569565434801125 285620989606793519025211)
                  ·
                    rfl

theorem cell22_2503102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_2503102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503102 prefixEnd_2503102 := by exact prefixLift 2503102
  have htrace : WordTrace (prefixWord ++ tailWord_2503102) baseStart_2503102 baseEnd_2503102 := by
    simpa [prefixWord, tailWord_2503102, baseEnd_2503102] using wordTrace_append hprefix tailTrace_2503102
  have hstable : (prefixWord ++ tailWord_2503102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503102).length < 2 ^ (prefixWord ++ tailWord_2503102).sum := by decide
  have hdescent : baseEnd_2503102 < baseStart_2503102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503128 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_2503128 : Nat := 118140960795 + 2503128 * 2 ^ 59
def prefixEnd_2503128 : Nat := 4983230072969 + 3 ^ 40 * 2503128 * 2
def baseEnd_2503128 : Nat := 856871869151725155925553

theorem tailTrace_2503128 : CollatzResearch.WordTrace tailWord_2503128 prefixEnd_2503128 856871869151725155925553 := by
  unfold tailWord_2503128
  simp only [CollatzResearch.WordTrace]
  refine ⟨45648289237801115536239019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60864385650401487381652025 45648289237801115536239019)
  ·
    refine ⟨68472433856701673304358529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45648289237801115536239019 68472433856701673304358529)
    ·
      refine ⟨51354325392526254978268897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68472433856701673304358529 51354325392526254978268897)
      ·
        refine ⟨38515744044394691233701673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51354325392526254978268897 38515744044394691233701673)
        ·
          refine ⟨28886808033296018425276255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38515744044394691233701673 28886808033296018425276255)
          ·
            refine ⟨43330212049944027637914383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28886808033296018425276255 43330212049944027637914383)
            ·
              refine ⟨64995318074916041456871575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43330212049944027637914383 64995318074916041456871575)
              ·
                refine ⟨97492977112374062185307363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64995318074916041456871575 97492977112374062185307363)
                ·
                  refine ⟨146239465668561093277961045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97492977112374062185307363 146239465668561093277961045)
                  ·
                    refine ⟨856871869151725155925553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 146239465668561093277961045 856871869151725155925553)
                    ·
                      rfl

theorem cell22_2503128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_2503128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503128 prefixEnd_2503128 := by exact prefixLift 2503128
  have htrace : WordTrace (prefixWord ++ tailWord_2503128) baseStart_2503128 baseEnd_2503128 := by
    simpa [prefixWord, tailWord_2503128, baseEnd_2503128] using wordTrace_append hprefix tailTrace_2503128
  have hstable : (prefixWord ++ tailWord_2503128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503128).length < 2 ^ (prefixWord ++ tailWord_2503128).sum := by decide
  have hdescent : baseEnd_2503128 < baseStart_2503128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503252 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2503252 : Nat := 118140960795 + 2503252 * 2 ^ 59
def prefixEnd_2503252 : Nat := 4983230072969 + 3 ^ 40 * 2503252 * 2
def baseEnd_2503252 : Nat := 856914316885830165825173

theorem tailTrace_2503252 : CollatzResearch.WordTrace tailWord_2503252 prefixEnd_2503252 856914316885830165825173 := by
  unfold tailWord_2503252
  simp only [CollatzResearch.WordTrace]
  refine ⟨45650550563576500124996005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60867400751435333499994673 45650550563576500124996005)
  ·
    refine ⟨8559478230670593773436751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45650550563576500124996005 8559478230670593773436751)
    ·
      refine ⟨12839217346005890660155127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8559478230670593773436751 12839217346005890660155127)
      ·
        refine ⟨19258826019008835990232691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12839217346005890660155127 19258826019008835990232691)
        ·
          refine ⟨28888239028513253985349037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19258826019008835990232691 28888239028513253985349037)
          ·
            refine ⟨10833089635692470244505889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28888239028513253985349037 10833089635692470244505889)
            ·
              refine ⟨8124817226769352683379417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10833089635692470244505889 8124817226769352683379417)
              ·
                refine ⟨6093612920077014512534563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8124817226769352683379417 6093612920077014512534563)
                ·
                  refine ⟨9140419380115521768801845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6093612920077014512534563 9140419380115521768801845)
                  ·
                    refine ⟨856914316885830165825173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9140419380115521768801845 856914316885830165825173)
                    ·
                      rfl

theorem cell22_2503252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2503252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503252 prefixEnd_2503252 := by exact prefixLift 2503252
  have htrace : WordTrace (prefixWord ++ tailWord_2503252) baseStart_2503252 baseEnd_2503252 := by
    simpa [prefixWord, tailWord_2503252, baseEnd_2503252] using wordTrace_append hprefix tailTrace_2503252
  have hstable : (prefixWord ++ tailWord_2503252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503252).length < 2 ^ (prefixWord ++ tailWord_2503252).sum := by decide
  have hdescent : baseEnd_2503252 < baseStart_2503252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503265 : List Nat := [1, 2, 3, 1, 1, 5, 9]
def baseStart_2503265 : Nat := 118140960795 + 2503265 * 2 ^ 59
def prefixEnd_2503265 : Nat := 4983230072969 + 3 ^ 40 * 2503265 * 2
def baseEnd_2503265 : Nat := 31737732113018609824079

theorem tailTrace_2503265 : CollatzResearch.WordTrace tailWord_2503265 prefixEnd_2503265 31737732113018609824079 := by
  unfold tailWord_2503265
  simp only [CollatzResearch.WordTrace]
  refine ⟨91301575276105903470215249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60867716850737268980143499 91301575276105903470215249)
  ·
    refine ⟨68476181457079427602661437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91301575276105903470215249 68476181457079427602661437)
    ·
      refine ⟨25678568046404785350998039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68476181457079427602661437 25678568046404785350998039)
      ·
        refine ⟨38517852069607178026497059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25678568046404785350998039 38517852069607178026497059)
        ·
          refine ⟨57776778104410767039745589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38517852069607178026497059 57776778104410767039745589)
          ·
            refine ⟨5416572947288509409976149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57776778104410767039745589 5416572947288509409976149)
            ·
              refine ⟨31737732113018609824079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5416572947288509409976149 31737732113018609824079)
              ·
                rfl

theorem cell22_2503265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 9].length) (baseStart_2503265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503265 prefixEnd_2503265 := by exact prefixLift 2503265
  have htrace : WordTrace (prefixWord ++ tailWord_2503265) baseStart_2503265 baseEnd_2503265 := by
    simpa [prefixWord, tailWord_2503265, baseEnd_2503265] using wordTrace_append hprefix tailTrace_2503265
  have hstable : (prefixWord ++ tailWord_2503265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503265).length < 2 ^ (prefixWord ++ tailWord_2503265).sum := by decide
  have hdescent : baseEnd_2503265 < baseStart_2503265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503269 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_2503269 : Nat := 118140960795 + 2503269 * 2 ^ 59
def prefixEnd_2503269 : Nat := 4983230072969 + 3 ^ 40 * 2503269 * 2
def baseEnd_2503269 : Nat := 856920136333247788150121

theorem tailTrace_2503269 : CollatzResearch.WordTrace tailWord_2503269 prefixEnd_2503269 856920136333247788150121 := by
  unfold tailWord_2503269
  simp only [CollatzResearch.WordTrace]
  refine ⟨91301721168091412153360861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60867814112060941435573907 91301721168091412153360861)
  ·
    refine ⟨34238145438034279557510323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91301721168091412153360861 34238145438034279557510323)
    ·
      refine ⟨51357218157051419336265485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34238145438034279557510323 51357218157051419336265485)
      ·
        refine ⟨19258956808894282251099557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51357218157051419336265485 19258956808894282251099557)
        ·
          refine ⟨3611054401667677922081167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19258956808894282251099557 3611054401667677922081167)
          ·
            refine ⟨5416581602501516883121751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611054401667677922081167 5416581602501516883121751)
            ·
              refine ⟨8124872403752275324682627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5416581602501516883121751 8124872403752275324682627)
              ·
                refine ⟨12187308605628412987023941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8124872403752275324682627 12187308605628412987023941)
                ·
                  refine ⟨2285120363555327435066989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12187308605628412987023941 2285120363555327435066989)
                  ·
                    refine ⟨856920136333247788150121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2285120363555327435066989 856920136333247788150121)
                    ·
                      rfl

theorem cell22_2503269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_2503269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503269 prefixEnd_2503269 := by exact prefixLift 2503269
  have htrace : WordTrace (prefixWord ++ tailWord_2503269) baseStart_2503269 baseEnd_2503269 := by
    simpa [prefixWord, tailWord_2503269, baseEnd_2503269] using wordTrace_append hprefix tailTrace_2503269
  have hstable : (prefixWord ++ tailWord_2503269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503269).length < 2 ^ (prefixWord ++ tailWord_2503269).sum := by decide
  have hdescent : baseEnd_2503269 < baseStart_2503269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503286 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_2503286 : Nat := 118140960795 + 2503286 * 2 ^ 59
def prefixEnd_2503286 : Nat := 4983230072969 + 3 ^ 40 * 2503286 * 2
def baseEnd_2503286 : Nat := 856925955780665410475069

theorem tailTrace_2503286 : CollatzResearch.WordTrace tailWord_2503286 prefixEnd_2503286 856925955780665410475069 := by
  unfold tailWord_2503286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5706396325564364003545607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60868227472686549371153141 5706396325564364003545607)
  ·
    refine ⟨8559594488346546005318411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5706396325564364003545607 8559594488346546005318411)
    ·
      refine ⟨12839391732519819007977617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8559594488346546005318411 12839391732519819007977617)
      ·
        refine ⟨9629543799389864255983213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12839391732519819007977617 9629543799389864255983213)
        ·
          refine ⟨3611078924771199095993705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9629543799389864255983213 3611078924771199095993705)
          ·
            refine ⟨2708309193578399321995279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3611078924771199095993705 2708309193578399321995279)
            ·
              refine ⟨4062463790367598982992919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708309193578399321995279 4062463790367598982992919)
              ·
                refine ⟨6093695685551398474489379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4062463790367598982992919 6093695685551398474489379)
                ·
                  refine ⟨9140543528327097711734069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6093695685551398474489379 9140543528327097711734069)
                  ·
                    refine ⟨856925955780665410475069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9140543528327097711734069 856925955780665410475069)
                    ·
                      rfl

theorem cell22_2503286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_2503286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503286 prefixEnd_2503286 := by exact prefixLift 2503286
  have htrace : WordTrace (prefixWord ++ tailWord_2503286) baseStart_2503286 baseEnd_2503286 := by
    simpa [prefixWord, tailWord_2503286, baseEnd_2503286] using wordTrace_append hprefix tailTrace_2503286
  have hstable : (prefixWord ++ tailWord_2503286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503286).length < 2 ^ (prefixWord ++ tailWord_2503286).sum := by decide
  have hdescent : baseEnd_2503286 < baseStart_2503286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503402 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2503402 : Nat := 118140960795 + 2503402 * 2 ^ 59
def prefixEnd_2503402 : Nat := 4983230072969 + 3 ^ 40 * 2503402 * 2
def baseEnd_2503402 : Nat := 856965664951279774574713

theorem tailTrace_2503402 : CollatzResearch.WordTrace tailWord_2503402 prefixEnd_2503402 856965664951279774574713 := by
  unfold tailWord_2503402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22826643019152393966988115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60871048051073050578634973 22826643019152393966988115)
  ·
    refine ⟨34239964528728590950482173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22826643019152393966988115 34239964528728590950482173)
    ·
      refine ⟨12839986698273221606430815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34239964528728590950482173 12839986698273221606430815)
      ·
        refine ⟨19259980047409832409646223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12839986698273221606430815 19259980047409832409646223)
        ·
          refine ⟨28889970071114748614469335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19259980047409832409646223 28889970071114748614469335)
          ·
            refine ⟨43334955106672122921704003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28889970071114748614469335 43334955106672122921704003)
            ·
              refine ⟨65002432660008184382556005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43334955106672122921704003 65002432660008184382556005)
              ·
                refine ⟨12187956123751534571729251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65002432660008184382556005 12187956123751534571729251)
                ·
                  refine ⟨18281934185627301857593877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12187956123751534571729251 18281934185627301857593877)
                  ·
                    refine ⟨856965664951279774574713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18281934185627301857593877 856965664951279774574713)
                    ·
                      rfl

theorem cell22_2503402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2503402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503402 prefixEnd_2503402 := by exact prefixLift 2503402
  have htrace : WordTrace (prefixWord ++ tailWord_2503402) baseStart_2503402 baseEnd_2503402 := by
    simpa [prefixWord, tailWord_2503402, baseEnd_2503402] using wordTrace_append hprefix tailTrace_2503402
  have hstable : (prefixWord ++ tailWord_2503402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503402).length < 2 ^ (prefixWord ++ tailWord_2503402).sum := by decide
  have hdescent : baseEnd_2503402 < baseStart_2503402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503500 : List Nat := [2, 2, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_2503500 : Nat := 118140960795 + 2503500 * 2 ^ 59
def prefixEnd_2503500 : Nat := 4983230072969 + 3 ^ 40 * 2503500 * 2
def baseEnd_2503500 : Nat := 856999212354040185624413

theorem tailTrace_2503500 : CollatzResearch.WordTrace tailWord_2503500 prefixEnd_2503500 856999212354040185624413 := by
  unfold tailWord_2503500
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655073215127269302509977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60873430953503025736679969 45655073215127269302509977)
  ·
    refine ⟨34241304911345451976882483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45655073215127269302509977 34241304911345451976882483)
    ·
      refine ⟨51361957367018177965323725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34241304911345451976882483 51361957367018177965323725)
      ·
        refine ⟨19260734012631816736996397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51361957367018177965323725 19260734012631816736996397)
        ·
          refine ⟨7222775254736931276373649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19260734012631816736996397 7222775254736931276373649)
          ·
            refine ⟨5417081441052698457280237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7222775254736931276373649 5417081441052698457280237)
            ·
              refine ⟨2031405540394761921480089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5417081441052698457280237 2031405540394761921480089)
              ·
                refine ⟨1523554155296071441110067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031405540394761921480089 1523554155296071441110067)
                ·
                  refine ⟨2285331232944107161665101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523554155296071441110067 2285331232944107161665101)
                  ·
                    refine ⟨856999212354040185624413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2285331232944107161665101 856999212354040185624413)
                    ·
                      rfl

theorem cell22_2503500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_2503500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503500 prefixEnd_2503500 := by exact prefixLift 2503500
  have htrace : WordTrace (prefixWord ++ tailWord_2503500) baseStart_2503500 baseEnd_2503500 := by
    simpa [prefixWord, tailWord_2503500, baseEnd_2503500] using wordTrace_append hprefix tailTrace_2503500
  have hstable : (prefixWord ++ tailWord_2503500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503500).length < 2 ^ (prefixWord ++ tailWord_2503500).sum := by decide
  have hdescent : baseEnd_2503500 < baseStart_2503500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503509 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_2503509 : Nat := 118140960795 + 2503509 * 2 ^ 59
def prefixEnd_2503509 : Nat := 4983230072969 + 3 ^ 40 * 2503509 * 2
def baseEnd_2503509 : Nat := 857002293237967162149385

theorem tailTrace_2503509 : CollatzResearch.WordTrace tailWord_2503509 prefixEnd_2503509 857002293237967162149385 := by
  unfold tailWord_2503509
  simp only [CollatzResearch.WordTrace]
  refine ⟨91310474687221933142097581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60873649791481288761398387 91310474687221933142097581)
  ·
    refine ⟨34241428007708224928286593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91310474687221933142097581 34241428007708224928286593)
    ·
      refine ⟨25681071005781168696214945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34241428007708224928286593 25681071005781168696214945)
      ·
        refine ⟨19260803254335876522161209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25681071005781168696214945 19260803254335876522161209)
        ·
          refine ⟨14445602440751907391620907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19260803254335876522161209 14445602440751907391620907)
          ·
            refine ⟨21668403661127861087431361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14445602440751907391620907 21668403661127861087431361)
            ·
              refine ⟨16251302745845895815573521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21668403661127861087431361 16251302745845895815573521)
              ·
                refine ⟨12188477059384421861680141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16251302745845895815573521 12188477059384421861680141)
                ·
                  refine ⟨4570678897269158198130053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12188477059384421861680141 4570678897269158198130053)
                  ·
                    refine ⟨857002293237967162149385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4570678897269158198130053 857002293237967162149385)
                    ·
                      rfl

theorem cell22_2503509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_2503509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503509 prefixEnd_2503509 := by exact prefixLift 2503509
  have htrace : WordTrace (prefixWord ++ tailWord_2503509) baseStart_2503509 baseEnd_2503509 := by
    simpa [prefixWord, tailWord_2503509, baseEnd_2503509] using wordTrace_append hprefix tailTrace_2503509
  have hstable : (prefixWord ++ tailWord_2503509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503509).length < 2 ^ (prefixWord ++ tailWord_2503509).sum := by decide
  have hdescent : baseEnd_2503509 < baseStart_2503509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503539 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 6, 3]
def baseStart_2503539 : Nat := 118140960795 + 2503539 * 2 ^ 59
def prefixEnd_2503539 : Nat := 4983230072969 + 3 ^ 40 * 2503539 * 2
def baseEnd_2503539 : Nat := 857012562851057083899293

theorem tailTrace_2503539 : CollatzResearch.WordTrace tailWord_2503539 prefixEnd_2503539 857012562851057083899293 := by
  unfold tailWord_2503539
  simp only [CollatzResearch.WordTrace]
  refine ⟨91311568877113248265689671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60874379251408832177126447 91311568877113248265689671)
  ·
    refine ⟨136967353315669872398534507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91311568877113248265689671 136967353315669872398534507)
    ·
      refine ⟨205451029973504808597801761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136967353315669872398534507 205451029973504808597801761)
      ·
        refine ⟨154088272480128606448351321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205451029973504808597801761 154088272480128606448351321)
        ·
          refine ⟨115566204360096454836263491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154088272480128606448351321 115566204360096454836263491)
          ·
            refine ⟨173349306540144682254395237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115566204360096454836263491 173349306540144682254395237)
            ·
              refine ⟨32502994976277127922699107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173349306540144682254395237 32502994976277127922699107)
              ·
                refine ⟨48754492464415691884048661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32502994976277127922699107 48754492464415691884048661)
                ·
                  refine ⟨2285366834269485557064781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48754492464415691884048661 2285366834269485557064781)
                  ·
                    refine ⟨857012562851057083899293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2285366834269485557064781 857012562851057083899293)
                    ·
                      rfl

theorem cell22_2503539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 3].length) (baseStart_2503539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503539 prefixEnd_2503539 := by exact prefixLift 2503539
  have htrace : WordTrace (prefixWord ++ tailWord_2503539) baseStart_2503539 baseEnd_2503539 := by
    simpa [prefixWord, tailWord_2503539, baseEnd_2503539] using wordTrace_append hprefix tailTrace_2503539
  have hstable : (prefixWord ++ tailWord_2503539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503539).length < 2 ^ (prefixWord ++ tailWord_2503539).sum := by decide
  have hdescent : baseEnd_2503539 < baseStart_2503539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503669 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2503669 : Nat := 118140960795 + 2503669 * 2 ^ 59
def prefixEnd_2503669 : Nat := 4983230072969 + 3 ^ 40 * 2503669 * 2
def baseEnd_2503669 : Nat := 857057064507780078148895

theorem tailTrace_2503669 : CollatzResearch.WordTrace tailWord_2503669 prefixEnd_2503669 857057064507780078148895 := by
  unfold tailWord_2503669
  simp only [CollatzResearch.WordTrace]
  refine ⟨91316310366642280467922061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60877540244428186978614707 91316310366642280467922061)
  ·
    refine ⟨34243616387490855175470773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91316310366642280467922061 34243616387490855175470773)
    ·
      refine ⟨3210339036327267672700385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34243616387490855175470773 3210339036327267672700385)
      ·
        refine ⟨2407754277245450754525289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3210339036327267672700385 2407754277245450754525289)
        ·
          refine ⟨1805815707934088065893967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407754277245450754525289 1805815707934088065893967)
          ·
            refine ⟨2708723561901132098840951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805815707934088065893967 2708723561901132098840951)
            ·
              refine ⟨4063085342851698148261427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708723561901132098840951 4063085342851698148261427)
              ·
                refine ⟨6094628014277547222392141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063085342851698148261427 6094628014277547222392141)
                ·
                  refine ⟨2285485505354080208397053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6094628014277547222392141 2285485505354080208397053)
                  ·
                    refine ⟨857057064507780078148895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2285485505354080208397053 857057064507780078148895)
                    ·
                      rfl

theorem cell22_2503669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2503669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503669 prefixEnd_2503669 := by exact prefixLift 2503669
  have htrace : WordTrace (prefixWord ++ tailWord_2503669) baseStart_2503669 baseEnd_2503669 := by
    simpa [prefixWord, tailWord_2503669, baseEnd_2503669] using wordTrace_append hprefix tailTrace_2503669
  have hstable : (prefixWord ++ tailWord_2503669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503669).length < 2 ^ (prefixWord ++ tailWord_2503669).sum := by decide
  have hdescent : baseEnd_2503669 < baseStart_2503669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503676 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 6]
def baseStart_2503676 : Nat := 118140960795 + 2503676 * 2 ^ 59
def prefixEnd_2503676 : Nat := 4983230072969 + 3 ^ 40 * 2503676 * 2
def baseEnd_2503676 : Nat := 285686486916944797741291

theorem tailTrace_2503676 : CollatzResearch.WordTrace tailWord_2503676 prefixEnd_2503676 285686486916944797741291 := by
  unfold tailWord_2503676
  simp only [CollatzResearch.WordTrace]
  refine ⟨45658282838808460331713441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60877710451744613775617921 45658282838808460331713441)
  ·
    refine ⟨34243712129106345248785081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45658282838808460331713441 34243712129106345248785081)
    ·
      refine ⟨25682784096829758936588811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34243712129106345248785081 25682784096829758936588811)
      ·
        refine ⟨38524176145244638404883217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25682784096829758936588811 38524176145244638404883217)
        ·
          refine ⟨28893132108933478803662413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38524176145244638404883217 28893132108933478803662413)
          ·
            refine ⟨10834924540850054551373405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28893132108933478803662413 10834924540850054551373405)
            ·
              refine ⟨4063096702818770456765027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10834924540850054551373405 4063096702818770456765027)
              ·
                refine ⟨6094645054228155685147541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063096702818770456765027 6094645054228155685147541)
                ·
                  refine ⟨285686486916944797741291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6094645054228155685147541 285686486916944797741291)
                  ·
                    rfl

theorem cell22_2503676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_2503676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503676 prefixEnd_2503676 := by exact prefixLift 2503676
  have htrace : WordTrace (prefixWord ++ tailWord_2503676) baseStart_2503676 baseEnd_2503676 := by
    simpa [prefixWord, tailWord_2503676, baseEnd_2503676] using wordTrace_append hprefix tailTrace_2503676
  have hstable : (prefixWord ++ tailWord_2503676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503676).length < 2 ^ (prefixWord ++ tailWord_2503676).sum := by decide
  have hdescent : baseEnd_2503676 < baseStart_2503676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503689 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_2503689 : Nat := 118140960795 + 2503689 * 2 ^ 59
def prefixEnd_2503689 : Nat := 4983230072969 + 3 ^ 40 * 2503689 * 2
def baseEnd_2503689 : Nat := 857063910916506692648833

theorem tailTrace_2503689 : CollatzResearch.WordTrace tailWord_2503689 prefixEnd_2503689 857063910916506692648833 := by
  unfold tailWord_2503689
  simp only [CollatzResearch.WordTrace]
  refine ⟨91317039826569823883650121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60878026551046549255766747 91317039826569823883650121)
  ·
    refine ⟨68487779869927367912737591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91317039826569823883650121 68487779869927367912737591)
    ·
      refine ⟨102731669804891051869106387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68487779869927367912737591 102731669804891051869106387)
      ·
        refine ⟨154097504707336577803659581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102731669804891051869106387 154097504707336577803659581)
        ·
          refine ⟨57786564265251216676372343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154097504707336577803659581 57786564265251216676372343)
          ·
            refine ⟨86679846397876825014558515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57786564265251216676372343 86679846397876825014558515)
            ·
              refine ⟨130019769596815237521837773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86679846397876825014558515 130019769596815237521837773)
              ·
                refine ⟨48757413598805714070689165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130019769596815237521837773 48757413598805714070689165)
                ·
                  refine ⟨18284030099552142776508437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48757413598805714070689165 18284030099552142776508437)
                  ·
                    refine ⟨857063910916506692648833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18284030099552142776508437 857063910916506692648833)
                    ·
                      rfl

theorem cell22_2503689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_2503689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503689 prefixEnd_2503689 := by exact prefixLift 2503689
  have htrace : WordTrace (prefixWord ++ tailWord_2503689) baseStart_2503689 baseEnd_2503689 := by
    simpa [prefixWord, tailWord_2503689, baseEnd_2503689] using wordTrace_append hprefix tailTrace_2503689
  have hstable : (prefixWord ++ tailWord_2503689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503689).length < 2 ^ (prefixWord ++ tailWord_2503689).sum := by decide
  have hdescent : baseEnd_2503689 < baseStart_2503689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503708 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_2503708 : Nat := 118140960795 + 2503708 * 2 ^ 59
def prefixEnd_2503708 : Nat := 4983230072969 + 3 ^ 40 * 2503708 * 2
def baseEnd_2503708 : Nat := 857070415004796976423775

theorem tailTrace_2503708 : CollatzResearch.WordTrace tailWord_2503708 prefixEnd_2503708 857070415004796976423775 := by
  unfold tailWord_2503708
  simp only [CollatzResearch.WordTrace]
  refine ⟨45658866406750495064295889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60878488542333993419061185 45658866406750495064295889)
  ·
    refine ⟨34244149805062871298221917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45658866406750495064295889 34244149805062871298221917)
    ·
      refine ⟨12841556176898576736833219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34244149805062871298221917 12841556176898576736833219)
      ·
        refine ⟨19262334265347865105249829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12841556176898576736833219 19262334265347865105249829)
        ·
          refine ⟨3611687674752724707234343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19262334265347865105249829 3611687674752724707234343)
          ·
            refine ⟨5417531512129087060851515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611687674752724707234343 5417531512129087060851515)
            ·
              refine ⟨8126297268193630591277273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417531512129087060851515 8126297268193630591277273)
              ·
                refine ⟨6094722951145222943457955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8126297268193630591277273 6094722951145222943457955)
                ·
                  refine ⟨9142084426717834415186933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6094722951145222943457955 9142084426717834415186933)
                  ·
                    refine ⟨857070415004796976423775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9142084426717834415186933 857070415004796976423775)
                    ·
                      rfl

theorem cell22_2503708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_2503708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503708 prefixEnd_2503708 := by exact prefixLift 2503708
  have htrace : WordTrace (prefixWord ++ tailWord_2503708) baseStart_2503708 baseEnd_2503708 := by
    simpa [prefixWord, tailWord_2503708, baseEnd_2503708] using wordTrace_append hprefix tailTrace_2503708
  have hstable : (prefixWord ++ tailWord_2503708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503708).length < 2 ^ (prefixWord ++ tailWord_2503708).sum := by decide
  have hdescent : baseEnd_2503708 < baseStart_2503708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503712 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 1, 4]
def baseStart_2503712 : Nat := 118140960795 + 2503712 * 2 ^ 59
def prefixEnd_2503712 : Nat := 4983230072969 + 3 ^ 40 * 2503712 * 2
def baseEnd_2503712 : Nat := 857071784286542299323763

theorem tailTrace_2503712 : CollatzResearch.WordTrace tailWord_2503712 prefixEnd_2503712 857071784286542299323763 := by
  unfold tailWord_2503712
  simp only [CollatzResearch.WordTrace]
  refine ⟨45658939352743249405868695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60878585803657665874491593 45658939352743249405868695)
  ·
    refine ⟨68488409029114874108803043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45658939352743249405868695 68488409029114874108803043)
    ·
      refine ⟨102732613543672311163204565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68488409029114874108803043 102732613543672311163204565)
      ·
        refine ⟨2407795629929819792887607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 102732613543672311163204565 2407795629929819792887607)
        ·
          refine ⟨3611693444894729689331411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407795629929819792887607 3611693444894729689331411)
          ·
            refine ⟨5417540167342094533997117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611693444894729689331411 5417540167342094533997117)
            ·
              refine ⟨2031577562753285450248919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5417540167342094533997117 2031577562753285450248919)
              ·
                refine ⟨3047366344129928175373379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031577562753285450248919 3047366344129928175373379)
                ·
                  refine ⟨4571049516194892263060069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047366344129928175373379 4571049516194892263060069)
                  ·
                    refine ⟨857071784286542299323763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4571049516194892263060069 857071784286542299323763)
                    ·
                      rfl

theorem cell22_2503712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 4].length) (baseStart_2503712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503712 prefixEnd_2503712 := by exact prefixLift 2503712
  have htrace : WordTrace (prefixWord ++ tailWord_2503712) baseStart_2503712 baseEnd_2503712 := by
    simpa [prefixWord, tailWord_2503712, baseEnd_2503712] using wordTrace_append hprefix tailTrace_2503712
  have hstable : (prefixWord ++ tailWord_2503712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503712).length < 2 ^ (prefixWord ++ tailWord_2503712).sum := by decide
  have hdescent : baseEnd_2503712 < baseStart_2503712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503781 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_2503781 : Nat := 118140960795 + 2503781 * 2 ^ 59
def prefixEnd_2503781 : Nat := 4983230072969 + 3 ^ 40 * 2503781 * 2
def baseEnd_2503781 : Nat := 857095404396649119348551

theorem tailTrace_2503781 : CollatzResearch.WordTrace tailWord_2503781 prefixEnd_2503781 857095404396649119348551 := by
  unfold tailWord_2503781
  simp only [CollatzResearch.WordTrace]
  refine ⟨91320395342236523595999197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60880263561491015730666131 91320395342236523595999197)
  ·
    refine ⟨34245148253338696348499699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91320395342236523595999197 34245148253338696348499699)
    ·
      refine ⟨51367722380008044522749549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34245148253338696348499699 51367722380008044522749549)
      ·
        refine ⟨19262895892503016696031081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51367722380008044522749549 19262895892503016696031081)
        ·
          refine ⟨14447171919377262522023311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19262895892503016696031081 14447171919377262522023311)
          ·
            refine ⟨21670757879065893783034967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14447171919377262522023311 21670757879065893783034967)
            ·
              refine ⟨32506136818598840674552451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21670757879065893783034967 32506136818598840674552451)
              ·
                refine ⟨48759205227898261011828677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32506136818598840674552451 48759205227898261011828677)
                ·
                  refine ⟨9142350980230923939717877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48759205227898261011828677 9142350980230923939717877)
                  ·
                    refine ⟨857095404396649119348551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9142350980230923939717877 857095404396649119348551)
                    ·
                      rfl

theorem cell22_2503781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_2503781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503781 prefixEnd_2503781 := by exact prefixLift 2503781
  have htrace : WordTrace (prefixWord ++ tailWord_2503781) baseStart_2503781 baseEnd_2503781 := by
    simpa [prefixWord, tailWord_2503781, baseEnd_2503781] using wordTrace_append hprefix tailTrace_2503781
  have hstable : (prefixWord ++ tailWord_2503781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503781).length < 2 ^ (prefixWord ++ tailWord_2503781).sum := by decide
  have hdescent : baseEnd_2503781 < baseStart_2503781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503783 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 5]
def baseStart_2503783 : Nat := 118140960795 + 2503783 * 2 ^ 59
def prefixEnd_2503783 : Nat := 4983230072969 + 3 ^ 40 * 2503783 * 2
def baseEnd_2503783 : Nat := 285698696345840593599515

theorem tailTrace_2503783 : CollatzResearch.WordTrace tailWord_2503783 prefixEnd_2503783 285698696345840593599515 := by
  unfold tailWord_2503783
  simp only [CollatzResearch.WordTrace]
  refine ⟨91320468288229277937572003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60880312192152851958381335 91320468288229277937572003)
  ·
    refine ⟨136980702432343916906358005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91320468288229277937572003 136980702432343916906358005)
    ·
      refine ⟨12841940853032242209971063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136980702432343916906358005 12841940853032242209971063)
      ·
        refine ⟨19262911279548363314956595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12841940853032242209971063 19262911279548363314956595)
        ·
          refine ⟨28894366919322544972434893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19262911279548363314956595 28894366919322544972434893)
          ·
            refine ⟨10835387594745954364663085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28894366919322544972434893 10835387594745954364663085)
            ·
              refine ⟨4063270348029732886748657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10835387594745954364663085 4063270348029732886748657)
              ·
                refine ⟨3047452761022299665061493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4063270348029732886748657 3047452761022299665061493)
                ·
                  refine ⟨285698696345840593599515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3047452761022299665061493 285698696345840593599515)
                  ·
                    rfl

theorem cell22_2503783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 5].length) (baseStart_2503783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503783 prefixEnd_2503783 := by exact prefixLift 2503783
  have htrace : WordTrace (prefixWord ++ tailWord_2503783) baseStart_2503783 baseEnd_2503783 := by
    simpa [prefixWord, tailWord_2503783, baseEnd_2503783] using wordTrace_append hprefix tailTrace_2503783
  have hstable : (prefixWord ++ tailWord_2503783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503783).length < 2 ^ (prefixWord ++ tailWord_2503783).sum := by decide
  have hdescent : baseEnd_2503783 < baseStart_2503783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503798 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2503798 : Nat := 118140960795 + 2503798 * 2 ^ 59
def prefixEnd_2503798 : Nat := 4983230072969 + 3 ^ 40 * 2503798 * 2
def baseEnd_2503798 : Nat := 857101223844066741673499

theorem tailTrace_2503798 : CollatzResearch.WordTrace tailWord_2503798 prefixEnd_2503798 857101223844066741673499 := by
  unfold tailWord_2503798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5707563461448433468710503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60880676922116623666245365 5707563461448433468710503)
  ·
    refine ⟨8561345192172650203065755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5707563461448433468710503 8561345192172650203065755)
    ·
      refine ⟨12842017788258975304598633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8561345192172650203065755 12842017788258975304598633)
      ·
        refine ⟨9631513341194231478448975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12842017788258975304598633 9631513341194231478448975)
        ·
          refine ⟨14447270011791347217673463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9631513341194231478448975 14447270011791347217673463)
          ·
            refine ⟨21670905017687020826510195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14447270011791347217673463 21670905017687020826510195)
            ·
              refine ⟨32506357526530531239765293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21670905017687020826510195 32506357526530531239765293)
              ·
                refine ⟨12189884072448949214911985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32506357526530531239765293 12189884072448949214911985)
                ·
                  refine ⟨9142413054336711911183989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12189884072448949214911985 9142413054336711911183989)
                  ·
                    refine ⟨857101223844066741673499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9142413054336711911183989 857101223844066741673499)
                    ·
                      rfl

theorem cell22_2503798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2503798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503798 prefixEnd_2503798 := by exact prefixLift 2503798
  have htrace : WordTrace (prefixWord ++ tailWord_2503798) baseStart_2503798 baseEnd_2503798 := by
    simpa [prefixWord, tailWord_2503798, baseEnd_2503798] using wordTrace_append hprefix tailTrace_2503798
  have hstable : (prefixWord ++ tailWord_2503798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503798).length < 2 ^ (prefixWord ++ tailWord_2503798).sum := by decide
  have hdescent : baseEnd_2503798 < baseStart_2503798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503806 : List Nat := [4, 2, 4, 1, 2, 1, 2, 6]
def baseStart_2503806 : Nat := 118140960795 + 2503806 * 2 ^ 59
def prefixEnd_2503806 : Nat := 4983230072969 + 3 ^ 40 * 2503806 * 2
def baseEnd_2503806 : Nat := 95233773600839709719275

theorem tailTrace_2503806 : CollatzResearch.WordTrace tailWord_2503806 prefixEnd_2503806 95233773600839709719275 := by
  unfold tailWord_2503806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11415163395893244108207409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60880871444763968577106181 11415163395893244108207409)
  ·
    refine ⟨8561372546919933081155557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11415163395893244108207409 8561372546919933081155557)
    ·
      refine ⟨1605257352547487452716667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8561372546919933081155557 1605257352547487452716667)
      ·
        refine ⟨2407886028821231179075001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605257352547487452716667 2407886028821231179075001)
        ·
          refine ⟨1805914521615923384306251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407886028821231179075001 1805914521615923384306251)
          ·
            refine ⟨2708871782423885076459377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805914521615923384306251 2708871782423885076459377)
            ·
              refine ⟨2031653836817913807344533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708871782423885076459377 2031653836817913807344533)
              ·
                refine ⟨95233773600839709719275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2031653836817913807344533 95233773600839709719275)
                ·
                  rfl

theorem cell22_2503806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_2503806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503806 prefixEnd_2503806 := by exact prefixLift 2503806
  have htrace : WordTrace (prefixWord ++ tailWord_2503806) baseStart_2503806 baseEnd_2503806 := by
    simpa [prefixWord, tailWord_2503806, baseEnd_2503806] using wordTrace_append hprefix tailTrace_2503806
  have hstable : (prefixWord ++ tailWord_2503806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503806).length < 2 ^ (prefixWord ++ tailWord_2503806).sum := by decide
  have hdescent : baseEnd_2503806 < baseStart_2503806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503811 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 6]
def baseStart_2503811 : Nat := 118140960795 + 2503811 * 2 ^ 59
def prefixEnd_2503811 : Nat := 4983230072969 + 3 ^ 40 * 2503811 * 2
def baseEnd_2503811 : Nat := 285701891336579680366153

theorem tailTrace_2503811 : CollatzResearch.WordTrace tailWord_2503811 prefixEnd_2503811 285701891336579680366153 := by
  unfold tailWord_2503811
  simp only [CollatzResearch.WordTrace]
  refine ⟨91321489532127838719591287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60880993021418559146394191 91321489532127838719591287)
  ·
    refine ⟨136982234298191758079386931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91321489532127838719591287 136982234298191758079386931)
    ·
      refine ⟨205473351447287637119080397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136982234298191758079386931 205473351447287637119080397)
      ·
        refine ⟨77052506792732863919655149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205473351447287637119080397 77052506792732863919655149)
        ·
          refine ⟨28894690047274823969870681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77052506792732863919655149 28894690047274823969870681)
          ·
            refine ⟨21671017535456117977403011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28894690047274823969870681 21671017535456117977403011)
            ·
              refine ⟨32506526303184176966104517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21671017535456117977403011 32506526303184176966104517)
              ·
                refine ⟨6094973681847033181144597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32506526303184176966104517 6094973681847033181144597)
                ·
                  refine ⟨285701891336579680366153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6094973681847033181144597 285701891336579680366153)
                  ·
                    rfl

theorem cell22_2503811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 6].length) (baseStart_2503811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503811 prefixEnd_2503811 := by exact prefixLift 2503811
  have htrace : WordTrace (prefixWord ++ tailWord_2503811) baseStart_2503811 baseEnd_2503811 := by
    simpa [prefixWord, tailWord_2503811, baseEnd_2503811] using wordTrace_append hprefix tailTrace_2503811
  have hstable : (prefixWord ++ tailWord_2503811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503811).length < 2 ^ (prefixWord ++ tailWord_2503811).sum := by decide
  have hdescent : baseEnd_2503811 < baseStart_2503811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503871 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 2, 7]
def baseStart_2503871 : Nat := 118140960795 + 2503871 * 2 ^ 59
def prefixEnd_2503871 : Nat := 4983230072969 + 3 ^ 40 * 2503871 * 2
def baseEnd_2503871 : Nat := 857126213235918884598275

theorem tailTrace_2503871 : CollatzResearch.WordTrace tailWord_2503871 prefixEnd_2503871 857126213235918884598275 := by
  unfold tailWord_2503871
  simp only [CollatzResearch.WordTrace]
  refine ⟨91323677911910468966775467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60882451941273645977850311 91323677911910468966775467)
  ·
    refine ⟨136985516867865703450163201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91323677911910468966775467 136985516867865703450163201)
    ·
      refine ⟨102739137650899277587622401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136985516867865703450163201 102739137650899277587622401)
      ·
        refine ⟨77054353238174458190716801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102739137650899277587622401 77054353238174458190716801)
        ·
          refine ⟨57790764928630843643037601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77054353238174458190716801 57790764928630843643037601)
          ·
            refine ⟨43343073696473132732278201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57790764928630843643037601 43343073696473132732278201)
            ·
              refine ⟨32507305272354849549208651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43343073696473132732278201 32507305272354849549208651)
              ·
                refine ⟨48760957908532274323812977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32507305272354849549208651 48760957908532274323812977)
                ·
                  refine ⟨36570718431399205742859733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48760957908532274323812977 36570718431399205742859733)
                  ·
                    refine ⟨857126213235918884598275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36570718431399205742859733 857126213235918884598275)
                    ·
                      rfl

theorem cell22_2503871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_2503871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503871 prefixEnd_2503871 := by exact prefixLift 2503871
  have htrace : WordTrace (prefixWord ++ tailWord_2503871) baseStart_2503871 baseEnd_2503871 := by
    simpa [prefixWord, tailWord_2503871, baseEnd_2503871] using wordTrace_append hprefix tailTrace_2503871
  have hstable : (prefixWord ++ tailWord_2503871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503871).length < 2 ^ (prefixWord ++ tailWord_2503871).sum := by decide
  have hdescent : baseEnd_2503871 < baseStart_2503871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503922 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_2503922 : Nat := 118140960795 + 2503922 * 2 ^ 59
def prefixEnd_2503922 : Nat := 4983230072969 + 3 ^ 40 * 2503922 * 2
def baseEnd_2503922 : Nat := 857143671578171751573119

theorem tailTrace_2503922 : CollatzResearch.WordTrace tailWord_2503922 prefixEnd_2503922 857143671578171751573119 := by
  unfold tailWord_2503922
  simp only [CollatzResearch.WordTrace]
  refine ⟨22831384508681426169220505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60883692023150469784588013 22831384508681426169220505)
  ·
    refine ⟨17123538381511069626915379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22831384508681426169220505 17123538381511069626915379)
    ·
      refine ⟨25685307572266604440373069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17123538381511069626915379 25685307572266604440373069)
      ·
        refine ⟨9631990339599976665139901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25685307572266604440373069 9631990339599976665139901)
        ·
          refine ⟨3611996377349991249427463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9631990339599976665139901 3611996377349991249427463)
          ·
            refine ⟨5417994566024986874141195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611996377349991249427463 5417994566024986874141195)
            ·
              refine ⟨8126991849037480311211793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417994566024986874141195 8126991849037480311211793)
              ·
                refine ⟨6095243886778110233408845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8126991849037480311211793 6095243886778110233408845)
                ·
                  refine ⟨2285716457541791337528317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6095243886778110233408845 2285716457541791337528317)
                  ·
                    refine ⟨857143671578171751573119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2285716457541791337528317 857143671578171751573119)
                    ·
                      rfl

theorem cell22_2503922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_2503922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503922 prefixEnd_2503922 := by exact prefixLift 2503922
  have htrace : WordTrace (prefixWord ++ tailWord_2503922) baseStart_2503922 baseEnd_2503922 := by
    simpa [prefixWord, tailWord_2503922, baseEnd_2503922] using wordTrace_append hprefix tailTrace_2503922
  have hstable : (prefixWord ++ tailWord_2503922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503922).length < 2 ^ (prefixWord ++ tailWord_2503922).sum := by decide
  have hdescent : baseEnd_2503922 < baseStart_2503922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2503990 : List Nat := [5, 1, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2503990 : Nat := 118140960795 + 2503990 * 2 ^ 59
def prefixEnd_2503990 : Nat := 4983230072969 + 3 ^ 40 * 2503990 * 2
def baseEnd_2503990 : Nat := 857166949367842240872911

theorem tailTrace_2503990 : CollatzResearch.WordTrace tailWord_2503990 prefixEnd_2503990 857166949367842240872911 := by
  unfold tailWord_2503990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708001137404959518147339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60885345465652901526904949 5708001137404959518147339)
  ·
    refine ⟨8562001706107439277221009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5708001137404959518147339 8562001706107439277221009)
    ·
      refine ⟨6421501279580579457915757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8562001706107439277221009 6421501279580579457915757)
      ·
        refine ⟨2408062979842717296718409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6421501279580579457915757 2408062979842717296718409)
        ·
          refine ⟨1806047234882037972538807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2408062979842717296718409 1806047234882037972538807)
          ·
            refine ⟨2709070852323056958808211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806047234882037972538807 2709070852323056958808211)
            ·
              refine ⟨4063606278484585438212317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709070852323056958808211 4063606278484585438212317)
              ·
                refine ⟨1523852354431719539329619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4063606278484585438212317 1523852354431719539329619)
                ·
                  refine ⟨2285778531647579308994429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523852354431719539329619 2285778531647579308994429)
                  ·
                    refine ⟨857166949367842240872911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2285778531647579308994429 857166949367842240872911)
                    ·
                      rfl

theorem cell22_2503990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2503990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2503990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2503990 prefixEnd_2503990 := by exact prefixLift 2503990
  have htrace : WordTrace (prefixWord ++ tailWord_2503990) baseStart_2503990 baseEnd_2503990 := by
    simpa [prefixWord, tailWord_2503990, baseEnd_2503990] using wordTrace_append hprefix tailTrace_2503990
  have hstable : (prefixWord ++ tailWord_2503990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2503990).length < 2 ^ (prefixWord ++ tailWord_2503990).sum := by decide
  have hdescent : baseEnd_2503990 < baseStart_2503990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2503990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504132 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 6]
def baseStart_2504132 : Nat := 118140960795 + 2504132 * 2 ^ 59
def prefixEnd_2504132 : Nat := 4983230072969 + 3 ^ 40 * 2504132 * 2
def baseEnd_2504132 : Nat := 285738519623267067940825

theorem tailTrace_2504132 : CollatzResearch.WordTrace tailWord_2504132 prefixEnd_2504132 285738519623267067940825 := by
  unfold tailWord_2504132
  simp only [CollatzResearch.WordTrace]
  refine ⟨45666598681982455271013325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60888798242643273694684433 45666598681982455271013325)
  ·
    refine ⟨17124974505743420726629997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45666598681982455271013325 17124974505743420726629997)
    ·
      refine ⟨6421865439653782772486249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17124974505743420726629997 6421865439653782772486249)
      ·
        refine ⟨4816399079740337079364687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6421865439653782772486249 4816399079740337079364687)
        ·
          refine ⟨7224598619610505619047031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4816399079740337079364687 7224598619610505619047031)
          ·
            refine ⟨10836897929415758428570547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7224598619610505619047031 10836897929415758428570547)
            ·
              refine ⟨16255346894123637642855821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10836897929415758428570547 16255346894123637642855821)
              ·
                refine ⟨6095755085296364116070933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16255346894123637642855821 6095755085296364116070933)
                ·
                  refine ⟨285738519623267067940825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6095755085296364116070933 285738519623267067940825)
                  ·
                    rfl

theorem cell22_2504132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_2504132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504132 prefixEnd_2504132 := by exact prefixLift 2504132
  have htrace : WordTrace (prefixWord ++ tailWord_2504132) baseStart_2504132 baseEnd_2504132 := by
    simpa [prefixWord, tailWord_2504132, baseEnd_2504132] using wordTrace_append hprefix tailTrace_2504132
  have hstable : (prefixWord ++ tailWord_2504132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504132).length < 2 ^ (prefixWord ++ tailWord_2504132).sum := by decide
  have hdescent : baseEnd_2504132 < baseStart_2504132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504194 : List Nat := [3, 4, 1, 2, 1, 2, 2, 7]
def baseStart_2504194 : Nat := 118140960795 + 2504194 * 2 ^ 59
def prefixEnd_2504194 : Nat := 4983230072969 + 3 ^ 40 * 2504194 * 2
def baseEnd_2504194 : Nat := 95248531415205967641365

theorem tailTrace_2504194 : CollatzResearch.WordTrace tailWord_2504194 prefixEnd_2504194 95248531415205967641365 := by
  unfold tailWord_2504194
  simp only [CollatzResearch.WordTrace]
  refine ⟨22833864672435073782695909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60890305793160196753855757 22833864672435073782695909)
  ·
    refine ⟨4281349626081576334255483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22833864672435073782695909 4281349626081576334255483)
    ·
      refine ⟨6422024439122364501383225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4281349626081576334255483 6422024439122364501383225)
      ·
        refine ⟨4816518329341773376037419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6422024439122364501383225 4816518329341773376037419)
        ·
          refine ⟨7224777494012660064056129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4816518329341773376037419 7224777494012660064056129)
          ·
            refine ⟨5418583120509495048042097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7224777494012660064056129 5418583120509495048042097)
            ·
              refine ⟨4063937340382121286031573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5418583120509495048042097 4063937340382121286031573)
              ·
                refine ⟨95248531415205967641365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4063937340382121286031573 95248531415205967641365)
                ·
                  rfl

theorem cell22_2504194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_2504194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504194 prefixEnd_2504194 := by exact prefixLift 2504194
  have htrace : WordTrace (prefixWord ++ tailWord_2504194) baseStart_2504194 baseEnd_2504194 := by
    simpa [prefixWord, tailWord_2504194, baseEnd_2504194] using wordTrace_append hprefix tailTrace_2504194
  have hstable : (prefixWord ++ tailWord_2504194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504194).length < 2 ^ (prefixWord ++ tailWord_2504194).sum := by decide
  have hdescent : baseEnd_2504194 < baseStart_2504194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504243 : List Nat := [1, 1, 1, 2, 4, 5, 2, 2, 1, 3]
def baseStart_2504243 : Nat := 118140960795 + 2504243 * 2 ^ 59
def prefixEnd_2504243 : Nat := 4983230072969 + 3 ^ 40 * 2504243 * 2
def baseEnd_2504243 : Nat := 857253556438233914297135

theorem tailTrace_2504243 : CollatzResearch.WordTrace tailWord_2504243 prefixEnd_2504243 857253556438233914297135 := by
  unfold tailWord_2504243
  simp only [CollatzResearch.WordTrace]
  refine ⟨91337245866562776499317383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60891497244375184332878255 91337245866562776499317383)
  ·
    refine ⟨137005868799844164748976075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91337245866562776499317383 137005868799844164748976075)
    ·
      refine ⟨205508803199766247123464113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137005868799844164748976075 205508803199766247123464113)
      ·
        refine ⟨154131602399824685342598085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205508803199766247123464113 154131602399824685342598085)
        ·
          refine ⟨28899675449967128501737141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154131602399824685342598085 28899675449967128501737141)
          ·
            refine ⟨2709344573434418297037857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28899675449967128501737141 2709344573434418297037857)
            ·
              refine ⟨2032008430075813722778393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2709344573434418297037857 2032008430075813722778393)
              ·
                refine ⟨1524006322556860292083795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032008430075813722778393 1524006322556860292083795)
                ·
                  refine ⟨2286009483835290438125693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524006322556860292083795 2286009483835290438125693)
                  ·
                    refine ⟨857253556438233914297135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286009483835290438125693 857253556438233914297135)
                    ·
                      rfl

theorem cell22_2504243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 3].length) (baseStart_2504243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504243 prefixEnd_2504243 := by exact prefixLift 2504243
  have htrace : WordTrace (prefixWord ++ tailWord_2504243) baseStart_2504243 baseEnd_2504243 := by
    simpa [prefixWord, tailWord_2504243, baseEnd_2504243] using wordTrace_append hprefix tailTrace_2504243
  have hstable : (prefixWord ++ tailWord_2504243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504243).length < 2 ^ (prefixWord ++ tailWord_2504243).sum := by decide
  have hdescent : baseEnd_2504243 < baseStart_2504243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504297 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_2504297 : Nat := 118140960795 + 2504297 * 2 ^ 59
def prefixEnd_2504297 : Nat := 4983230072969 + 3 ^ 40 * 2504297 * 2
def baseEnd_2504297 : Nat := 857272041741795773446969

theorem tailTrace_2504297 : CollatzResearch.WordTrace tailWord_2504297 prefixEnd_2504297 857272041741795773446969 := by
  unfold tailWord_2504297
  simp only [CollatzResearch.WordTrace]
  refine ⟨91339215408367143721783145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60892810272244762481188763 91339215408367143721783145)
  ·
    refine ⟨68504411556275357791337359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91339215408367143721783145 68504411556275357791337359)
    ·
      refine ⟨102756617334413036687006039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68504411556275357791337359 102756617334413036687006039)
      ·
        refine ⟨154134926001619555030509059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102756617334413036687006039 154134926001619555030509059)
        ·
          refine ⟨231202389002429332545763589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154134926001619555030509059 231202389002429332545763589)
          ·
            refine ⟨43350447937955499852330673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231202389002429332545763589 43350447937955499852330673)
            ·
              refine ⟨32512835953466624889248005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43350447937955499852330673 32512835953466624889248005)
              ·
                refine ⟨6096156741274992166734001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32512835953466624889248005 6096156741274992166734001)
                ·
                  refine ⟨4572117555956244125050501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6096156741274992166734001 4572117555956244125050501)
                  ·
                    refine ⟨857272041741795773446969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572117555956244125050501 857272041741795773446969)
                    ·
                      rfl

theorem cell22_2504297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_2504297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504297 prefixEnd_2504297 := by exact prefixLift 2504297
  have htrace : WordTrace (prefixWord ++ tailWord_2504297) baseStart_2504297 baseEnd_2504297 := by
    simpa [prefixWord, tailWord_2504297, baseEnd_2504297] using wordTrace_append hprefix tailTrace_2504297
  have hstable : (prefixWord ++ tailWord_2504297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504297).length < 2 ^ (prefixWord ++ tailWord_2504297).sum := by decide
  have hdescent : baseEnd_2504297 < baseStart_2504297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504357 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 7]
def baseStart_2504357 : Nat := 118140960795 + 2504357 * 2 ^ 59
def prefixEnd_2504357 : Nat := 4983230072969 + 3 ^ 40 * 2504357 * 2
def baseEnd_2504357 : Nat := 285764193655991872315595

theorem tailTrace_2504357 : CollatzResearch.WordTrace tailWord_2504357 prefixEnd_2504357 285764193655991872315595 := by
  unfold tailWord_2504357
  simp only [CollatzResearch.WordTrace]
  refine ⟨91341403788149773968967325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60894269192099849312644883 91341403788149773968967325)
  ·
    refine ⟨34253026420556165238362747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91341403788149773968967325 34253026420556165238362747)
    ·
      refine ⟨51379539630834247857544121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34253026420556165238362747 51379539630834247857544121)
      ·
        refine ⟨38534654723125685893158091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51379539630834247857544121 38534654723125685893158091)
        ·
          refine ⟨57801982084688528839737137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38534654723125685893158091 57801982084688528839737137)
          ·
            refine ⟨43351486563516396629802853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57801982084688528839737137 43351486563516396629802853)
            ·
              refine ⟨8128403730659324368088035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43351486563516396629802853 8128403730659324368088035)
              ·
                refine ⟨12192605595988986552132053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8128403730659324368088035 12192605595988986552132053)
                ·
                  refine ⟨285764193655991872315595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12192605595988986552132053 285764193655991872315595)
                  ·
                    rfl

theorem cell22_2504357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_2504357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504357 prefixEnd_2504357 := by exact prefixLift 2504357
  have htrace : WordTrace (prefixWord ++ tailWord_2504357) baseStart_2504357 baseEnd_2504357 := by
    simpa [prefixWord, tailWord_2504357, baseEnd_2504357] using wordTrace_append hprefix tailTrace_2504357
  have hstable : (prefixWord ++ tailWord_2504357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504357).length < 2 ^ (prefixWord ++ tailWord_2504357).sum := by decide
  have hdescent : baseEnd_2504357 < baseStart_2504357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504447 : List Nat := [1, 1, 2, 2, 1, 3, 2, 10]
def baseStart_2504447 : Nat := 118140960795 + 2504447 * 2 ^ 59
def prefixEnd_2504447 : Nat := 4983230072969 + 3 ^ 40 * 2504447 * 2
def baseEnd_2504447 : Nat := 95258154423027264688501

theorem tailTrace_2504447 : CollatzResearch.WordTrace tailWord_2504447 prefixEnd_2504447 95258154423027264688501 := by
  unfold tailWord_2504447
  simp only [CollatzResearch.WordTrace]
  refine ⟨91344686357823719339743595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60896457571882479559829063 91344686357823719339743595)
  ·
    refine ⟨137017029536735579009615393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91344686357823719339743595 137017029536735579009615393)
    ·
      refine ⟨102762772152551684257211545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137017029536735579009615393 102762772152551684257211545)
      ·
        refine ⟨77072079114413763192908659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102762772152551684257211545 77072079114413763192908659)
        ·
          refine ⟨115608118671620644789362989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77072079114413763192908659 115608118671620644789362989)
          ·
            refine ⟨43353044501857741796011121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115608118671620644789362989 43353044501857741796011121)
            ·
              refine ⟨32514783376393306347008341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43353044501857741796011121 32514783376393306347008341)
              ·
                refine ⟨95258154423027264688501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32514783376393306347008341 95258154423027264688501)
                ·
                  rfl

theorem cell22_2504447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 10].length) (baseStart_2504447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504447 prefixEnd_2504447 := by exact prefixLift 2504447
  have htrace : WordTrace (prefixWord ++ tailWord_2504447) baseStart_2504447 baseEnd_2504447 := by
    simpa [prefixWord, tailWord_2504447, baseEnd_2504447] using wordTrace_append hprefix tailTrace_2504447
  have hstable : (prefixWord ++ tailWord_2504447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504447).length < 2 ^ (prefixWord ++ tailWord_2504447).sum := by decide
  have hdescent : baseEnd_2504447 < baseStart_2504447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504455 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 1, 4]
def baseStart_2504455 : Nat := 118140960795 + 2504455 * 2 ^ 59
def prefixEnd_2504455 : Nat := 4983230072969 + 3 ^ 40 * 2504455 * 2
def baseEnd_2504455 : Nat := 857326128370736027996485

theorem tailTrace_2504455 : CollatzResearch.WordTrace tailWord_2504455 prefixEnd_2504455 857326128370736027996485 := by
  unfold tailWord_2504455
  simp only [CollatzResearch.WordTrace]
  refine ⟨91344978141794736706034819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60896652094529824470689879 91344978141794736706034819)
  ·
    refine ⟨137017467212692105059052229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91344978141794736706034819 137017467212692105059052229)
    ·
      refine ⟨25690775102379769698572293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137017467212692105059052229 25690775102379769698572293)
      ·
        refine ⟨4817020331696206818482305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25690775102379769698572293 4817020331696206818482305)
        ·
          refine ⟨3612765248772155113861729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4817020331696206818482305 3612765248772155113861729)
          ·
            refine ⟨2709573936579116335396297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3612765248772155113861729 2709573936579116335396297)
            ·
              refine ⟨2032180452434337251547223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2709573936579116335396297 2032180452434337251547223)
              ·
                refine ⟨3048270678651505877320835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032180452434337251547223 3048270678651505877320835)
                ·
                  refine ⟨4572406017977258815981253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048270678651505877320835 4572406017977258815981253)
                  ·
                    refine ⟨857326128370736027996485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572406017977258815981253 857326128370736027996485)
                    ·
                      rfl

theorem cell22_2504455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_2504455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504455 prefixEnd_2504455 := by exact prefixLift 2504455
  have htrace : WordTrace (prefixWord ++ tailWord_2504455) baseStart_2504455 baseEnd_2504455 := by
    simpa [prefixWord, tailWord_2504455, baseEnd_2504455] using wordTrace_append hprefix tailTrace_2504455
  have hstable : (prefixWord ++ tailWord_2504455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504455).length < 2 ^ (prefixWord ++ tailWord_2504455).sum := by decide
  have hdescent : baseEnd_2504455 < baseStart_2504455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504543 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 5]
def baseStart_2504543 : Nat := 118140960795 + 2504543 * 2 ^ 59
def prefixEnd_2504543 : Nat := 4983230072969 + 3 ^ 40 * 2504543 * 2
def baseEnd_2504543 : Nat := 285785417523044377265405

theorem tailTrace_2504543 : CollatzResearch.WordTrace tailWord_2504543 prefixEnd_2504543 285785417523044377265405 := by
  unfold tailWord_2504543
  simp only [CollatzResearch.WordTrace]
  refine ⟨91348187765475927735238283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60898791843650618490158855 91348187765475927735238283)
  ·
    refine ⟨137022281648213891602857425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91348187765475927735238283 137022281648213891602857425)
    ·
      refine ⟨102766711236160418702143069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137022281648213891602857425 102766711236160418702143069)
      ·
        refine ⟨38537516713560157013303651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102766711236160418702143069 38537516713560157013303651)
        ·
          refine ⟨57806275070340235519955477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38537516713560157013303651 57806275070340235519955477)
          ·
            refine ⟨2709669143922198539997913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57806275070340235519955477 2709669143922198539997913)
            ·
              refine ⟨2032251857941648904998435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2709669143922198539997913 2032251857941648904998435)
              ·
                refine ⟨3048377786912473357497653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032251857941648904998435 3048377786912473357497653)
                ·
                  refine ⟨285785417523044377265405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3048377786912473357497653 285785417523044377265405)
                  ·
                    rfl

theorem cell22_2504543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 5].length) (baseStart_2504543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504543 prefixEnd_2504543 := by exact prefixLift 2504543
  have htrace : WordTrace (prefixWord ++ tailWord_2504543) baseStart_2504543 baseEnd_2504543 := by
    simpa [prefixWord, tailWord_2504543, baseEnd_2504543] using wordTrace_append hprefix tailTrace_2504543
  have hstable : (prefixWord ++ tailWord_2504543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504543).length < 2 ^ (prefixWord ++ tailWord_2504543).sum := by decide
  have hdescent : baseEnd_2504543 < baseStart_2504543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504556 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_2504556 : Nat := 118140960795 + 2504556 * 2 ^ 59
def prefixEnd_2504556 : Nat := 4983230072969 + 3 ^ 40 * 2504556 * 2
def baseEnd_2504556 : Nat := 857360702734805431221175

theorem tailTrace_2504556 : CollatzResearch.WordTrace tailWord_2504556 prefixEnd_2504556 857360702734805431221175 := by
  unfold tailWord_2504556
  simp only [CollatzResearch.WordTrace]
  refine ⟨45674330957214415477730761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60899107942952553970307681 45674330957214415477730761)
  ·
    refine ⟨34255748217910811608298071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45674330957214415477730761 34255748217910811608298071)
    ·
      refine ⟨51383622326866217412447107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34255748217910811608298071 51383622326866217412447107)
      ·
        refine ⟨77075433490299326118670661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51383622326866217412447107 77075433490299326118670661)
        ·
          refine ⟨14451643779431123647250749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77075433490299326118670661 14451643779431123647250749)
          ·
            refine ⟨5419366417286671367719031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14451643779431123647250749 5419366417286671367719031)
            ·
              refine ⟨8129049625930007051578547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5419366417286671367719031 8129049625930007051578547)
              ·
                refine ⟨12193574438895010577367821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8129049625930007051578547 12193574438895010577367821)
                ·
                  refine ⟨4572590414585628966512933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12193574438895010577367821 4572590414585628966512933)
                  ·
                    refine ⟨857360702734805431221175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572590414585628966512933 857360702734805431221175)
                    ·
                      rfl

theorem cell22_2504556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_2504556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504556 prefixEnd_2504556 := by exact prefixLift 2504556
  have htrace : WordTrace (prefixWord ++ tailWord_2504556) baseStart_2504556 baseEnd_2504556 := by
    simpa [prefixWord, tailWord_2504556, baseEnd_2504556] using wordTrace_append hprefix tailTrace_2504556
  have hstable : (prefixWord ++ tailWord_2504556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504556).length < 2 ^ (prefixWord ++ tailWord_2504556).sum := by decide
  have hdescent : baseEnd_2504556 < baseStart_2504556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504571 : List Nat := [1, 1, 1, 1, 1, 5, 1, 7, 4]
def baseStart_2504571 : Nat := 118140960795 + 2504571 * 2 ^ 59
def prefixEnd_2504571 : Nat := 4983230072969 + 3 ^ 40 * 2504571 * 2
def baseEnd_2504571 : Nat := 285788612513783464032043

theorem tailTrace_2504571 : CollatzResearch.WordTrace tailWord_2504571 prefixEnd_2504571 285788612513783464032043 := by
  unfold tailWord_2504571
  simp only [CollatzResearch.WordTrace]
  refine ⟨91349209009374488517257567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60899472672916325678171711 91349209009374488517257567)
  ·
    refine ⟨137023813514061732775886351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91349209009374488517257567 137023813514061732775886351)
    ·
      refine ⟨205535720271092599163829527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137023813514061732775886351 205535720271092599163829527)
      ·
        refine ⟨308303580406638898745744291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205535720271092599163829527 308303580406638898745744291)
        ·
          refine ⟨462455370609958348118616437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308303580406638898745744291 462455370609958348118616437)
          ·
            refine ⟨43355190994683595136120291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 462455370609958348118616437 43355190994683595136120291)
            ·
              refine ⟨65032786492025392704180437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43355190994683595136120291 65032786492025392704180437)
              ·
                refine ⟨1524205933406845141504229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65032786492025392704180437 1524205933406845141504229)
                ·
                  refine ⟨285788612513783464032043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524205933406845141504229 285788612513783464032043)
                  ·
                    rfl

theorem cell22_2504571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 4].length) (baseStart_2504571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504571 prefixEnd_2504571 := by exact prefixLift 2504571
  have htrace : WordTrace (prefixWord ++ tailWord_2504571) baseStart_2504571 baseEnd_2504571 := by
    simpa [prefixWord, tailWord_2504571, baseEnd_2504571] using wordTrace_append hprefix tailTrace_2504571
  have hstable : (prefixWord ++ tailWord_2504571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504571).length < 2 ^ (prefixWord ++ tailWord_2504571).sum := by decide
  have hdescent : baseEnd_2504571 < baseStart_2504571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504631 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 7, 3]
def baseStart_2504631 : Nat := 118140960795 + 2504631 * 2 ^ 59
def prefixEnd_2504631 : Nat := 4983230072969 + 3 ^ 40 * 2504631 * 2
def baseEnd_2504631 : Nat := 857386376767530235595945

theorem tailTrace_2504631 : CollatzResearch.WordTrace tailWord_2504631 prefixEnd_2504631 857386376767530235595945 := by
  unfold tailWord_2504631
  simp only [CollatzResearch.WordTrace]
  refine ⟨91351397389157118764441747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60900931592771412509627831 91351397389157118764441747)
  ·
    refine ⟨137027096083735678146662621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91351397389157118764441747 137027096083735678146662621)
    ·
      refine ⟨51385161031400879304998483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137027096083735678146662621 51385161031400879304998483)
      ·
        refine ⟨77077741547101318957497725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51385161031400879304998483 77077741547101318957497725)
        ·
          refine ⟨28904153080162994609061647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77077741547101318957497725 28904153080162994609061647)
          ·
            refine ⟨43356229620244491913592471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28904153080162994609061647 43356229620244491913592471)
            ·
              refine ⟨65034344430366737870388707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43356229620244491913592471 65034344430366737870388707)
              ·
                refine ⟨97551516645550106805583061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65034344430366737870388707 97551516645550106805583061)
                ·
                  refine ⟨2286363671380080628255853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 97551516645550106805583061 2286363671380080628255853)
                  ·
                    refine ⟨857386376767530235595945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286363671380080628255853 857386376767530235595945)
                    ·
                      rfl

theorem cell22_2504631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_2504631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504631 prefixEnd_2504631 := by exact prefixLift 2504631
  have htrace : WordTrace (prefixWord ++ tailWord_2504631) baseStart_2504631 baseEnd_2504631 := by
    simpa [prefixWord, tailWord_2504631, baseEnd_2504631] using wordTrace_append hprefix tailTrace_2504631
  have hstable : (prefixWord ++ tailWord_2504631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504631).length < 2 ^ (prefixWord ++ tailWord_2504631).sum := by decide
  have hdescent : baseEnd_2504631 < baseStart_2504631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504648 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 3, 3]
def baseStart_2504648 : Nat := 118140960795 + 2504648 * 2 ^ 59
def prefixEnd_2504648 : Nat := 4983230072969 + 3 ^ 40 * 2504648 * 2
def baseEnd_2504648 : Nat := 857392196214947857920893

theorem tailTrace_2504648 : CollatzResearch.WordTrace tailWord_2504648 prefixEnd_2504648 857392196214947857920893 := by
  unfold tailWord_2504648
  simp only [CollatzResearch.WordTrace]
  refine ⟨45676008715047765333905299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60901344953397020445207065 45676008715047765333905299)
  ·
    refine ⟨68514013072571648000857949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45676008715047765333905299 68514013072571648000857949)
    ·
      refine ⟨25692754902214368000321731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68514013072571648000857949 25692754902214368000321731)
      ·
        refine ⟨38539132353321552000482597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25692754902214368000321731 38539132353321552000482597)
        ·
          refine ⟨7226087316247791000090487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38539132353321552000482597 7226087316247791000090487)
          ·
            refine ⟨10839130974371686500135731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226087316247791000090487 10839130974371686500135731)
            ·
              refine ⟨16258696461557529750203597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10839130974371686500135731 16258696461557529750203597)
              ·
                refine ⟨6097011173084073656326349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16258696461557529750203597 6097011173084073656326349)
                ·
                  refine ⟨2286379189906527621122381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6097011173084073656326349 2286379189906527621122381)
                  ·
                    refine ⟨857392196214947857920893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286379189906527621122381 857392196214947857920893)
                    ·
                      rfl

theorem cell22_2504648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_2504648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504648 prefixEnd_2504648 := by exact prefixLift 2504648
  have htrace : WordTrace (prefixWord ++ tailWord_2504648) baseStart_2504648 baseEnd_2504648 := by
    simpa [prefixWord, tailWord_2504648, baseEnd_2504648] using wordTrace_append hprefix tailTrace_2504648
  have hstable : (prefixWord ++ tailWord_2504648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504648).length < 2 ^ (prefixWord ++ tailWord_2504648).sum := by decide
  have hdescent : baseEnd_2504648 < baseStart_2504648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504738 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2504738 : Nat := 118140960795 + 2504738 * 2 ^ 59
def prefixEnd_2504738 : Nat := 4983230072969 + 3 ^ 40 * 2504738 * 2
def baseEnd_2504738 : Nat := 857423005054217623170617

theorem tailTrace_2504738 : CollatzResearch.WordTrace tailWord_2504738 prefixEnd_2504738 857423005054217623170617 := by
  unfold tailWord_2504738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22838824999942369009646717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60903533333179650692391245 22838824999942369009646717)
  ·
    refine ⟨8564559374978388378617519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22838824999942369009646717 8564559374978388378617519)
    ·
      refine ⟨12846839062467582567926279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8564559374978388378617519 12846839062467582567926279)
      ·
        refine ⟨19270258593701373851889419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12846839062467582567926279 19270258593701373851889419)
        ·
          refine ⟨28905387890552060777834129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19270258593701373851889419 28905387890552060777834129)
          ·
            refine ⟨21679040917914045583375597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28905387890552060777834129 21679040917914045583375597)
            ·
              refine ⟨8129640344217767093765849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21679040917914045583375597 8129640344217767093765849)
              ·
                refine ⟨6097230258163325320324387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8129640344217767093765849 6097230258163325320324387)
                ·
                  refine ⟨9145845387244987980486581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6097230258163325320324387 9145845387244987980486581)
                  ·
                    refine ⟨857423005054217623170617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9145845387244987980486581 857423005054217623170617)
                    ·
                      rfl

theorem cell22_2504738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2504738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504738 prefixEnd_2504738 := by exact prefixLift 2504738
  have htrace : WordTrace (prefixWord ++ tailWord_2504738) baseStart_2504738 baseEnd_2504738 := by
    simpa [prefixWord, tailWord_2504738, baseEnd_2504738] using wordTrace_append hprefix tailTrace_2504738
  have hstable : (prefixWord ++ tailWord_2504738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504738).length < 2 ^ (prefixWord ++ tailWord_2504738).sum := by decide
  have hdescent : baseEnd_2504738 < baseStart_2504738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504753 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_2504753 : Nat := 118140960795 + 2504753 * 2 ^ 59
def prefixEnd_2504753 : Nat := 4983230072969 + 3 ^ 40 * 2504753 * 2
def baseEnd_2504753 : Nat := 857428139860762584045571

theorem tailTrace_2504753 : CollatzResearch.WordTrace tailWord_2504753 prefixEnd_2504753 857428139860762584045571 := by
  unfold tailWord_2504753
  simp only [CollatzResearch.WordTrace]
  refine ⟨91355847094715133600382913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60903898063143422400255275 91355847094715133600382913)
  ·
    refine ⟨68516885321036350200287185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91355847094715133600382913 68516885321036350200287185)
    ·
      refine ⟨51387663990777262650215389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68516885321036350200287185 51387663990777262650215389)
      ·
        refine ⟨19270373996541473493830771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51387663990777262650215389 19270373996541473493830771)
        ·
          refine ⟨28905560994812210240746157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19270373996541473493830771 28905560994812210240746157)
          ·
            refine ⟨10839585373054578840279809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28905560994812210240746157 10839585373054578840279809)
            ·
              refine ⟨8129689029790934130209857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10839585373054578840279809 8129689029790934130209857)
              ·
                refine ⟨6097266772343200597657393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8129689029790934130209857 6097266772343200597657393)
                ·
                  refine ⟨4572950079257400448243045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6097266772343200597657393 4572950079257400448243045)
                  ·
                    refine ⟨857428139860762584045571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572950079257400448243045 857428139860762584045571)
                    ·
                      rfl

theorem cell22_2504753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_2504753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504753 prefixEnd_2504753 := by exact prefixLift 2504753
  have htrace : WordTrace (prefixWord ++ tailWord_2504753) baseStart_2504753 baseEnd_2504753 := by
    simpa [prefixWord, tailWord_2504753, baseEnd_2504753] using wordTrace_append hprefix tailTrace_2504753
  have hstable : (prefixWord ++ tailWord_2504753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504753).length < 2 ^ (prefixWord ++ tailWord_2504753).sum := by decide
  have hdescent : baseEnd_2504753 < baseStart_2504753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504768 : List Nat := [2, 1, 1, 2, 2, 6, 1, 7]
def baseStart_2504768 : Nat := 118140960795 + 2504768 * 2 ^ 59
def prefixEnd_2504768 : Nat := 4983230072969 + 3 ^ 40 * 2504768 * 2
def baseEnd_2504768 : Nat := 95270363851923060546725

theorem tailTrace_2504768 : CollatzResearch.WordTrace tailWord_2504768 prefixEnd_2504768 95270363851923060546725 := by
  unfold tailWord_2504768
  simp only [CollatzResearch.WordTrace]
  refine ⟨45678197094830395581089479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60904262793107194108119305 45678197094830395581089479)
  ·
    refine ⟨68517295642245593371634219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45678197094830395581089479 68517295642245593371634219)
    ·
      refine ⟨102775943463368390057451329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68517295642245593371634219 102775943463368390057451329)
      ·
        refine ⟨77081957597526292543088497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102775943463368390057451329 77081957597526292543088497)
        ·
          refine ⟨57811468198144719407316373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77081957597526292543088497 57811468198144719407316373)
          ·
            refine ⟨2709912571788033722217955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57811468198144719407316373 2709912571788033722217955)
            ·
              refine ⟨4064868857682050583326933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709912571788033722217955 4064868857682050583326933)
              ·
                refine ⟨95270363851923060546725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4064868857682050583326933 95270363851923060546725)
                ·
                  rfl

theorem cell22_2504768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 7].length) (baseStart_2504768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504768 prefixEnd_2504768 := by exact prefixLift 2504768
  have htrace : WordTrace (prefixWord ++ tailWord_2504768) baseStart_2504768 baseEnd_2504768 := by
    simpa [prefixWord, tailWord_2504768, baseEnd_2504768] using wordTrace_append hprefix tailTrace_2504768
  have hstable : (prefixWord ++ tailWord_2504768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504768).length < 2 ^ (prefixWord ++ tailWord_2504768).sum := by decide
  have hdescent : baseEnd_2504768 < baseStart_2504768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504783 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 3, 3]
def baseStart_2504783 : Nat := 118140960795 + 2504783 * 2 ^ 59
def prefixEnd_2504783 : Nat := 4983230072969 + 3 ^ 40 * 2504783 * 2
def baseEnd_2504783 : Nat := 857438409473852505795479

theorem tailTrace_2504783 : CollatzResearch.WordTrace tailWord_2504783 prefixEnd_2504783 857438409473852505795479 := by
  unfold tailWord_2504783
  simp only [CollatzResearch.WordTrace]
  refine ⟨91356941284606448723975003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60904627523070965815983335 91356941284606448723975003)
  ·
    refine ⟨137035411926909673085962505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91356941284606448723975003 137035411926909673085962505)
    ·
      refine ⟨102776558945182254814471879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137035411926909673085962505 102776558945182254814471879)
      ·
        refine ⟨154164838417773382221707819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102776558945182254814471879 154164838417773382221707819)
        ·
          refine ⟨231247257626660073332561729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154164838417773382221707819 231247257626660073332561729)
          ·
            refine ⟨173435443219995054999421297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231247257626660073332561729 173435443219995054999421297)
            ·
              refine ⟨130076582414996291249565973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173435443219995054999421297 130076582414996291249565973)
              ·
                refine ⟨6097339800702951152323405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130076582414996291249565973 6097339800702951152323405)
                ·
                  refine ⟨2286502425263606682121277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6097339800702951152323405 2286502425263606682121277)
                  ·
                    refine ⟨857438409473852505795479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286502425263606682121277 857438409473852505795479)
                    ·
                      rfl

theorem cell22_2504783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_2504783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504783 prefixEnd_2504783 := by exact prefixLift 2504783
  have htrace : WordTrace (prefixWord ++ tailWord_2504783) baseStart_2504783 baseEnd_2504783 := by
    simpa [prefixWord, tailWord_2504783, baseEnd_2504783] using wordTrace_append hprefix tailTrace_2504783
  have hstable : (prefixWord ++ tailWord_2504783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504783).length < 2 ^ (prefixWord ++ tailWord_2504783).sum := by decide
  have hdescent : baseEnd_2504783 < baseStart_2504783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504813 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2504813 : Nat := 118140960795 + 2504813 * 2 ^ 59
def prefixEnd_2504813 : Nat := 4983230072969 + 3 ^ 40 * 2504813 * 2
def baseEnd_2504813 : Nat := 285816226362314142515129

theorem tailTrace_2504813 : CollatzResearch.WordTrace tailWord_2504813 prefixEnd_2504813 285816226362314142515129 := by
  unfold tailWord_2504813
  simp only [CollatzResearch.WordTrace]
  refine ⟨91358035474497763847567093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60905356982998509231711395 91358035474497763847567093)
  ·
    refine ⟨8564815825734165360709415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91358035474497763847567093 8564815825734165360709415)
    ·
      refine ⟨12847223738601248041064123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8564815825734165360709415 12847223738601248041064123)
      ·
        refine ⟨19270835607901872061596185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12847223738601248041064123 19270835607901872061596185)
        ·
          refine ⟨14453126705926404046197139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19270835607901872061596185 14453126705926404046197139)
          ·
            refine ⟨21679690058889606069295709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14453126705926404046197139 21679690058889606069295709)
            ·
              refine ⟨8129883772083602275985891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21679690058889606069295709 8129883772083602275985891)
              ·
                refine ⟨12194825658125403413978837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8129883772083602275985891 12194825658125403413978837)
                ·
                  refine ⟨285816226362314142515129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12194825658125403413978837 285816226362314142515129)
                  ·
                    rfl

theorem cell22_2504813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2504813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504813 prefixEnd_2504813 := by exact prefixLift 2504813
  have htrace : WordTrace (prefixWord ++ tailWord_2504813) baseStart_2504813 baseEnd_2504813 := by
    simpa [prefixWord, tailWord_2504813, baseEnd_2504813] using wordTrace_append hprefix tailTrace_2504813
  have hstable : (prefixWord ++ tailWord_2504813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504813).length < 2 ^ (prefixWord ++ tailWord_2504813).sum := by decide
  have hdescent : baseEnd_2504813 < baseStart_2504813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504828 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_2504828 : Nat := 118140960795 + 2504828 * 2 ^ 59
def prefixEnd_2504828 : Nat := 4983230072969 + 3 ^ 40 * 2504828 * 2
def baseEnd_2504828 : Nat := 857453813893487388420341

theorem tailTrace_2504828 : CollatzResearch.WordTrace tailWord_2504828 prefixEnd_2504828 857453813893487388420341 := by
  unfold tailWord_2504828
  simp only [CollatzResearch.WordTrace]
  refine ⟨45679291284721710704681569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60905721712962280939575425 45679291284721710704681569)
  ·
    refine ⟨34259468463541283028511177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45679291284721710704681569 34259468463541283028511177)
    ·
      refine ⟨25694601347655962271383383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34259468463541283028511177 25694601347655962271383383)
      ·
        refine ⟨38541902021483943407075075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25694601347655962271383383 38541902021483943407075075)
        ·
          refine ⟨57812853032225915110612613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38541902021483943407075075 57812853032225915110612613)
          ·
            refine ⟨10839909943542359083239865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57812853032225915110612613 10839909943542359083239865)
            ·
              refine ⟨8129932457656769312429899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10839909943542359083239865 8129932457656769312429899)
              ·
                refine ⟨12194898686485153968644849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8129932457656769312429899 12194898686485153968644849)
                ·
                  refine ⟨9146174014863865476483637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12194898686485153968644849 9146174014863865476483637)
                  ·
                    refine ⟨857453813893487388420341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9146174014863865476483637 857453813893487388420341)
                    ·
                      rfl

theorem cell22_2504828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_2504828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504828 prefixEnd_2504828 := by exact prefixLift 2504828
  have htrace : WordTrace (prefixWord ++ tailWord_2504828) baseStart_2504828 baseEnd_2504828 := by
    simpa [prefixWord, tailWord_2504828, baseEnd_2504828] using wordTrace_append hprefix tailTrace_2504828
  have hstable : (prefixWord ++ tailWord_2504828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504828).length < 2 ^ (prefixWord ++ tailWord_2504828).sum := by decide
  have hdescent : baseEnd_2504828 < baseStart_2504828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504860 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_2504860 : Nat := 118140960795 + 2504860 * 2 ^ 59
def prefixEnd_2504860 : Nat := 4983230072969 + 3 ^ 40 * 2504860 * 2
def baseEnd_2504860 : Nat := 857464768147449971620243

theorem tailTrace_2504860 : CollatzResearch.WordTrace tailWord_2504860 prefixEnd_2504860 857464768147449971620243 := by
  unfold tailWord_2504860
  simp only [CollatzResearch.WordTrace]
  refine ⟨45679874852663745437264017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60906499803551660583018689 45679874852663745437264017)
  ·
    refine ⟨34259906139497809077948013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45679874852663745437264017 34259906139497809077948013)
    ·
      refine ⟨12847464802311678404230505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34259906139497809077948013 12847464802311678404230505)
      ·
        refine ⟨9635598601733758803172879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12847464802311678404230505 9635598601733758803172879)
        ·
          refine ⟨14453397902600638204759319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9635598601733758803172879 14453397902600638204759319)
          ·
            refine ⟨21680096853900957307138979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14453397902600638204759319 21680096853900957307138979)
            ·
              refine ⟨32520145280851435960708469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21680096853900957307138979 32520145280851435960708469)
              ·
                refine ⟨3048763620079822121316419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32520145280851435960708469 3048763620079822121316419)
                ·
                  refine ⟨4573145430119733181974629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048763620079822121316419 4573145430119733181974629)
                  ·
                    refine ⟨857464768147449971620243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4573145430119733181974629 857464768147449971620243)
                    ·
                      rfl

theorem cell22_2504860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_2504860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504860 prefixEnd_2504860 := by exact prefixLift 2504860
  have htrace : WordTrace (prefixWord ++ tailWord_2504860) baseStart_2504860 baseEnd_2504860 := by
    simpa [prefixWord, tailWord_2504860, baseEnd_2504860] using wordTrace_append hprefix tailTrace_2504860
  have hstable : (prefixWord ++ tailWord_2504860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504860).length < 2 ^ (prefixWord ++ tailWord_2504860).sum := by decide
  have hdescent : baseEnd_2504860 < baseStart_2504860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504888 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_2504888 : Nat := 118140960795 + 2504888 * 2 ^ 59
def prefixEnd_2504888 : Nat := 4983230072969 + 3 ^ 40 * 2504888 * 2
def baseEnd_2504888 : Nat := 857474353119667231920157

theorem tailTrace_2504888 : CollatzResearch.WordTrace tailWord_2504888 prefixEnd_2504888 857474353119667231920157 := by
  unfold tailWord_2504888
  simp only [CollatzResearch.WordTrace]
  refine ⟨45680385474613025828273659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60907180632817367771031545 45680385474613025828273659)
  ·
    refine ⟨68520578211919538742410489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45680385474613025828273659 68520578211919538742410489)
    ·
      refine ⟨51390433658939654056807867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68520578211919538742410489 51390433658939654056807867)
      ·
        refine ⟨77085650488409481085211801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51390433658939654056807867 77085650488409481085211801)
        ·
          refine ⟨57814237866307110813908851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77085650488409481085211801 57814237866307110813908851)
          ·
            refine ⟨86721356799460666220863277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57814237866307110813908851 86721356799460666220863277)
            ·
              refine ⟨32520508799797749832823729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86721356799460666220863277 32520508799797749832823729)
              ·
                refine ⟨24390381599848312374617797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32520508799797749832823729 24390381599848312374617797)
                ·
                  refine ⟨4573196549971558570240837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24390381599848312374617797 4573196549971558570240837)
                  ·
                    refine ⟨857474353119667231920157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4573196549971558570240837 857474353119667231920157)
                    ·
                      rfl

theorem cell22_2504888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_2504888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504888 prefixEnd_2504888 := by exact prefixLift 2504888
  have htrace : WordTrace (prefixWord ++ tailWord_2504888) baseStart_2504888 baseEnd_2504888 := by
    simpa [prefixWord, tailWord_2504888, baseEnd_2504888] using wordTrace_append hprefix tailTrace_2504888
  have hstable : (prefixWord ++ tailWord_2504888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504888).length < 2 ^ (prefixWord ++ tailWord_2504888).sum := by decide
  have hdescent : baseEnd_2504888 < baseStart_2504888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504894 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2504894 : Nat := 118140960795 + 2504894 * 2 ^ 59
def prefixEnd_2504894 : Nat := 4983230072969 + 3 ^ 40 * 2504894 * 2
def baseEnd_2504894 : Nat := 857476407042285216270139

theorem tailTrace_2504894 : CollatzResearch.WordTrace tailWord_2504894 prefixEnd_2504894 857476407042285216270139 := by
  unfold tailWord_2504894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11420123723400539335158217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60907326524802876454177157 11420123723400539335158217)
  ·
    refine ⟨8565092792550404501368663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11420123723400539335158217 8565092792550404501368663)
    ·
      refine ⟨12847639188825606752052995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8565092792550404501368663 12847639188825606752052995)
      ·
        refine ⟨19271458783238410128079493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12847639188825606752052995 19271458783238410128079493)
        ·
          refine ⟨3613398521857201899014905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19271458783238410128079493 3613398521857201899014905)
          ·
            refine ⟨2710048891392901424261179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3613398521857201899014905 2710048891392901424261179)
            ·
              refine ⟨4065073337089352136391769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710048891392901424261179 4065073337089352136391769)
              ·
                refine ⟨3048805002817014102293827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065073337089352136391769 3048805002817014102293827)
                ·
                  refine ⟨4573207504225521153440741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048805002817014102293827 4573207504225521153440741)
                  ·
                    refine ⟨857476407042285216270139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4573207504225521153440741 857476407042285216270139)
                    ·
                      rfl

theorem cell22_2504894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2504894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504894 prefixEnd_2504894 := by exact prefixLift 2504894
  have htrace : WordTrace (prefixWord ++ tailWord_2504894) baseStart_2504894 baseEnd_2504894 := by
    simpa [prefixWord, tailWord_2504894, baseEnd_2504894] using wordTrace_append hprefix tailTrace_2504894
  have hstable : (prefixWord ++ tailWord_2504894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504894).length < 2 ^ (prefixWord ++ tailWord_2504894).sum := by decide
  have hdescent : baseEnd_2504894 < baseStart_2504894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504963 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 1, 7]
def baseStart_2504963 : Nat := 118140960795 + 2504963 * 2 ^ 59
def prefixEnd_2504963 : Nat := 4983230072969 + 3 ^ 40 * 2504963 * 2
def baseEnd_2504963 : Nat := 857500027152392036294927

theorem tailTrace_2504963 : CollatzResearch.WordTrace tailWord_2504963 prefixEnd_2504963 857500027152392036294927 := by
  unfold tailWord_2504963
  simp only [CollatzResearch.WordTrace]
  refine ⟨91363506423954339465527543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60909004282636226310351695 91363506423954339465527543)
  ·
    refine ⟨137045259635931509198291315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91363506423954339465527543 137045259635931509198291315)
    ·
      refine ⟨205567889453897263797436973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137045259635931509198291315 205567889453897263797436973)
      ·
        refine ⟨77087958545211473924038865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205567889453897263797436973 77087958545211473924038865)
        ·
          refine ⟨57815968908908605443029149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77087958545211473924038865 57815968908908605443029149)
          ·
            refine ⟨21680988340840727041135931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57815968908908605443029149 21680988340840727041135931)
            ·
              refine ⟨32521482511261090561703897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21680988340840727041135931 32521482511261090561703897)
              ·
                refine ⟨24391111883445817921277923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32521482511261090561703897 24391111883445817921277923)
                ·
                  refine ⟨36586667825168726881916885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24391111883445817921277923 36586667825168726881916885)
                  ·
                    refine ⟨857500027152392036294927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36586667825168726881916885 857500027152392036294927)
                    ·
                      rfl

theorem cell22_2504963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_2504963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504963 prefixEnd_2504963 := by exact prefixLift 2504963
  have htrace : WordTrace (prefixWord ++ tailWord_2504963) baseStart_2504963 baseEnd_2504963 := by
    simpa [prefixWord, tailWord_2504963, baseEnd_2504963] using wordTrace_append hprefix tailTrace_2504963
  have hstable : (prefixWord ++ tailWord_2504963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504963).length < 2 ^ (prefixWord ++ tailWord_2504963).sum := by decide
  have hdescent : baseEnd_2504963 < baseStart_2504963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2504969 : List Nat := [1, 2, 1, 1, 3, 5, 2, 3, 1, 3]
def baseStart_2504969 : Nat := 118140960795 + 2504969 * 2 ^ 59
def prefixEnd_2504969 : Nat := 4983230072969 + 3 ^ 40 * 2504969 * 2
def baseEnd_2504969 : Nat := 857502081075010020644909

theorem tailTrace_2504969 : CollatzResearch.WordTrace tailWord_2504969 prefixEnd_2504969 857502081075010020644909 := by
  unfold tailWord_2504969
  simp only [CollatzResearch.WordTrace]
  refine ⟨91363725261932602490245961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60909150174621734993497307 91363725261932602490245961)
  ·
    refine ⟨68522793946449451867684471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91363725261932602490245961 68522793946449451867684471)
    ·
      refine ⟨102784190919674177801526707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68522793946449451867684471 102784190919674177801526707)
      ·
        refine ⟨154176286379511266702290061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102784190919674177801526707 154176286379511266702290061)
        ·
          refine ⟨57816107392316725013358773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154176286379511266702290061 57816107392316725013358773)
          ·
            refine ⟨5420260068029692970002385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57816107392316725013358773 5420260068029692970002385)
            ·
              refine ⟨4065195051022269727501789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5420260068029692970002385 4065195051022269727501789)
              ·
                refine ⟨1524448144133351147813171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4065195051022269727501789 1524448144133351147813171)
                ·
                  refine ⟨2286672216200026721719757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524448144133351147813171 2286672216200026721719757)
                  ·
                    refine ⟨857502081075010020644909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286672216200026721719757 857502081075010020644909)
                    ·
                      rfl

theorem cell22_2504969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 3].length) (baseStart_2504969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2504969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2504969 prefixEnd_2504969 := by exact prefixLift 2504969
  have htrace : WordTrace (prefixWord ++ tailWord_2504969) baseStart_2504969 baseEnd_2504969 := by
    simpa [prefixWord, tailWord_2504969, baseEnd_2504969] using wordTrace_append hprefix tailTrace_2504969
  have hstable : (prefixWord ++ tailWord_2504969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2504969).length < 2 ^ (prefixWord ++ tailWord_2504969).sum := by decide
  have hdescent : baseEnd_2504969 < baseStart_2504969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2504969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505027 : List Nat := [1, 1, 1, 3, 1, 3, 5, 3, 4]
def baseStart_2505027 : Nat := 118140960795 + 2505027 * 2 ^ 59
def prefixEnd_2505027 : Nat := 4983230072969 + 3 ^ 40 * 2505027 * 2
def baseEnd_2505027 : Nat := 285840645220105734231577

theorem tailTrace_2505027 : CollatzResearch.WordTrace tailWord_2505027 prefixEnd_2505027 285840645220105734231577 := by
  unfold tailWord_2505027
  simp only [CollatzResearch.WordTrace]
  refine ⟨91365840695722478395857335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60910560463814985597238223 91365840695722478395857335)
  ·
    refine ⟨137048761043583717593786003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91365840695722478395857335 137048761043583717593786003)
    ·
      refine ⟨205573141565375576390679005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137048761043583717593786003 205573141565375576390679005)
      ·
        refine ⟨77089928087015841146504627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205573141565375576390679005 77089928087015841146504627)
        ·
          refine ⟨115634892130523761719756941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77089928087015841146504627 115634892130523761719756941)
          ·
            refine ⟨43363084548946410644908853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115634892130523761719756941 43363084548946410644908853)
            ·
              refine ⟨4065289176463725997960205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43363084548946410644908853 4065289176463725997960205)
              ·
                refine ⟨1524483441173897249235077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4065289176463725997960205 1524483441173897249235077)
                ·
                  refine ⟨285840645220105734231577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524483441173897249235077 285840645220105734231577)
                  ·
                    rfl

theorem cell22_2505027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 4].length) (baseStart_2505027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505027 prefixEnd_2505027 := by exact prefixLift 2505027
  have htrace : WordTrace (prefixWord ++ tailWord_2505027) baseStart_2505027 baseEnd_2505027 := by
    simpa [prefixWord, tailWord_2505027, baseEnd_2505027] using wordTrace_append hprefix tailTrace_2505027
  have hstable : (prefixWord ++ tailWord_2505027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505027).length < 2 ^ (prefixWord ++ tailWord_2505027).sum := by decide
  have hdescent : baseEnd_2505027 < baseStart_2505027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505040 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_2505040 : Nat := 118140960795 + 2505040 * 2 ^ 59
def prefixEnd_2505040 : Nat := 4983230072969 + 3 ^ 40 * 2505040 * 2
def baseEnd_2505040 : Nat := 857526385825989502119691

theorem tailTrace_2505040 : CollatzResearch.WordTrace tailWord_2505040 prefixEnd_2505040 857526385825989502119691 := by
  unfold tailWord_2505040
  simp only [CollatzResearch.WordTrace]
  refine ⟨45683157422337690808040287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60910876563116921077387049 45683157422337690808040287)
  ·
    refine ⟨68524736133506536212060431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45683157422337690808040287 68524736133506536212060431)
    ·
      refine ⟨102787104200259804318090647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68524736133506536212060431 102787104200259804318090647)
      ·
        refine ⟨154180656300389706477135971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102787104200259804318090647 154180656300389706477135971)
        ·
          refine ⟨231270984450584559715703957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154180656300389706477135971 231270984450584559715703957)
          ·
            refine ⟨10840827396121151236673623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 231270984450584559715703957 10840827396121151236673623)
            ·
              refine ⟨16261241094181726855010435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10840827396121151236673623 16261241094181726855010435)
              ·
                refine ⟨24391861641272590282515653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16261241094181726855010435 24391861641272590282515653)
                ·
                  refine ⟨4573474057738610677971685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24391861641272590282515653 4573474057738610677971685)
                  ·
                    refine ⟨857526385825989502119691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4573474057738610677971685 857526385825989502119691)
                    ·
                      rfl

theorem cell22_2505040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_2505040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505040 prefixEnd_2505040 := by exact prefixLift 2505040
  have htrace : WordTrace (prefixWord ++ tailWord_2505040) baseStart_2505040 baseEnd_2505040 := by
    simpa [prefixWord, tailWord_2505040, baseEnd_2505040] using wordTrace_append hprefix tailTrace_2505040
  have hstable : (prefixWord ++ tailWord_2505040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505040).length < 2 ^ (prefixWord ++ tailWord_2505040).sum := by decide
  have hdescent : baseEnd_2505040 < baseStart_2505040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505042 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_2505042 : Nat := 118140960795 + 2505042 * 2 ^ 59
def prefixEnd_2505042 : Nat := 4983230072969 + 3 ^ 40 * 2505042 * 2
def baseEnd_2505042 : Nat := 857527070466862163569685

theorem tailTrace_2505042 : CollatzResearch.WordTrace tailWord_2505042 prefixEnd_2505042 857527070466862163569685 := by
  unfold tailWord_2505042
  simp only [CollatzResearch.WordTrace]
  refine ⟨22841596947667033989413345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60910925193778757305102253 22841596947667033989413345)
  ·
    refine ⟨17131197710750275492060009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22841596947667033989413345 17131197710750275492060009)
    ·
      refine ⟨12848398283062706619045007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17131197710750275492060009 12848398283062706619045007)
      ·
        refine ⟨19272597424594059928567511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12848398283062706619045007 19272597424594059928567511)
        ·
          refine ⟨28908896136891089892851267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19272597424594059928567511 28908896136891089892851267)
          ·
            refine ⟨43363344205336634839276901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28908896136891089892851267 43363344205336634839276901)
            ·
              refine ⟨8130627038500619032364419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43363344205336634839276901 8130627038500619032364419)
              ·
                refine ⟨12195940557750928548546629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8130627038500619032364419 12195940557750928548546629)
                ·
                  refine ⟨2286738854578299102852493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12195940557750928548546629 2286738854578299102852493)
                  ·
                    refine ⟨857527070466862163569685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286738854578299102852493 857527070466862163569685)
                    ·
                      rfl

theorem cell22_2505042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_2505042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505042 prefixEnd_2505042 := by exact prefixLift 2505042
  have htrace : WordTrace (prefixWord ++ tailWord_2505042) baseStart_2505042 baseEnd_2505042 := by
    simpa [prefixWord, tailWord_2505042, baseEnd_2505042] using wordTrace_append hprefix tailTrace_2505042
  have hstable : (prefixWord ++ tailWord_2505042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505042).length < 2 ^ (prefixWord ++ tailWord_2505042).sum := by decide
  have hdescent : baseEnd_2505042 < baseStart_2505042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505102 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_2505102 : Nat := 118140960795 + 2505102 * 2 ^ 59
def prefixEnd_2505102 : Nat := 4983230072969 + 3 ^ 40 * 2505102 * 2
def baseEnd_2505102 : Nat := 857547609693042007069501

theorem tailTrace_2505102 : CollatzResearch.WordTrace tailWord_2505102 prefixEnd_2505102 857547609693042007069501 := by
  unfold tailWord_2505102
  simp only [CollatzResearch.WordTrace]
  refine ⟨11421072021306345775604695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60912384113633844136558373 11421072021306345775604695)
  ·
    refine ⟨17131608031959518663407043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11421072021306345775604695 17131608031959518663407043)
    ·
      refine ⟨25697412047939277995110565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17131608031959518663407043 25697412047939277995110565)
      ·
        refine ⟨4818264758988614624083231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25697412047939277995110565 4818264758988614624083231)
        ·
          refine ⟨7227397138482921936124847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4818264758988614624083231 7227397138482921936124847)
          ·
            refine ⟨10841095707724382904187271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7227397138482921936124847 10841095707724382904187271)
            ·
              refine ⟨16261643561586574356280907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10841095707724382904187271 16261643561586574356280907)
              ·
                refine ⟨24392465342379861534421361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16261643561586574356280907 24392465342379861534421361)
                ·
                  refine ⟨18294349006784896150816021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24392465342379861534421361 18294349006784896150816021)
                  ·
                    refine ⟨857547609693042007069501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18294349006784896150816021 857547609693042007069501)
                    ·
                      rfl

theorem cell22_2505102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_2505102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505102 prefixEnd_2505102 := by exact prefixLift 2505102
  have htrace : WordTrace (prefixWord ++ tailWord_2505102) baseStart_2505102 baseEnd_2505102 := by
    simpa [prefixWord, tailWord_2505102, baseEnd_2505102] using wordTrace_append hprefix tailTrace_2505102
  have hstable : (prefixWord ++ tailWord_2505102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505102).length < 2 ^ (prefixWord ++ tailWord_2505102).sum := by decide
  have hdescent : baseEnd_2505102 < baseStart_2505102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505121 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 3, 3]
def baseStart_2505121 : Nat := 118140960795 + 2505121 * 2 ^ 59
def prefixEnd_2505121 : Nat := 4983230072969 + 3 ^ 40 * 2505121 * 2
def baseEnd_2505121 : Nat := 857554113781332290844443

theorem tailTrace_2505121 : CollatzResearch.WordTrace tailWord_2505121 prefixEnd_2505121 857554113781332290844443 := by
  unfold tailWord_2505121
  simp only [CollatzResearch.WordTrace]
  refine ⟨91369269157381932449779217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60912846104921288299852811 91369269157381932449779217)
  ·
    refine ⟨68526951868036449337334413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91369269157381932449779217 68526951868036449337334413)
    ·
      refine ⟨25697606950513668501500405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68526951868036449337334413 25697606950513668501500405)
      ·
        refine ⟨2409150651610656422015663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25697606950513668501500405 2409150651610656422015663)
        ·
          refine ⟨3613725977415984633023495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409150651610656422015663 3613725977415984633023495)
          ·
            refine ⟨5420588966123976949535243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613725977415984633023495 5420588966123976949535243)
            ·
              refine ⟨8130883449185965424302865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5420588966123976949535243 8130883449185965424302865)
              ·
                refine ⟨6098162586889474068227149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8130883449185965424302865 6098162586889474068227149)
                ·
                  refine ⟨2286810970083552775585181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6098162586889474068227149 2286810970083552775585181)
                  ·
                    refine ⟨857554113781332290844443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286810970083552775585181 857554113781332290844443)
                    ·
                      rfl

theorem cell22_2505121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_2505121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505121 prefixEnd_2505121 := by exact prefixLift 2505121
  have htrace : WordTrace (prefixWord ++ tailWord_2505121) baseStart_2505121 baseEnd_2505121 := by
    simpa [prefixWord, tailWord_2505121, baseEnd_2505121] using wordTrace_append hprefix tailTrace_2505121
  have hstable : (prefixWord ++ tailWord_2505121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505121).length < 2 ^ (prefixWord ++ tailWord_2505121).sum := by decide
  have hdescent : baseEnd_2505121 < baseStart_2505121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505162 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_2505162 : Nat := 118140960795 + 2505162 * 2 ^ 59
def prefixEnd_2505162 : Nat := 4983230072969 + 3 ^ 40 * 2505162 * 2
def baseEnd_2505162 : Nat := 285856049639740616856439

theorem tailTrace_2505162 : CollatzResearch.WordTrace tailWord_2505162 prefixEnd_2505162 285856049639740616856439 := by
  unfold tailWord_2505162
  simp only [CollatzResearch.WordTrace]
  refine ⟨22842691137558349113005435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60913843033488930968014493 22842691137558349113005435)
  ·
    refine ⟨34264036706337523669508153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22842691137558349113005435 34264036706337523669508153)
    ·
      refine ⟨25698027529753142752131115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34264036706337523669508153 25698027529753142752131115)
      ·
        refine ⟨38547041294629714128196673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25698027529753142752131115 38547041294629714128196673)
        ·
          refine ⟨28910280970972285596147505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38547041294629714128196673 28910280970972285596147505)
          ·
            refine ⟨21682710728229214197110629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28910280970972285596147505 21682710728229214197110629)
            ·
              refine ⟨4065508261542977661958243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21682710728229214197110629 4065508261542977661958243)
              ·
                refine ⟨6098262392314466492937365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4065508261542977661958243 6098262392314466492937365)
                ·
                  refine ⟨285856049639740616856439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6098262392314466492937365 285856049639740616856439)
                  ·
                    rfl

theorem cell22_2505162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_2505162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505162 prefixEnd_2505162 := by exact prefixLift 2505162
  have htrace : WordTrace (prefixWord ++ tailWord_2505162) baseStart_2505162 baseEnd_2505162 := by
    simpa [prefixWord, tailWord_2505162, baseEnd_2505162] using wordTrace_append hprefix tailTrace_2505162
  have hstable : (prefixWord ++ tailWord_2505162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505162).length < 2 ^ (prefixWord ++ tailWord_2505162).sum := by decide
  have hdescent : baseEnd_2505162 < baseStart_2505162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505192 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_2505192 : Nat := 118140960795 + 2505192 * 2 ^ 59
def prefixEnd_2505192 : Nat := 4983230072969 + 3 ^ 40 * 2505192 * 2
def baseEnd_2505192 : Nat := 857578418532311772319225

theorem tailTrace_2505192 : CollatzResearch.WordTrace tailWord_2505192 prefixEnd_2505192 857578418532311772319225 := by
  unfold tailWord_2505192
  simp only [CollatzResearch.WordTrace]
  refine ⟨45685929370062355787806915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60914572493416474383742553 45685929370062355787806915)
  ·
    refine ⟨68528894055093533681710373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45685929370062355787806915 68528894055093533681710373)
    ·
      refine ⟨12849167635330037565320695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68528894055093533681710373 12849167635330037565320695)
      ·
        refine ⟨19273751452995056347981043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12849167635330037565320695 19273751452995056347981043)
        ·
          refine ⟨28910627179492584521971565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19273751452995056347981043 28910627179492584521971565)
          ·
            refine ⟨10841485192309719195739337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28910627179492584521971565 10841485192309719195739337)
            ·
              refine ⟨8131113894232289396804503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10841485192309719195739337 8131113894232289396804503)
              ·
                refine ⟨12196670841348434095206755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8131113894232289396804503 12196670841348434095206755)
                ·
                  refine ⟨18295006262022651142810133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12196670841348434095206755 18295006262022651142810133)
                  ·
                    refine ⟨857578418532311772319225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18295006262022651142810133 857578418532311772319225)
                    ·
                      rfl

theorem cell22_2505192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_2505192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505192 prefixEnd_2505192 := by exact prefixLift 2505192
  have htrace : WordTrace (prefixWord ++ tailWord_2505192) baseStart_2505192 baseEnd_2505192 := by
    simpa [prefixWord, tailWord_2505192, baseEnd_2505192] using wordTrace_append hprefix tailTrace_2505192
  have hstable : (prefixWord ++ tailWord_2505192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505192).length < 2 ^ (prefixWord ++ tailWord_2505192).sum := by decide
  have hdescent : baseEnd_2505192 < baseStart_2505192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505194 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_2505194 : Nat := 118140960795 + 2505194 * 2 ^ 59
def prefixEnd_2505194 : Nat := 4983230072969 + 3 ^ 40 * 2505194 * 2
def baseEnd_2505194 : Nat := 857579103173184433769219

theorem tailTrace_2505194 : CollatzResearch.WordTrace tailWord_2505194 prefixEnd_2505194 857579103173184433769219 := by
  unfold tailWord_2505194
  simp only [CollatzResearch.WordTrace]
  refine ⟨22842982921529366479296659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60914621124078310611457757 22842982921529366479296659)
  ·
    refine ⟨34264474382294049718944989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22842982921529366479296659 34264474382294049718944989)
    ·
      refine ⟨12849177893360268644604371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34264474382294049718944989 12849177893360268644604371)
      ·
        refine ⟨19273766840040402966906557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12849177893360268644604371 19273766840040402966906557)
        ·
          refine ⟨7227662565015151112589959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19273766840040402966906557 7227662565015151112589959)
          ·
            refine ⟨10841493847522726668884939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7227662565015151112589959 10841493847522726668884939)
            ·
              refine ⟨16262240771284090003327409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10841493847522726668884939 16262240771284090003327409)
              ·
                refine ⟨12196680578463067502495557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16262240771284090003327409 12196680578463067502495557)
                ·
                  refine ⟨2286877608461825156717917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12196680578463067502495557 2286877608461825156717917)
                  ·
                    refine ⟨857579103173184433769219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286877608461825156717917 857579103173184433769219)
                    ·
                      rfl

theorem cell22_2505194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_2505194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505194 prefixEnd_2505194 := by exact prefixLift 2505194
  have htrace : WordTrace (prefixWord ++ tailWord_2505194) baseStart_2505194 baseEnd_2505194 := by
    simpa [prefixWord, tailWord_2505194, baseEnd_2505194] using wordTrace_append hprefix tailTrace_2505194
  have hstable : (prefixWord ++ tailWord_2505194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505194).length < 2 ^ (prefixWord ++ tailWord_2505194).sum := by decide
  have hdescent : baseEnd_2505194 < baseStart_2505194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505228 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_2505228 : Nat := 118140960795 + 2505228 * 2 ^ 59
def prefixEnd_2505228 : Nat := 4983230072969 + 3 ^ 40 * 2505228 * 2
def baseEnd_2505228 : Nat := 857590742068019678419115

theorem tailTrace_2505228 : CollatzResearch.WordTrace tailWord_2505228 prefixEnd_2505228 857590742068019678419115 := by
  unfold tailWord_2505228
  simp only [CollatzResearch.WordTrace]
  refine ⟨45686585883997144861962169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60915447845329526482616225 45686585883997144861962169)
  ·
    refine ⟨34264939412997858646471627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45686585883997144861962169 34264939412997858646471627)
    ·
      refine ⟨51397409119496787969707441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34264939412997858646471627 51397409119496787969707441)
      ·
        refine ⟨38548056839622590977280581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51397409119496787969707441 38548056839622590977280581)
        ·
          refine ⟨7227760657429235808240109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38548056839622590977280581 7227760657429235808240109)
          ·
            refine ⟨2710410246535963428090041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7227760657429235808240109 2710410246535963428090041)
            ·
              refine ⟨2032807684901972571067531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2710410246535963428090041 2032807684901972571067531)
              ·
                refine ⟨3049211527352958856601297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032807684901972571067531 3049211527352958856601297)
                ·
                  refine ⟨2286908645514719142450973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3049211527352958856601297 2286908645514719142450973)
                  ·
                    refine ⟨857590742068019678419115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286908645514719142450973 857590742068019678419115)
                    ·
                      rfl

theorem cell22_2505228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_2505228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505228 prefixEnd_2505228 := by exact prefixLift 2505228
  have htrace : WordTrace (prefixWord ++ tailWord_2505228) baseStart_2505228 baseEnd_2505228 := by
    simpa [prefixWord, tailWord_2505228, baseEnd_2505228] using wordTrace_append hprefix tailTrace_2505228
  have hstable : (prefixWord ++ tailWord_2505228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505228).length < 2 ^ (prefixWord ++ tailWord_2505228).sum := by decide
  have hdescent : baseEnd_2505228 < baseStart_2505228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505267 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 2, 5]
def baseStart_2505267 : Nat := 118140960795 + 2505267 * 2 ^ 59
def prefixEnd_2505267 : Nat := 4983230072969 + 3 ^ 40 * 2505267 * 2
def baseEnd_2505267 : Nat := 857604092565036576693995

theorem tailTrace_2505267 : CollatzResearch.WordTrace tailWord_2505267 prefixEnd_2505267 857604092565036576693995 := by
  unfold tailWord_2505267
  simp only [CollatzResearch.WordTrace]
  refine ⟨91374594214852999384594055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60916396143235332923062703 91374594214852999384594055)
  ·
    refine ⟨137061891322279499076891083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91374594214852999384594055 137061891322279499076891083)
    ·
      refine ⟨205592836983419248615336625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137061891322279499076891083 205592836983419248615336625)
      ·
        refine ⟨154194627737564436461502469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205592836983419248615336625 154194627737564436461502469)
        ·
          refine ⟨28911492700793331836531713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154194627737564436461502469 28911492700793331836531713)
          ·
            refine ⟨21683619525594998877398785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28911492700793331836531713 21683619525594998877398785)
            ·
              refine ⟨16262714644196249158049089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21683619525594998877398785 16262714644196249158049089)
              ·
                refine ⟨12197035983147186868536817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16262714644196249158049089 12197035983147186868536817)
                ·
                  refine ⟨9147776987360390151402613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12197035983147186868536817 9147776987360390151402613)
                  ·
                    refine ⟨857604092565036576693995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9147776987360390151402613 857604092565036576693995)
                    ·
                      rfl

theorem cell22_2505267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_2505267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505267 prefixEnd_2505267 := by exact prefixLift 2505267
  have htrace : WordTrace (prefixWord ++ tailWord_2505267) baseStart_2505267 baseEnd_2505267 := by
    simpa [prefixWord, tailWord_2505267, baseEnd_2505267] using wordTrace_append hprefix tailTrace_2505267
  have hstable : (prefixWord ++ tailWord_2505267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505267).length < 2 ^ (prefixWord ++ tailWord_2505267).sum := by decide
  have hdescent : baseEnd_2505267 < baseStart_2505267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505269 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 5]
def baseStart_2505269 : Nat := 118140960795 + 2505269 * 2 ^ 59
def prefixEnd_2505269 : Nat := 4983230072969 + 3 ^ 40 * 2505269 * 2
def baseEnd_2505269 : Nat := 285868259068636412714663

theorem tailTrace_2505269 : CollatzResearch.WordTrace tailWord_2505269 prefixEnd_2505269 285868259068636412714663 := by
  unfold tailWord_2505269
  simp only [CollatzResearch.WordTrace]
  refine ⟨91374667160845753726166861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60916444773897169150777907 91374667160845753726166861)
  ·
    refine ⟨34265500185317157647312573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91374667160845753726166861 34265500185317157647312573)
    ·
      refine ⟨12849562569493934117742215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34265500185317157647312573 12849562569493934117742215)
      ·
        refine ⟨19274343854240901176613323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12849562569493934117742215 19274343854240901176613323)
        ·
          refine ⟨28911515781361351764919985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19274343854240901176613323 28911515781361351764919985)
          ·
            refine ⟨21683636836021013823689989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28911515781361351764919985 21683636836021013823689989)
            ·
              refine ⟨4065681906753940091941873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21683636836021013823689989 4065681906753940091941873)
              ·
                refine ⟨3049261430065455068956405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065681906753940091941873 3049261430065455068956405)
                ·
                  refine ⟨285868259068636412714663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3049261430065455068956405 285868259068636412714663)
                  ·
                    rfl

theorem cell22_2505269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_2505269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505269 prefixEnd_2505269 := by exact prefixLift 2505269
  have htrace : WordTrace (prefixWord ++ tailWord_2505269) baseStart_2505269 baseEnd_2505269 := by
    simpa [prefixWord, tailWord_2505269, baseEnd_2505269] using wordTrace_append hprefix tailTrace_2505269
  have hstable : (prefixWord ++ tailWord_2505269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505269).length < 2 ^ (prefixWord ++ tailWord_2505269).sum := by decide
  have hdescent : baseEnd_2505269 < baseStart_2505269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2505297 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 8]
def baseStart_2505297 : Nat := 118140960795 + 2505297 * 2 ^ 59
def prefixEnd_2505297 : Nat := 4983230072969 + 3 ^ 40 * 2505297 * 2
def baseEnd_2505297 : Nat := 285871454059375499481301

theorem tailTrace_2505297 : CollatzResearch.WordTrace tailWord_2505297 prefixEnd_2505297 285871454059375499481301 := by
  unfold tailWord_2505297
  simp only [CollatzResearch.WordTrace]
  refine ⟨91375688404744314508186145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60917125603162876338790763 91375688404744314508186145)
  ·
    refine ⟨68531766303558235881139609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91375688404744314508186145 68531766303558235881139609)
    ·
      refine ⟨51398824727668676910854707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68531766303558235881139609 51398824727668676910854707)
      ·
        refine ⟨77098237091503015366282061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51398824727668676910854707 77098237091503015366282061)
        ·
          refine ⟨28911838909313630762355773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77098237091503015366282061 28911838909313630762355773)
          ·
            refine ⟨10841939590992611535883415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28911838909313630762355773 10841939590992611535883415)
            ·
              refine ⟨16262909386488917303825123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10841939590992611535883415 16262909386488917303825123)
              ·
                refine ⟨24394364079733375955737685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16262909386488917303825123 24394364079733375955737685)
                ·
                  refine ⟨285871454059375499481301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24394364079733375955737685 285871454059375499481301)
                  ·
                    rfl

theorem cell22_2505297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_2505297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2505297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2505297 prefixEnd_2505297 := by exact prefixLift 2505297
  have htrace : WordTrace (prefixWord ++ tailWord_2505297) baseStart_2505297 baseEnd_2505297 := by
    simpa [prefixWord, tailWord_2505297, baseEnd_2505297] using wordTrace_append hprefix tailTrace_2505297
  have hstable : (prefixWord ++ tailWord_2505297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2505297).length < 2 ^ (prefixWord ++ tailWord_2505297).sum := by decide
  have hdescent : baseEnd_2505297 < baseStart_2505297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2505297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
