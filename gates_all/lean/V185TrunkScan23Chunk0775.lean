import V185TrunkScan23Chunk0774

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4583772 : List Nat := [2, 2, 4, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4583772 : Nat := 118140960795 + 4583772 * 2 ^ 59
def prefixEnd_4583772 : Nat := 4983230072969 + 3 ^ 40 * 4583772 * 2
def baseEnd_4583772 : Nat := 2353678246620945204669623

theorem tailTrace_4583772 : CollatzResearch.WordTrace tailWord_4583772 prefixEnd_4583772 2353678246620945204669623 := by
  unfold tailWord_4583772
  simp only [CollatzResearch.WordTrace]
  refine ⟨83591949774892182388580785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111455933033189576518107713 83591949774892182388580785)
  ·
    refine ⟨62693962331169136791435589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83591949774892182388580785 62693962331169136791435589)
    ·
      refine ⟨11755117937094213148394173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62693962331169136791435589 11755117937094213148394173)
      ·
        refine ⟨4408169226410329930647815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11755117937094213148394173 4408169226410329930647815)
        ·
          refine ⟨6612253839615494895971723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4408169226410329930647815 6612253839615494895971723)
          ·
            refine ⟨9918380759423242343957585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6612253839615494895971723 9918380759423242343957585)
            ·
              refine ⟨7438785569567431757968189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9918380759423242343957585 7438785569567431757968189)
              ·
                refine ⟨2789544588587786909238071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7438785569567431757968189 2789544588587786909238071)
                ·
                  refine ⟨4184316882881680363857107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2789544588587786909238071 4184316882881680363857107)
                  ·
                    refine ⟨6276475324322520545785661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4184316882881680363857107 6276475324322520545785661)
                    ·
                      refine ⟨2353678246620945204669623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276475324322520545785661 2353678246620945204669623)
                      ·
                        rfl

theorem cell23_4583772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4583772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583772 prefixEnd_4583772 := by exact prefixLift 4583772
  have htrace : WordTrace (prefixWord ++ tailWord_4583772) baseStart_4583772 baseEnd_4583772 := by
    simpa [prefixWord, tailWord_4583772, baseEnd_4583772] using wordTrace_append hprefix tailTrace_4583772
  have hstable : (prefixWord ++ tailWord_4583772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583772).length < 2 ^ (prefixWord ++ tailWord_4583772).sum := by decide
  have hdescent : baseEnd_4583772 < baseStart_4583772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583778 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_4583778 : Nat := 118140960795 + 4583778 * 2 ^ 59
def prefixEnd_4583778 : Nat := 4983230072969 + 3 ^ 40 * 4583778 * 2
def baseEnd_4583778 : Nat := 2353681327504872181194595

theorem tailTrace_4583778 : CollatzResearch.WordTrace tailWord_4583778 prefixEnd_4583778 2353681327504872181194595 := by
  unfold tailWord_4583778
  simp only [CollatzResearch.WordTrace]
  refine ⟨41796029596940656950469997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111456078925175085201253325 41796029596940656950469997)
  ·
    refine ⟨15673511098852746356426249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41796029596940656950469997 15673511098852746356426249)
    ·
      refine ⟨11755133324139559767319687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15673511098852746356426249 11755133324139559767319687)
      ·
        refine ⟨17632699986209339650979531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11755133324139559767319687 17632699986209339650979531)
        ·
          refine ⟨26449049979314009476469297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17632699986209339650979531 26449049979314009476469297)
          ·
            refine ⟨19836787484485507107351973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26449049979314009476469297 19836787484485507107351973)
            ·
              refine ⟨3719397653341032582628495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19836787484485507107351973 3719397653341032582628495)
              ·
                refine ⟨5579096480011548873942743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3719397653341032582628495 5579096480011548873942743)
                ·
                  refine ⟨8368644720017323310914115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5579096480011548873942743 8368644720017323310914115)
                  ·
                    refine ⟨12552967080025984966371173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8368644720017323310914115 12552967080025984966371173)
                    ·
                      refine ⟨2353681327504872181194595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12552967080025984966371173 2353681327504872181194595)
                      ·
                        rfl

theorem cell23_4583778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_4583778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583778 prefixEnd_4583778 := by exact prefixLift 4583778
  have htrace : WordTrace (prefixWord ++ tailWord_4583778) baseStart_4583778 baseEnd_4583778 := by
    simpa [prefixWord, tailWord_4583778, baseEnd_4583778] using wordTrace_append hprefix tailTrace_4583778
  have hstable : (prefixWord ++ tailWord_4583778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583778).length < 2 ^ (prefixWord ++ tailWord_4583778).sum := by decide
  have hdescent : baseEnd_4583778 < baseStart_4583778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583781 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_4583781 : Nat := 118140960795 + 4583781 * 2 ^ 59
def prefixEnd_4583781 : Nat := 4983230072969 + 3 ^ 40 * 4583781 * 2
def baseEnd_4583781 : Nat := 2353682867946835669457081

theorem tailTrace_4583781 : CollatzResearch.WordTrace tailWord_4583781 prefixEnd_4583781 2353682867946835669457081 := by
  unfold tailWord_4583781
  simp only [CollatzResearch.WordTrace]
  refine ⟨167184227806751759314239197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111456151871167839542826131 167184227806751759314239197)
  ·
    refine ⟨62694085427531909742839699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167184227806751759314239197 62694085427531909742839699)
    ·
      refine ⟨94041128141297864614259549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62694085427531909742839699 94041128141297864614259549)
      ·
        refine ⟨35265423052986699230347331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94041128141297864614259549 35265423052986699230347331)
        ·
          refine ⟨52898134579480048845520997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35265423052986699230347331 52898134579480048845520997)
          ·
            refine ⟨9918400233652509158535187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52898134579480048845520997 9918400233652509158535187)
            ·
              refine ⟨14877600350478763737802781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9918400233652509158535187 14877600350478763737802781)
              ·
                refine ⟨5579100131429536401676043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14877600350478763737802781 5579100131429536401676043)
                ·
                  refine ⟨8368650197144304602514065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5579100131429536401676043 8368650197144304602514065)
                  ·
                    refine ⟨6276487647858228451885549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8368650197144304602514065 6276487647858228451885549)
                    ·
                      refine ⟨2353682867946835669457081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276487647858228451885549 2353682867946835669457081)
                      ·
                        rfl

theorem cell23_4583781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_4583781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583781 prefixEnd_4583781 := by exact prefixLift 4583781
  have htrace : WordTrace (prefixWord ++ tailWord_4583781) baseStart_4583781 baseEnd_4583781 := by
    simpa [prefixWord, tailWord_4583781, baseEnd_4583781] using wordTrace_append hprefix tailTrace_4583781
  have hstable : (prefixWord ++ tailWord_4583781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583781).length < 2 ^ (prefixWord ++ tailWord_4583781).sum := by decide
  have hdescent : baseEnd_4583781 < baseStart_4583781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583788 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_4583788 : Nat := 118140960795 + 4583788 * 2 ^ 59
def prefixEnd_4583788 : Nat := 4983230072969 + 3 ^ 40 * 4583788 * 2
def baseEnd_4583788 : Nat := 784562154103805714023183

theorem tailTrace_4583788 : CollatzResearch.WordTrace tailWord_4583788 prefixEnd_4583788 784562154103805714023183 := by
  unfold tailWord_4583788
  simp only [CollatzResearch.WordTrace]
  refine ⟨83592241558863199754872009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111456322078484266339829345 83592241558863199754872009)
  ·
    refine ⟨62694181169147399816154007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83592241558863199754872009 62694181169147399816154007)
    ·
      refine ⟨94041271753721099724231011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62694181169147399816154007 94041271753721099724231011)
      ·
        refine ⟨141061907630581649586346517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94041271753721099724231011 141061907630581649586346517)
        ·
          refine ⟨6612276920183514824359993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 141061907630581649586346517 6612276920183514824359993)
          ·
            refine ⟨4959207690137636118269995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6612276920183514824359993 4959207690137636118269995)
            ·
              refine ⟨7438811535206454177404993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959207690137636118269995 7438811535206454177404993)
              ·
                refine ⟨5579108651404840633053745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7438811535206454177404993 5579108651404840633053745)
                ·
                  refine ⟨4184331488553630474790309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5579108651404840633053745 4184331488553630474790309)
                  ·
                    refine ⟨784562154103805714023183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4184331488553630474790309 784562154103805714023183)
                    ·
                      rfl

theorem cell23_4583788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_4583788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583788 prefixEnd_4583788 := by exact prefixLift 4583788
  have htrace : WordTrace (prefixWord ++ tailWord_4583788) baseStart_4583788 baseEnd_4583788 := by
    simpa [prefixWord, tailWord_4583788, baseEnd_4583788] using wordTrace_append hprefix tailTrace_4583788
  have hstable : (prefixWord ++ tailWord_4583788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583788).length < 2 ^ (prefixWord ++ tailWord_4583788).sum := by decide
  have hdescent : baseEnd_4583788 < baseStart_4583788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583798 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4583798 : Nat := 118140960795 + 4583798 * 2 ^ 59
def prefixEnd_4583798 : Nat := 4983230072969 + 3 ^ 40 * 4583798 * 2
def baseEnd_4583798 : Nat := 2353691597117962102944503

theorem tailTrace_4583798 : CollatzResearch.WordTrace tailWord_4583798 prefixEnd_4583798 2353691597117962102944503 := by
  unfold tailWord_4583798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449052990480635701100503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111456565231793447478405365 10449052990480635701100503)
  ·
    refine ⟨15673579485720953551650755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10449052990480635701100503 15673579485720953551650755)
    ·
      refine ⟨23510369228581430327476133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15673579485720953551650755 23510369228581430327476133)
      ·
        refine ⟨4408194230359018186401775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23510369228581430327476133 4408194230359018186401775)
        ·
          refine ⟨6612291345538527279602663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4408194230359018186401775 6612291345538527279602663)
          ·
            refine ⟨9918437018307790919403995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6612291345538527279602663 9918437018307790919403995)
            ·
              refine ⟨14877655527461686379105993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9918437018307790919403995 14877655527461686379105993)
              ·
                refine ⟨11158241645596264784329495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14877655527461686379105993 11158241645596264784329495)
                ·
                  refine ⟨16737362468394397176494243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11158241645596264784329495 16737362468394397176494243)
                  ·
                    refine ⟨25106043702591595764741365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16737362468394397176494243 25106043702591595764741365)
                    ·
                      refine ⟨2353691597117962102944503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25106043702591595764741365 2353691597117962102944503)
                      ·
                        rfl

theorem cell23_4583798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4583798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583798 prefixEnd_4583798 := by exact prefixLift 4583798
  have htrace : WordTrace (prefixWord ++ tailWord_4583798) baseStart_4583798 baseEnd_4583798 := by
    simpa [prefixWord, tailWord_4583798, baseEnd_4583798] using wordTrace_append hprefix tailTrace_4583798
  have hstable : (prefixWord ++ tailWord_4583798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583798).length < 2 ^ (prefixWord ++ tailWord_4583798).sum := by decide
  have hdescent : baseEnd_4583798 < baseStart_4583798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583804 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_4583804 : Nat := 118140960795 + 4583804 * 2 ^ 59
def prefixEnd_4583804 : Nat := 4983230072969 + 3 ^ 40 * 4583804 * 2
def baseEnd_4583804 : Nat := 2353694678001889079469475

theorem tailTrace_4583804 : CollatzResearch.WordTrace tailWord_4583804 prefixEnd_4583804 2353694678001889079469475 := by
  unfold tailWord_4583804
  simp only [CollatzResearch.WordTrace]
  refine ⟨83592533342834217121163233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111456711123778956161550977 83592533342834217121163233)
  ·
    refine ⟨62694400007125662840872425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83592533342834217121163233 62694400007125662840872425)
    ·
      refine ⟨47020800005344247130654319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62694400007125662840872425 47020800005344247130654319)
      ·
        refine ⟨70531200008016370695981479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47020800005344247130654319 70531200008016370695981479)
        ·
          refine ⟨105796800012024556043972219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70531200008016370695981479 105796800012024556043972219)
          ·
            refine ⟨158695200018036834065958329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105796800012024556043972219 158695200018036834065958329)
            ·
              refine ⟨119021400013527625549468747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158695200018036834065958329 119021400013527625549468747)
              ·
                refine ⟨178532100020291438324203121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119021400013527625549468747 178532100020291438324203121)
                ·
                  refine ⟨133899075015218578743152341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178532100020291438324203121 133899075015218578743152341)
                  ·
                    refine ⟨3138259570669185439292633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 133899075015218578743152341 3138259570669185439292633)
                    ·
                      refine ⟨2353694678001889079469475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138259570669185439292633 2353694678001889079469475)
                      ·
                        rfl

theorem cell23_4583804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_4583804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583804 prefixEnd_4583804 := by exact prefixLift 4583804
  have htrace : WordTrace (prefixWord ++ tailWord_4583804) baseStart_4583804 baseEnd_4583804 := by
    simpa [prefixWord, tailWord_4583804, baseEnd_4583804] using wordTrace_append hprefix tailTrace_4583804
  have hstable : (prefixWord ++ tailWord_4583804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583804).length < 2 ^ (prefixWord ++ tailWord_4583804).sum := by decide
  have hdescent : baseEnd_4583804 < baseStart_4583804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583818 : List Nat := [3, 1, 2, 5, 1, 2, 2, 7]
def baseStart_4583818 : Nat := 118140960795 + 4583818 * 2 ^ 59
def prefixEnd_4583818 : Nat := 4983230072969 + 3 ^ 40 * 4583818 * 2
def baseEnd_4583818 : Nat := 87174143212261186099793

theorem tailTrace_4583818 : CollatzResearch.WordTrace tailWord_4583818 prefixEnd_4583818 87174143212261186099793 := by
  unfold tailWord_4583818
  simp only [CollatzResearch.WordTrace]
  refine ⟨41796394326904428658334027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111457051538411809755557405 41796394326904428658334027)
  ·
    refine ⟨62694591490356642987501041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41796394326904428658334027 62694591490356642987501041)
    ·
      refine ⟨47020943617767482240625781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62694591490356642987501041 47020943617767482240625781)
      ·
        refine ⟨4408213464165701460058667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47020943617767482240625781 4408213464165701460058667)
        ·
          refine ⟨6612320196248552190088001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4408213464165701460058667 6612320196248552190088001)
          ·
            refine ⟨4959240147186414142566001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6612320196248552190088001 4959240147186414142566001)
            ·
              refine ⟨3719430110389810606924501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4959240147186414142566001 3719430110389810606924501)
              ·
                refine ⟨87174143212261186099793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3719430110389810606924501 87174143212261186099793)
                ·
                  rfl

theorem cell23_4583818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 7].length) (baseStart_4583818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583818 prefixEnd_4583818 := by exact prefixLift 4583818
  have htrace : WordTrace (prefixWord ++ tailWord_4583818) baseStart_4583818 baseEnd_4583818 := by
    simpa [prefixWord, tailWord_4583818, baseEnd_4583818] using wordTrace_append hprefix tailTrace_4583818
  have hstable : (prefixWord ++ tailWord_4583818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583818).length < 2 ^ (prefixWord ++ tailWord_4583818).sum := by decide
  have hdescent : baseEnd_4583818 < baseStart_4583818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583877 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_4583877 : Nat := 118140960795 + 4583877 * 2 ^ 59
def prefixEnd_4583877 : Nat := 4983230072969 + 3 ^ 40 * 4583877 * 2
def baseEnd_4583877 : Nat := 2353732162089667293856639

theorem tailTrace_4583877 : CollatzResearch.WordTrace tailWord_4583877 prefixEnd_4583877 2353732162089667293856639 := by
  unfold tailWord_4583877
  simp only [CollatzResearch.WordTrace]
  refine ⟨167187729214403967709733885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111458486142935978473155923 167187729214403967709733885)
  ·
    refine ⟨62695398455401487891150207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167187729214403967709733885 62695398455401487891150207)
    ·
      refine ⟨94043097683102231836725311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62695398455401487891150207 94043097683102231836725311)
      ·
        refine ⟨141064646524653347755087967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94043097683102231836725311 141064646524653347755087967)
        ·
          refine ⟨211596969786980021632631951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141064646524653347755087967 211596969786980021632631951)
          ·
            refine ⟨317395454680470032448947927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211596969786980021632631951 317395454680470032448947927)
            ·
              refine ⟨476093182020705048673421891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317395454680470032448947927 476093182020705048673421891)
              ·
                refine ⟨714139773031057573010132837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476093182020705048673421891 714139773031057573010132837)
                ·
                  refine ⟨133901207443323294939399907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714139773031057573010132837 133901207443323294939399907)
                  ·
                    refine ⟨200851811164984942409099861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 133901207443323294939399907 200851811164984942409099861)
                    ·
                      refine ⟨2353732162089667293856639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 200851811164984942409099861 2353732162089667293856639)
                      ·
                        rfl

theorem cell23_4583877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_4583877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583877 prefixEnd_4583877 := by exact prefixLift 4583877
  have htrace : WordTrace (prefixWord ++ tailWord_4583877) baseStart_4583877 baseEnd_4583877 := by
    simpa [prefixWord, tailWord_4583877, baseEnd_4583877] using wordTrace_append hprefix tailTrace_4583877
  have hstable : (prefixWord ++ tailWord_4583877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583877).length < 2 ^ (prefixWord ++ tailWord_4583877).sum := by decide
  have hdescent : baseEnd_4583877 < baseStart_4583877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583901 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_4583901 : Nat := 118140960795 + 4583901 * 2 ^ 59
def prefixEnd_4583901 : Nat := 4983230072969 + 3 ^ 40 * 4583901 * 2
def baseEnd_4583901 : Nat := 2353744485625375199956529

theorem tailTrace_4583901 : CollatzResearch.WordTrace tailWord_4583901 prefixEnd_4583901 2353744485625375199956529 := by
  unfold tailWord_4583901
  simp only [CollatzResearch.WordTrace]
  refine ⟨167188604566317019808607557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111459069710878013205738371 167188604566317019808607557)
  ·
    refine ⟨31347863356184441214113917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167188604566317019808607557 31347863356184441214113917)
    ·
      refine ⟨11755448758569165455292719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31347863356184441214113917 11755448758569165455292719)
      ·
        refine ⟨17633173137853748182939079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11755448758569165455292719 17633173137853748182939079)
        ·
          refine ⟨26449759706780622274408619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17633173137853748182939079 26449759706780622274408619)
          ·
            refine ⟨39674639560170933411612929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26449759706780622274408619 39674639560170933411612929)
            ·
              refine ⟨29755979670128200058709697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39674639560170933411612929 29755979670128200058709697)
              ·
                refine ⟨22316984752596150044032273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29755979670128200058709697 22316984752596150044032273)
                ·
                  refine ⟨16737738564447112533024205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22316984752596150044032273 16737738564447112533024205)
                  ·
                    refine ⟨6276651961667667199884077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16737738564447112533024205 6276651961667667199884077)
                    ·
                      refine ⟨2353744485625375199956529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276651961667667199884077 2353744485625375199956529)
                      ·
                        rfl

theorem cell23_4583901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_4583901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583901 prefixEnd_4583901 := by exact prefixLift 4583901
  have htrace : WordTrace (prefixWord ++ tailWord_4583901) baseStart_4583901 baseEnd_4583901 := by
    simpa [prefixWord, tailWord_4583901, baseEnd_4583901] using wordTrace_append hprefix tailTrace_4583901
  have hstable : (prefixWord ++ tailWord_4583901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583901).length < 2 ^ (prefixWord ++ tailWord_4583901).sum := by decide
  have hdescent : baseEnd_4583901 < baseStart_4583901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583904 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 2, 5]
def baseStart_4583904 : Nat := 118140960795 + 4583904 * 2 ^ 59
def prefixEnd_4583904 : Nat := 4983230072969 + 3 ^ 40 * 4583904 * 2
def baseEnd_4583904 : Nat := 784582008689112896073005

theorem tailTrace_4583904 : CollatzResearch.WordTrace tailWord_4583904 prefixEnd_4583904 784582008689112896073005 := by
  unfold tailWord_4583904
  simp only [CollatzResearch.WordTrace]
  refine ⟨83594356992653075660483383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111459142656870767547311177 83594356992653075660483383)
  ·
    refine ⟨125391535488979613490725075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83594356992653075660483383 125391535488979613490725075)
    ·
      refine ⟨188087303233469420236087613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125391535488979613490725075 188087303233469420236087613)
      ·
        refine ⟨70532738712551032588532855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188087303233469420236087613 70532738712551032588532855)
        ·
          refine ⟨105799108068826548882799283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70532738712551032588532855 105799108068826548882799283)
          ·
            refine ⟨158698662103239823324198925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105799108068826548882799283 158698662103239823324198925)
            ·
              refine ⟨59511998288714933746574597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158698662103239823324198925 59511998288714933746574597)
              ·
                refine ⟨11158499679134050077482737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59511998288714933746574597 11158499679134050077482737)
                ·
                  refine ⟨8368874759350537558112053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11158499679134050077482737 8368874759350537558112053)
                  ·
                    refine ⟨784582008689112896073005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8368874759350537558112053 784582008689112896073005)
                    ·
                      rfl

theorem cell23_4583904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_4583904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583904 prefixEnd_4583904 := by exact prefixLift 4583904
  have htrace : WordTrace (prefixWord ++ tailWord_4583904) baseStart_4583904 baseEnd_4583904 := by
    simpa [prefixWord, tailWord_4583904, baseEnd_4583904] using wordTrace_append hprefix tailTrace_4583904
  have hstable : (prefixWord ++ tailWord_4583904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583904).length < 2 ^ (prefixWord ++ tailWord_4583904).sum := by decide
  have hdescent : baseEnd_4583904 < baseStart_4583904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583911 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_4583911 : Nat := 118140960795 + 4583911 * 2 ^ 59
def prefixEnd_4583911 : Nat := 4983230072969 + 3 ^ 40 * 4583911 * 2
def baseEnd_4583911 : Nat := 2353749620431920160831483

theorem tailTrace_4583911 : CollatzResearch.WordTrace tailWord_4583911 prefixEnd_4583911 2353749620431920160831483 := by
  unfold tailWord_4583911
  simp only [CollatzResearch.WordTrace]
  refine ⟨167188969296280791516471587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111459312864187194344314391 167188969296280791516471587)
  ·
    refine ⟨250783453944421187274707381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167188969296280791516471587 250783453944421187274707381)
    ·
      refine ⟨23510948807289486307003817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250783453944421187274707381 23510948807289486307003817)
      ·
        refine ⟨17633211605467114730252863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23510948807289486307003817 17633211605467114730252863)
        ·
          refine ⟨26449817408200672095379295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17633211605467114730252863 26449817408200672095379295)
          ·
            refine ⟨39674726112301008143068943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26449817408200672095379295 39674726112301008143068943)
            ·
              refine ⟨59512089168451512214603415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39674726112301008143068943 59512089168451512214603415)
              ·
                refine ⟨89268133752677268321905123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59512089168451512214603415 89268133752677268321905123)
                ·
                  refine ⟨133902200629015902482857685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89268133752677268321905123 133902200629015902482857685)
                  ·
                    refine ⟨3138332827242560214441977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 133902200629015902482857685 3138332827242560214441977)
                    ·
                      refine ⟨2353749620431920160831483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138332827242560214441977 2353749620431920160831483)
                      ·
                        rfl

theorem cell23_4583911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_4583911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583911 prefixEnd_4583911 := by exact prefixLift 4583911
  have htrace : WordTrace (prefixWord ++ tailWord_4583911) baseStart_4583911 baseEnd_4583911 := by
    simpa [prefixWord, tailWord_4583911, baseEnd_4583911] using wordTrace_append hprefix tailTrace_4583911
  have hstable : (prefixWord ++ tailWord_4583911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583911).length < 2 ^ (prefixWord ++ tailWord_4583911).sum := by decide
  have hdescent : baseEnd_4583911 < baseStart_4583911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583938 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_4583938 : Nat := 118140960795 + 4583938 * 2 ^ 59
def prefixEnd_4583938 : Nat := 4983230072969 + 3 ^ 40 * 4583938 * 2
def baseEnd_4583938 : Nat := 784587828136530518397953

theorem tailTrace_4583938 : CollatzResearch.WordTrace tailWord_4583938 prefixEnd_4583938 784587828136530518397953 := by
  unfold tailWord_4583938
  simp only [CollatzResearch.WordTrace]
  refine ⟨41797488516795743781926117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111459969378121983418469645 41797488516795743781926117)
  ·
    refine ⟨7837029096899201959111147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41797488516795743781926117 7837029096899201959111147)
    ·
      refine ⟨11755543645348802938666721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7837029096899201959111147 11755543645348802938666721)
      ·
        refine ⟨8816657734011602204000041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11755543645348802938666721 8816657734011602204000041)
        ·
          refine ⟨6612493300508701653000031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8816657734011602204000041 6612493300508701653000031)
          ·
            refine ⟨9918739950763052479500047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6612493300508701653000031 9918739950763052479500047)
            ·
              refine ⟨14878109926144578719250071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9918739950763052479500047 14878109926144578719250071)
              ·
                refine ⟨22317164889216868078875107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14878109926144578719250071 22317164889216868078875107)
                ·
                  refine ⟨33475747333825302118312661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22317164889216868078875107 33475747333825302118312661)
                  ·
                    refine ⟨784587828136530518397953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33475747333825302118312661 784587828136530518397953)
                    ·
                      rfl

theorem cell23_4583938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_4583938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583938 prefixEnd_4583938 := by exact prefixLift 4583938
  have htrace : WordTrace (prefixWord ++ tailWord_4583938) baseStart_4583938 baseEnd_4583938 := by
    simpa [prefixWord, tailWord_4583938, baseEnd_4583938] using wordTrace_append hprefix tailTrace_4583938
  have hstable : (prefixWord ++ tailWord_4583938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583938).length < 2 ^ (prefixWord ++ tailWord_4583938).sum := by decide
  have hdescent : baseEnd_4583938 < baseStart_4583938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583941 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_4583941 : Nat := 118140960795 + 4583941 * 2 ^ 59
def prefixEnd_4583941 : Nat := 4983230072969 + 3 ^ 40 * 4583941 * 2
def baseEnd_4583941 : Nat := 2353765024851555043456345

theorem tailTrace_4583941 : CollatzResearch.WordTrace tailWord_4583941 prefixEnd_4583941 2353765024851555043456345 := by
  unfold tailWord_4583941
  simp only [CollatzResearch.WordTrace]
  refine ⟨167190063486172106640063677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111460042324114737760042451 167190063486172106640063677)
  ·
    refine ⟨62696273807314539990023879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167190063486172106640063677 62696273807314539990023879)
    ·
      refine ⟨94044410710971809985035819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62696273807314539990023879 94044410710971809985035819)
      ·
        refine ⟨141066616066457714977553729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94044410710971809985035819 141066616066457714977553729)
        ·
          refine ⟨105799962049843286233165297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141066616066457714977553729 105799962049843286233165297)
          ·
            refine ⟨79349971537382464674873973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105799962049843286233165297 79349971537382464674873973)
            ·
              refine ⟨7439059831629606063269435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79349971537382464674873973 7439059831629606063269435)
              ·
                refine ⟨11158589747444409094904153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7439059831629606063269435 11158589747444409094904153)
                ·
                  refine ⟨8368942310583306821178115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11158589747444409094904153 8368942310583306821178115)
                  ·
                    refine ⟨12553413465874960231767173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8368942310583306821178115 12553413465874960231767173)
                    ·
                      refine ⟨2353765024851555043456345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12553413465874960231767173 2353765024851555043456345)
                      ·
                        rfl

theorem cell23_4583941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_4583941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583941 prefixEnd_4583941 := by exact prefixLift 4583941
  have htrace : WordTrace (prefixWord ++ tailWord_4583941) baseStart_4583941 baseEnd_4583941 := by
    simpa [prefixWord, tailWord_4583941, baseEnd_4583941] using wordTrace_append hprefix tailTrace_4583941
  have hstable : (prefixWord ++ tailWord_4583941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583941).length < 2 ^ (prefixWord ++ tailWord_4583941).sum := by decide
  have hdescent : baseEnd_4583941 < baseStart_4583941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4583942 : List Nat := [6, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_4583942 : Nat := 118140960795 + 4583942 * 2 ^ 59
def prefixEnd_4583942 : Nat := 4983230072969 + 3 ^ 40 * 4583942 * 2
def baseEnd_4583942 : Nat := 261529504259134393282649

theorem tailTrace_4583942 : CollatzResearch.WordTrace tailWord_4583942 prefixEnd_4583942 261529504259134393282649 := by
  unfold tailWord_4583942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5224690623724015119089065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111460066639445655873900053 5224690623724015119089065)
  ·
    refine ⟨3918517967793011339316799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5224690623724015119089065 3918517967793011339316799)
    ·
      refine ⟨5877776951689517008975199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3918517967793011339316799 5877776951689517008975199)
      ·
        refine ⟨8816665427534275513462799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5877776951689517008975199 8816665427534275513462799)
        ·
          refine ⟨13224998141301413270194199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8816665427534275513462799 13224998141301413270194199)
          ·
            refine ⟨19837497211952119905291299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13224998141301413270194199 19837497211952119905291299)
            ·
              refine ⟨29756245817928179857936949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19837497211952119905291299 29756245817928179857936949)
              ·
                refine ⟨2789648045430766861681589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29756245817928179857936949 2789648045430766861681589)
                ·
                  refine ⟨261529504259134393282649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2789648045430766861681589 261529504259134393282649)
                  ·
                    rfl

theorem cell23_4583942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_4583942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4583942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4583942 prefixEnd_4583942 := by exact prefixLift 4583942
  have htrace : WordTrace (prefixWord ++ tailWord_4583942) baseStart_4583942 baseEnd_4583942 := by
    simpa [prefixWord, tailWord_4583942, baseEnd_4583942] using wordTrace_append hprefix tailTrace_4583942
  have hstable : (prefixWord ++ tailWord_4583942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4583942).length < 2 ^ (prefixWord ++ tailWord_4583942).sum := by decide
  have hdescent : baseEnd_4583942 < baseStart_4583942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4583942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584011 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 1, 5]
def baseStart_4584011 : Nat := 118140960795 + 4584011 * 2 ^ 59
def prefixEnd_4584011 : Nat := 4983230072969 + 3 ^ 40 * 4584011 * 2
def baseEnd_4584011 : Nat := 784600322832456589860341

theorem tailTrace_4584011 : CollatzResearch.WordTrace tailWord_4584011 prefixEnd_4584011 784600322832456589860341 := by
  unfold tailWord_4584011
  simp only [CollatzResearch.WordTrace]
  refine ⟨167192616595918508595111887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111461744397279005730074591 167192616595918508595111887)
  ·
    refine ⟨250788924893877762892667831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167192616595918508595111887 250788924893877762892667831)
    ·
      refine ⟨376183387340816644339001747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250788924893877762892667831 376183387340816644339001747)
      ·
        refine ⟨564275081011224966508502621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376183387340816644339001747 564275081011224966508502621)
        ·
          refine ⟨211603155379209362440688483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 564275081011224966508502621 211603155379209362440688483)
          ·
            refine ⟨317404733068814043661032725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211603155379209362440688483 317404733068814043661032725)
            ·
              refine ⟨14878346862600658296610909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 317404733068814043661032725 14878346862600658296610909)
              ·
                refine ⟨5579380073475246861229091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14878346862600658296610909 5579380073475246861229091)
                ·
                  refine ⟨8369070110212870291843637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5579380073475246861229091 8369070110212870291843637)
                  ·
                    refine ⟨784600322832456589860341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8369070110212870291843637 784600322832456589860341)
                    ·
                      rfl

theorem cell23_4584011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 5].length) (baseStart_4584011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584011 prefixEnd_4584011 := by exact prefixLift 4584011
  have htrace : WordTrace (prefixWord ++ tailWord_4584011) baseStart_4584011 baseEnd_4584011 := by
    simpa [prefixWord, tailWord_4584011, baseEnd_4584011] using wordTrace_append hprefix tailTrace_4584011
  have hstable : (prefixWord ++ tailWord_4584011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584011).length < 2 ^ (prefixWord ++ tailWord_4584011).sum := by decide
  have hdescent : baseEnd_4584011 < baseStart_4584011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584045 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_4584045 : Nat := 118140960795 + 4584045 * 2 ^ 59
def prefixEnd_4584045 : Nat := 4983230072969 + 3 ^ 40 * 4584045 * 2
def baseEnd_4584045 : Nat := 784606142279874212185289

theorem tailTrace_4584045 : CollatzResearch.WordTrace tailWord_4584045 prefixEnd_4584045 784606142279874212185289 := by
  unfold tailWord_4584045
  simp only [CollatzResearch.WordTrace]
  refine ⟨167193856677795332401849589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111462571118530221601233059 167193856677795332401849589)
  ·
    refine ⟨15674424063543312412673399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167193856677795332401849589 15674424063543312412673399)
    ·
      refine ⟨23511636095314968619010099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15674424063543312412673399 23511636095314968619010099)
      ·
        refine ⟨35267454142972452928515149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23511636095314968619010099 35267454142972452928515149)
        ·
          refine ⟨13225295303614669848193181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35267454142972452928515149 13225295303614669848193181)
          ·
            refine ⟨4959485738855501193072443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13225295303614669848193181 4959485738855501193072443)
            ·
              refine ⟨7439228608283251789608665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959485738855501193072443 7439228608283251789608665)
              ·
                refine ⟨5579421456212438842206499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7439228608283251789608665 5579421456212438842206499)
                ·
                  refine ⟨8369132184318658263309749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5579421456212438842206499 8369132184318658263309749)
                  ·
                    refine ⟨784606142279874212185289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8369132184318658263309749 784606142279874212185289)
                    ·
                      rfl

theorem cell23_4584045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_4584045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584045 prefixEnd_4584045 := by exact prefixLift 4584045
  have htrace : WordTrace (prefixWord ++ tailWord_4584045) baseStart_4584045 baseEnd_4584045 := by
    simpa [prefixWord, tailWord_4584045, baseEnd_4584045] using wordTrace_append hprefix tailTrace_4584045
  have hstable : (prefixWord ++ tailWord_4584045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584045).length < 2 ^ (prefixWord ++ tailWord_4584045).sum := by decide
  have hdescent : baseEnd_4584045 < baseStart_4584045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584048 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 4]
def baseStart_4584048 : Nat := 118140960795 + 4584048 * 2 ^ 59
def prefixEnd_4584048 : Nat := 4983230072969 + 3 ^ 40 * 4584048 * 2
def baseEnd_4584048 : Nat := 2353819967281586124818353

theorem tailTrace_4584048 : CollatzResearch.WordTrace tailWord_4584048 prefixEnd_4584048 2353819967281586124818353 := by
  unfold tailWord_4584048
  simp only [CollatzResearch.WordTrace]
  refine ⟨83596983048392231957104399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111462644064522975942805865 83596983048392231957104399)
  ·
    refine ⟨125395474572588347935656599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83596983048392231957104399 125395474572588347935656599)
    ·
      refine ⟨188093211858882521903484899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125395474572588347935656599 188093211858882521903484899)
      ·
        refine ⟨282139817788323782855227349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188093211858882521903484899 282139817788323782855227349)
        ·
          refine ⟨6612651979413838660669391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 282139817788323782855227349 6612651979413838660669391)
          ·
            refine ⟨9918977969120757991004087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6612651979413838660669391 9918977969120757991004087)
            ·
              refine ⟨14878466953681136986506131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9918977969120757991004087 14878466953681136986506131)
              ·
                refine ⟨22317700430521705479759197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14878466953681136986506131 22317700430521705479759197)
                ·
                  refine ⟨8369137661445639554909699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22317700430521705479759197 8369137661445639554909699)
                  ·
                    refine ⟨12553706492168459332364549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8369137661445639554909699 12553706492168459332364549)
                    ·
                      refine ⟨2353819967281586124818353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12553706492168459332364549 2353819967281586124818353)
                      ·
                        rfl

theorem cell23_4584048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_4584048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584048 prefixEnd_4584048 := by exact prefixLift 4584048
  have htrace : WordTrace (prefixWord ++ tailWord_4584048) baseStart_4584048 baseEnd_4584048 := by
    simpa [prefixWord, tailWord_4584048, baseEnd_4584048] using wordTrace_append hprefix tailTrace_4584048
  have hstable : (prefixWord ++ tailWord_4584048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584048).length < 2 ^ (prefixWord ++ tailWord_4584048).sum := by decide
  have hdescent : baseEnd_4584048 < baseStart_4584048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584065 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_4584065 : Nat := 118140960795 + 4584065 * 2 ^ 59
def prefixEnd_4584065 : Nat := 4983230072969 + 3 ^ 40 * 4584065 * 2
def baseEnd_4584065 : Nat := 2353828696452712558305775

theorem tailTrace_4584065 : CollatzResearch.WordTrace tailWord_4584065 prefixEnd_4584065 2353828696452712558305775 := by
  unfold tailWord_4584065
  simp only [CollatzResearch.WordTrace]
  refine ⟨167194586137722875817577649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111463057425148583878385099 167194586137722875817577649)
  ·
    refine ⟨125395939603292156863183237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167194586137722875817577649 125395939603292156863183237)
    ·
      refine ⟨23511738675617279411846857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125395939603292156863183237 23511738675617279411846857)
      ·
        refine ⟨17633804006712959558885143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23511738675617279411846857 17633804006712959558885143)
        ·
          refine ⟨26450706010069439338327715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17633804006712959558885143 26450706010069439338327715)
          ·
            refine ⟨39676059015104159007491573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26450706010069439338327715 39676059015104159007491573)
            ·
              refine ⟨3719630532666014906952335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39676059015104159007491573 3719630532666014906952335)
              ·
                refine ⟨5579445798999022360428503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3719630532666014906952335 5579445798999022360428503)
                ·
                  refine ⟨8369168698498533540642755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5579445798999022360428503 8369168698498533540642755)
                  ·
                    refine ⟨12553753047747800310964133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8369168698498533540642755 12553753047747800310964133)
                    ·
                      refine ⟨2353828696452712558305775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12553753047747800310964133 2353828696452712558305775)
                      ·
                        rfl

theorem cell23_4584065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_4584065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584065 prefixEnd_4584065 := by exact prefixLift 4584065
  have htrace : WordTrace (prefixWord ++ tailWord_4584065) baseStart_4584065 baseEnd_4584065 := by
    simpa [prefixWord, tailWord_4584065, baseEnd_4584065] using wordTrace_append hprefix tailTrace_4584065
  have hstable : (prefixWord ++ tailWord_4584065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584065).length < 2 ^ (prefixWord ++ tailWord_4584065).sum := by decide
  have hdescent : baseEnd_4584065 < baseStart_4584065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584068 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_4584068 : Nat := 118140960795 + 4584068 * 2 ^ 59
def prefixEnd_4584068 : Nat := 4983230072969 + 3 ^ 40 * 4584068 * 2
def baseEnd_4584068 : Nat := 2353830236894676046568261

theorem tailTrace_4584068 : CollatzResearch.WordTrace tailWord_4584068 prefixEnd_4584068 2353830236894676046568261 := by
  unfold tailWord_4584068
  simp only [CollatzResearch.WordTrace]
  refine ⟨83597347778356003664968429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111463130371141338219957905 83597347778356003664968429)
  ·
    refine ⟨31349005416883501374363161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83597347778356003664968429 31349005416883501374363161)
    ·
      refine ⟨23511754062662626030772371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31349005416883501374363161 23511754062662626030772371)
      ·
        refine ⟨35267631093993939046158557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23511754062662626030772371 35267631093993939046158557)
        ·
          refine ⟨13225361660247727142309459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35267631093993939046158557 13225361660247727142309459)
          ·
            refine ⟨19838042490371590713464189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13225361660247727142309459 19838042490371590713464189)
            ·
              refine ⟨7439265933889346517549071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19838042490371590713464189 7439265933889346517549071)
              ·
                refine ⟨11158898900834019776323607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7439265933889346517549071 11158898900834019776323607)
                ·
                  refine ⟨16738348351251029664485411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11158898900834019776323607 16738348351251029664485411)
                  ·
                    refine ⟨25107522526876544496728117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16738348351251029664485411 25107522526876544496728117)
                    ·
                      refine ⟨2353830236894676046568261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25107522526876544496728117 2353830236894676046568261)
                      ·
                        rfl

theorem cell23_4584068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_4584068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584068 prefixEnd_4584068 := by exact prefixLift 4584068
  have htrace : WordTrace (prefixWord ++ tailWord_4584068) baseStart_4584068 baseEnd_4584068 := by
    simpa [prefixWord, tailWord_4584068, baseEnd_4584068] using wordTrace_append hprefix tailTrace_4584068
  have hstable : (prefixWord ++ tailWord_4584068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584068).length < 2 ^ (prefixWord ++ tailWord_4584068).sum := by decide
  have hdescent : baseEnd_4584068 < baseStart_4584068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584119 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 1, 2, 3]
def baseStart_4584119 : Nat := 118140960795 + 4584119 * 2 ^ 59
def prefixEnd_4584119 : Nat := 4983230072969 + 3 ^ 40 * 4584119 * 2
def baseEnd_4584119 : Nat := 2353856424408055347030527

theorem tailTrace_4584119 : CollatzResearch.WordTrace tailWord_4584119 prefixEnd_4584119 2353856424408055347030527 := by
  unfold tailWord_4584119
  simp only [CollatzResearch.WordTrace]
  refine ⟨167196555679527243040043411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111464370453018162026695607 167196555679527243040043411)
  ·
    refine ⟨250794833519290864560065117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167196555679527243040043411 250794833519290864560065117)
    ·
      refine ⟨94048062569734074210024419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250794833519290864560065117 94048062569734074210024419)
      ·
        refine ⟨141072093854601111315036629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94048062569734074210024419 141072093854601111315036629)
        ·
          refine ⟨3306377199717213546446171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 141072093854601111315036629 3306377199717213546446171)
          ·
            refine ⟨4959565799575820319669257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306377199717213546446171 4959565799575820319669257)
            ·
              refine ⟨3719674349681865239751943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4959565799575820319669257 3719674349681865239751943)
              ·
                refine ⟨5579511524522797859627915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3719674349681865239751943 5579511524522797859627915)
                ·
                  refine ⟨8369267286784196789441873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5579511524522797859627915 8369267286784196789441873)
                  ·
                    refine ⟨6276950465088147592081405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8369267286784196789441873 6276950465088147592081405)
                    ·
                      refine ⟨2353856424408055347030527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276950465088147592081405 2353856424408055347030527)
                      ·
                        rfl

theorem cell23_4584119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_4584119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584119 prefixEnd_4584119 := by exact prefixLift 4584119
  have htrace : WordTrace (prefixWord ++ tailWord_4584119) baseStart_4584119 baseEnd_4584119 := by
    simpa [prefixWord, tailWord_4584119, baseEnd_4584119] using wordTrace_append hprefix tailTrace_4584119
  have hstable : (prefixWord ++ tailWord_4584119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584119).length < 2 ^ (prefixWord ++ tailWord_4584119).sum := by decide
  have hdescent : baseEnd_4584119 < baseStart_4584119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584132 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_4584132 : Nat := 118140960795 + 4584132 * 2 ^ 59
def prefixEnd_4584132 : Nat := 4983230072969 + 3 ^ 40 * 4584132 * 2
def baseEnd_4584132 : Nat := 2353863099656563796167967

theorem tailTrace_4584132 : CollatzResearch.WordTrace tailWord_4584132 prefixEnd_4584132 2353863099656563796167967 := by
  unfold tailWord_4584132
  simp only [CollatzResearch.WordTrace]
  refine ⟨83598514914240073130133325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111464686552320097506844433 83598514914240073130133325)
  ·
    refine ⟨31349443092840027423799997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83598514914240073130133325 31349443092840027423799997)
    ·
      refine ⟨11756041159815010283924999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31349443092840027423799997 11756041159815010283924999)
      ·
        refine ⟨17634061739722515425887499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11756041159815010283924999 17634061739722515425887499)
        ·
          refine ⟨26451092609583773138831249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17634061739722515425887499 26451092609583773138831249)
          ·
            refine ⟨19838319457187829854123437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26451092609583773138831249 19838319457187829854123437)
            ·
              refine ⟨7439369796445436195296289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19838319457187829854123437 7439369796445436195296289)
              ·
                refine ⟨5579527347334077146472217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7439369796445436195296289 5579527347334077146472217)
                ·
                  refine ⟨4184645510500557859854163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5579527347334077146472217 4184645510500557859854163)
                  ·
                    refine ⟨6276968265750836789781245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4184645510500557859854163 6276968265750836789781245)
                    ·
                      refine ⟨2353863099656563796167967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276968265750836789781245 2353863099656563796167967)
                      ·
                        rfl

theorem cell23_4584132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_4584132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584132 prefixEnd_4584132 := by exact prefixLift 4584132
  have htrace : WordTrace (prefixWord ++ tailWord_4584132) baseStart_4584132 baseEnd_4584132 := by
    simpa [prefixWord, tailWord_4584132, baseEnd_4584132] using wordTrace_append hprefix tailTrace_4584132
  have hstable : (prefixWord ++ tailWord_4584132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584132).length < 2 ^ (prefixWord ++ tailWord_4584132).sum := by decide
  have hdescent : baseEnd_4584132 < baseStart_4584132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584149 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4584149 : Nat := 118140960795 + 4584149 * 2 ^ 59
def prefixEnd_4584149 : Nat := 4983230072969 + 3 ^ 40 * 4584149 * 2
def baseEnd_4584149 : Nat := 2353871828827690229655389

theorem tailTrace_4584149 : CollatzResearch.WordTrace tailWord_4584149 prefixEnd_4584149 2353871828827690229655389 := by
  unfold tailWord_4584149
  simp only [CollatzResearch.WordTrace]
  refine ⟨167197649869418558163635501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111465099912945705442423667 167197649869418558163635501)
  ·
    refine ⟨62699118701031959311363313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167197649869418558163635501 62699118701031959311363313)
    ·
      refine ⟨47024339025773969483522485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62699118701031959311363313 47024339025773969483522485)
      ·
        refine ⟨4408531783666309639080233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47024339025773969483522485 4408531783666309639080233)
        ·
          refine ⟨3306398837749732229310175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4408531783666309639080233 3306398837749732229310175)
          ·
            refine ⟨4959598256624598343965263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306398837749732229310175 4959598256624598343965263)
            ·
              refine ⟨7439397384936897515947895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959598256624598343965263 7439397384936897515947895)
              ·
                refine ⟨11159096077405346273921843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7439397384936897515947895 11159096077405346273921843)
                ·
                  refine ⟨16738644116108019410882765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11159096077405346273921843 16738644116108019410882765)
                  ·
                    refine ⟨6276991543540507279081037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16738644116108019410882765 6276991543540507279081037)
                    ·
                      refine ⟨2353871828827690229655389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6276991543540507279081037 2353871828827690229655389)
                      ·
                        rfl

theorem cell23_4584149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4584149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584149 prefixEnd_4584149 := by exact prefixLift 4584149
  have htrace : WordTrace (prefixWord ++ tailWord_4584149) baseStart_4584149 baseEnd_4584149 := by
    simpa [prefixWord, tailWord_4584149, baseEnd_4584149] using wordTrace_append hprefix tailTrace_4584149
  have hstable : (prefixWord ++ tailWord_4584149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584149).length < 2 ^ (prefixWord ++ tailWord_4584149).sum := by decide
  have hdescent : baseEnd_4584149 < baseStart_4584149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584201 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_4584201 : Nat := 118140960795 + 4584201 * 2 ^ 59
def prefixEnd_4584201 : Nat := 4983230072969 + 3 ^ 40 * 4584201 * 2
def baseEnd_4584201 : Nat := 2353898529821724026205149

theorem tailTrace_4584201 : CollatzResearch.WordTrace tailWord_4584201 prefixEnd_4584201 2353898529821724026205149 := by
  unfold tailWord_4584201
  simp only [CollatzResearch.WordTrace]
  refine ⟨167199546465230171044528457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111466364310153447363018971 167199546465230171044528457)
  ·
    refine ⟨125399659848922628283396343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167199546465230171044528457 125399659848922628283396343)
    ·
      refine ⟨188099489773383942425094515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125399659848922628283396343 188099489773383942425094515)
      ·
        refine ⟨282149234660075913637641773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188099489773383942425094515 282149234660075913637641773)
        ·
          refine ⟨105805962997528467614115665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282149234660075913637641773 105805962997528467614115665)
          ·
            refine ⟨79354472248146350710586749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105805962997528467614115665 79354472248146350710586749)
            ·
              refine ⟨29757927093054881516470031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79354472248146350710586749 29757927093054881516470031)
              ·
                refine ⟨44636890639582322274705047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29757927093054881516470031 44636890639582322274705047)
                ·
                  refine ⟨66955335959373483412057571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44636890639582322274705047 66955335959373483412057571)
                  ·
                    refine ⟨100433003939060225118086357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66955335959373483412057571 100433003939060225118086357)
                    ·
                      refine ⟨2353898529821724026205149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100433003939060225118086357 2353898529821724026205149)
                      ·
                        rfl

theorem cell23_4584201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_4584201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584201 prefixEnd_4584201 := by exact prefixLift 4584201
  have htrace : WordTrace (prefixWord ++ tailWord_4584201) baseStart_4584201 baseEnd_4584201 := by
    simpa [prefixWord, tailWord_4584201, baseEnd_4584201] using wordTrace_append hprefix tailTrace_4584201
  have hstable : (prefixWord ++ tailWord_4584201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584201).length < 2 ^ (prefixWord ++ tailWord_4584201).sum := by decide
  have hdescent : baseEnd_4584201 < baseStart_4584201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584245 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_4584245 : Nat := 118140960795 + 4584245 * 2 ^ 59
def prefixEnd_4584245 : Nat := 4983230072969 + 3 ^ 40 * 4584245 * 2
def baseEnd_4584245 : Nat := 2353921122970521854054947

theorem tailTrace_4584245 : CollatzResearch.WordTrace tailWord_4584245 prefixEnd_4584245 2353921122970521854054947 := by
  unfold tailWord_4584245
  simp only [CollatzResearch.WordTrace]
  refine ⟨167201151277070766559130189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111467434184713844372753459 167201151277070766559130189)
  ·
    refine ⟨62700431728901537459673821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167201151277070766559130189 62700431728901537459673821)
    ·
      refine ⟨23512661898338076547377683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62700431728901537459673821 23512661898338076547377683)
      ·
        refine ⟨35268992847507114821066525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23512661898338076547377683 35268992847507114821066525)
        ·
          refine ⟨13225872317815168057899947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35268992847507114821066525 13225872317815168057899947)
          ·
            refine ⟨19838808476722752086849921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13225872317815168057899947 19838808476722752086849921)
            ·
              refine ⟨14879106357542064065137441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19838808476722752086849921 14879106357542064065137441)
              ·
                refine ⟨11159329768156548048853081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14879106357542064065137441 11159329768156548048853081)
                ·
                  refine ⟨8369497326117411036639811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11159329768156548048853081 8369497326117411036639811)
                  ·
                    refine ⟨12554245989176116554959717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8369497326117411036639811 12554245989176116554959717)
                    ·
                      refine ⟨2353921122970521854054947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12554245989176116554959717 2353921122970521854054947)
                      ·
                        rfl

theorem cell23_4584245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_4584245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584245 prefixEnd_4584245 := by exact prefixLift 4584245
  have htrace : WordTrace (prefixWord ++ tailWord_4584245) baseStart_4584245 baseEnd_4584245 := by
    simpa [prefixWord, tailWord_4584245, baseEnd_4584245] using wordTrace_append hprefix tailTrace_4584245
  have hstable : (prefixWord ++ tailWord_4584245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584245).length < 2 ^ (prefixWord ++ tailWord_4584245).sum := by decide
  have hdescent : baseEnd_4584245 < baseStart_4584245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584246 : List Nat := [5, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_4584246 : Nat := 118140960795 + 4584246 * 2 ^ 59
def prefixEnd_4584246 : Nat := 4983230072969 + 3 ^ 40 * 4584246 * 2
def baseEnd_4584246 : Nat := 261546848494575150015827

theorem tailTrace_4584246 : CollatzResearch.WordTrace tailWord_4584246 prefixEnd_4584246 261546848494575150015827 := by
  unfold tailWord_4584246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10450074234379196483119787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111467458500044762486611061 10450074234379196483119787)
  ·
    refine ⟨15675111351568794724679681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10450074234379196483119787 15675111351568794724679681)
    ·
      refine ⟨11756333513676596043509761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15675111351568794724679681 11756333513676596043509761)
      ·
        refine ⟨8817250135257447032632321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11756333513676596043509761 8817250135257447032632321)
        ·
          refine ⟨6612937601443085274474241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8817250135257447032632321 6612937601443085274474241)
          ·
            refine ⟨4959703201082313955855681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6612937601443085274474241 4959703201082313955855681)
            ·
              refine ⟨3719777400811735466891761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4959703201082313955855681 3719777400811735466891761)
              ·
                refine ⟨2789833050608801600168821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3719777400811735466891761 2789833050608801600168821)
                ·
                  refine ⟨261546848494575150015827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2789833050608801600168821 261546848494575150015827)
                  ·
                    rfl

theorem cell23_4584246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_4584246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584246 prefixEnd_4584246 := by exact prefixLift 4584246
  have htrace : WordTrace (prefixWord ++ tailWord_4584246) baseStart_4584246 baseEnd_4584246 := by
    simpa [prefixWord, tailWord_4584246, baseEnd_4584246] using wordTrace_append hprefix tailTrace_4584246
  have hstable : (prefixWord ++ tailWord_4584246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584246).length < 2 ^ (prefixWord ++ tailWord_4584246).sum := by decide
  have hdescent : baseEnd_4584246 < baseStart_4584246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584282 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_4584282 : Nat := 118140960795 + 4584282 * 2 ^ 59
def prefixEnd_4584282 : Nat := 4983230072969 + 3 ^ 40 * 4584282 * 2
def baseEnd_4584282 : Nat := 2353940121754738209292277

theorem tailTrace_4584282 : CollatzResearch.WordTrace tailWord_4584282 prefixEnd_4584282 2353940121754738209292277 := by
  unfold tailWord_4584282
  simp only [CollatzResearch.WordTrace]
  refine ⟨41800625194484180469556775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111468333851957814585484733 41800625194484180469556775)
  ·
    refine ⟨62700937791726270704335163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41800625194484180469556775 62700937791726270704335163)
    ·
      refine ⟨94051406687589406056502745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62700937791726270704335163 94051406687589406056502745)
      ·
        refine ⟨70538555015692054542377059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94051406687589406056502745 70538555015692054542377059)
        ·
          refine ⟨105807832523538081813565589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70538555015692054542377059 105807832523538081813565589)
          ·
            refine ⟨4959742149540847585010887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105807832523538081813565589 4959742149540847585010887)
            ·
              refine ⟨7439613224311271377516331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959742149540847585010887 7439613224311271377516331)
              ·
                refine ⟨11159419836466907066274497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7439613224311271377516331 11159419836466907066274497)
                ·
                  refine ⟨8369564877350180299705873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11159419836466907066274497 8369564877350180299705873)
                  ·
                    refine ⟨6277173658012635224779405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8369564877350180299705873 6277173658012635224779405)
                    ·
                      refine ⟨2353940121754738209292277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6277173658012635224779405 2353940121754738209292277)
                      ·
                        rfl

theorem cell23_4584282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_4584282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584282 prefixEnd_4584282 := by exact prefixLift 4584282
  have htrace : WordTrace (prefixWord ++ tailWord_4584282) baseStart_4584282 baseEnd_4584282 := by
    simpa [prefixWord, tailWord_4584282, baseEnd_4584282] using wordTrace_append hprefix tailTrace_4584282
  have hstable : (prefixWord ++ tailWord_4584282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584282).length < 2 ^ (prefixWord ++ tailWord_4584282).sum := by decide
  have hdescent : baseEnd_4584282 < baseStart_4584282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584352 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 5, 2, 2]
def baseStart_4584352 : Nat := 118140960795 + 4584352 * 2 ^ 59
def prefixEnd_4584352 : Nat := 4983230072969 + 3 ^ 40 * 4584352 * 2
def baseEnd_4584352 : Nat := 2353976065400552935416955

theorem tailTrace_4584352 : CollatzResearch.WordTrace tailWord_4584352 prefixEnd_4584352 2353976065400552935416955 := by
  unfold tailWord_4584352
  simp only [CollatzResearch.WordTrace]
  refine ⟨83602526943841561916637655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111470035925122082555516873 83602526943841561916637655)
  ·
    refine ⟨125403790415762342874956483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83602526943841561916637655 125403790415762342874956483)
    ·
      refine ⟨188105685623643514312434725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125403790415762342874956483 188105685623643514312434725)
      ·
        refine ⟨35269816054433158933581511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188105685623643514312434725 35269816054433158933581511)
        ·
          refine ⟨52904724081649738400372267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35269816054433158933581511 52904724081649738400372267)
          ·
            refine ⟨79357086122474607600558401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52904724081649738400372267 79357086122474607600558401)
            ·
              refine ⟨59517814591855955700418801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79357086122474607600558401 59517814591855955700418801)
              ·
                refine ⟨44638360943891966775314101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59517814591855955700418801 44638360943891966775314101)
                ·
                  refine ⟨4184846338489871885185697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44638360943891966775314101 4184846338489871885185697)
                  ·
                    refine ⟨3138634753867403913889273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4184846338489871885185697 3138634753867403913889273)
                    ·
                      refine ⟨2353976065400552935416955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138634753867403913889273 2353976065400552935416955)
                      ·
                        rfl

theorem cell23_4584352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_4584352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584352 prefixEnd_4584352 := by exact prefixLift 4584352
  have htrace : WordTrace (prefixWord ++ tailWord_4584352) baseStart_4584352 baseEnd_4584352 := by
    simpa [prefixWord, tailWord_4584352, baseEnd_4584352] using wordTrace_append hprefix tailTrace_4584352
  have hstable : (prefixWord ++ tailWord_4584352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584352).length < 2 ^ (prefixWord ++ tailWord_4584352).sum := by decide
  have hdescent : baseEnd_4584352 < baseStart_4584352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584378 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_4584378 : Nat := 118140960795 + 4584378 * 2 ^ 59
def prefixEnd_4584378 : Nat := 4983230072969 + 3 ^ 40 * 4584378 * 2
def baseEnd_4584378 : Nat := 2353989415897569833691835

theorem tailTrace_4584378 : CollatzResearch.WordTrace tailWord_4584378 prefixEnd_4584378 2353989415897569833691835 := by
  unfold tailWord_4584378
  simp only [CollatzResearch.WordTrace]
  refine ⟨41801500546397232568430447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111470668123725953515814525 41801500546397232568430447)
  ·
    refine ⟨62702250819595848852645671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41801500546397232568430447 62702250819595848852645671)
    ·
      refine ⟨94053376229393773278968507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62702250819595848852645671 94053376229393773278968507)
      ·
        refine ⟨141080064344090659918452761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94053376229393773278968507 141080064344090659918452761)
        ·
          refine ⟨105810048258067994938839571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141080064344090659918452761 105810048258067994938839571)
          ·
            refine ⟨158715072387101992408259357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105810048258067994938839571 158715072387101992408259357)
            ·
              refine ⟨59518152145163247153097259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158715072387101992408259357 59518152145163247153097259)
              ·
                refine ⟨89277228217744870729645889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59518152145163247153097259 89277228217744870729645889)
                ·
                  refine ⟨66957921163308653047234417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89277228217744870729645889 66957921163308653047234417)
                  ·
                    refine ⟨50218440872481489785425813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66957921163308653047234417 50218440872481489785425813)
                    ·
                      refine ⟨2353989415897569833691835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50218440872481489785425813 2353989415897569833691835)
                      ·
                        rfl

theorem cell23_4584378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_4584378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584378 prefixEnd_4584378 := by exact prefixLift 4584378
  have htrace : WordTrace (prefixWord ++ tailWord_4584378) baseStart_4584378 baseEnd_4584378 := by
    simpa [prefixWord, tailWord_4584378, baseEnd_4584378] using wordTrace_append hprefix tailTrace_4584378
  have hstable : (prefixWord ++ tailWord_4584378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584378).length < 2 ^ (prefixWord ++ tailWord_4584378).sum := by decide
  have hdescent : baseEnd_4584378 < baseStart_4584378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584402 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4584402 : Nat := 118140960795 + 4584402 * 2 ^ 59
def prefixEnd_4584402 : Nat := 4983230072969 + 3 ^ 40 * 4584402 * 2
def baseEnd_4584402 : Nat := 2354001739433277739791725

theorem tailTrace_4584402 : CollatzResearch.WordTrace tailWord_4584402 prefixEnd_4584402 2354001739433277739791725 := by
  unfold tailWord_4584402
  simp only [CollatzResearch.WordTrace]
  refine ⟨41801719384375495593148865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111471251691667988248396973 41801719384375495593148865)
  ·
    refine ⟨31351289538281621694861649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41801719384375495593148865 31351289538281621694861649)
    ·
      refine ⟨23513467153711216271146237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31351289538281621694861649 23513467153711216271146237)
      ·
        refine ⟨8817550182641706101679839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23513467153711216271146237 8817550182641706101679839)
        ·
          refine ⟨13226325273962559152519759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8817550182641706101679839 13226325273962559152519759)
          ·
            refine ⟨19839487910943838728779639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13226325273962559152519759 19839487910943838728779639)
            ·
              refine ⟨29759231866415758093169459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19839487910943838728779639 29759231866415758093169459)
              ·
                refine ⟨44638847799623637139754189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29759231866415758093169459 44638847799623637139754189)
                ·
                  refine ⟨16739567924858863927407821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44638847799623637139754189 16739567924858863927407821)
                  ·
                    refine ⟨6277337971822073972777933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16739567924858863927407821 6277337971822073972777933)
                    ·
                      refine ⟨2354001739433277739791725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6277337971822073972777933 2354001739433277739791725)
                      ·
                        rfl

theorem cell23_4584402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4584402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584402 prefixEnd_4584402 := by exact prefixLift 4584402
  have htrace : WordTrace (prefixWord ++ tailWord_4584402) baseStart_4584402 baseEnd_4584402 := by
    simpa [prefixWord, tailWord_4584402, baseEnd_4584402] using wordTrace_append hprefix tailTrace_4584402
  have hstable : (prefixWord ++ tailWord_4584402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584402).length < 2 ^ (prefixWord ++ tailWord_4584402).sum := by decide
  have hdescent : baseEnd_4584402 < baseStart_4584402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584419 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 3]
def baseStart_4584419 : Nat := 118140960795 + 4584419 * 2 ^ 59
def prefixEnd_4584419 : Nat := 4983230072969 + 3 ^ 40 * 4584419 * 2
def baseEnd_4584419 : Nat := 2354010468604404173279147

theorem tailTrace_4584419 : CollatzResearch.WordTrace tailWord_4584419 prefixEnd_4584419 2354010468604404173279147 := by
  unfold tailWord_4584419
  simp only [CollatzResearch.WordTrace]
  refine ⟨167207497578440394275964311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111471665052293596183976207 167207497578440394275964311)
  ·
    refine ⟨250811246367660591413946467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167207497578440394275964311 250811246367660591413946467)
    ·
      refine ⟨376216869551490887120919701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250811246367660591413946467 376216869551490887120919701)
      ·
        refine ⟨17635165760226135333793111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 376216869551490887120919701 17635165760226135333793111)
        ·
          refine ⟨26452748640339203000689667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17635165760226135333793111 26452748640339203000689667)
          ·
            refine ⟨39679122960508804501034501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26452748640339203000689667 39679122960508804501034501)
            ·
              refine ⟨7439835555095400843943969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39679122960508804501034501 7439835555095400843943969)
              ·
                refine ⟨5579876666321550632957977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7439835555095400843943969 5579876666321550632957977)
                ·
                  refine ⟨4184907499741162974718483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5579876666321550632957977 4184907499741162974718483)
                  ·
                    refine ⟨6277361249611744462077725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4184907499741162974718483 6277361249611744462077725)
                    ·
                      refine ⟨2354010468604404173279147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6277361249611744462077725 2354010468604404173279147)
                      ·
                        rfl

theorem cell23_4584419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_4584419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584419 prefixEnd_4584419 := by exact prefixLift 4584419
  have htrace : WordTrace (prefixWord ++ tailWord_4584419) baseStart_4584419 baseEnd_4584419 := by
    simpa [prefixWord, tailWord_4584419, baseEnd_4584419] using wordTrace_append hprefix tailTrace_4584419
  have hstable : (prefixWord ++ tailWord_4584419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584419).length < 2 ^ (prefixWord ++ tailWord_4584419).sum := by decide
  have hdescent : baseEnd_4584419 < baseStart_4584419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584445 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_4584445 : Nat := 118140960795 + 4584445 * 2 ^ 59
def prefixEnd_4584445 : Nat := 4983230072969 + 3 ^ 40 * 4584445 * 2
def baseEnd_4584445 : Nat := 2354023819101421071554027

theorem tailTrace_4584445 : CollatzResearch.WordTrace tailWord_4584445 prefixEnd_4584445 2354023819101421071554027 := by
  unfold tailWord_4584445
  simp only [CollatzResearch.WordTrace]
  refine ⟨167208445876346200716410789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111472297250897467144273859 167208445876346200716410789)
  ·
    refine ⟨31351583601814912634327023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167208445876346200716410789 31351583601814912634327023)
    ·
      refine ⟨47027375402722368951490535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31351583601814912634327023 47027375402722368951490535)
      ·
        refine ⟨70541063104083553427235803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47027375402722368951490535 70541063104083553427235803)
        ·
          refine ⟨105811594656125330140853705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70541063104083553427235803 105811594656125330140853705)
          ·
            refine ⟨79358695992093997605640279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105811594656125330140853705 79358695992093997605640279)
            ·
              refine ⟨119038043988140996408460419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79358695992093997605640279 119038043988140996408460419)
              ·
                refine ⟨178557065982211494612690629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119038043988140996408460419 178557065982211494612690629)
                ·
                  refine ⟨33479449871664655239879493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178557065982211494612690629 33479449871664655239879493)
                  ·
                    refine ⟨6277396850937122857477405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33479449871664655239879493 6277396850937122857477405)
                    ·
                      refine ⟨2354023819101421071554027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6277396850937122857477405 2354023819101421071554027)
                      ·
                        rfl

theorem cell23_4584445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_4584445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584445 prefixEnd_4584445 := by exact prefixLift 4584445
  have htrace : WordTrace (prefixWord ++ tailWord_4584445) baseStart_4584445 baseEnd_4584445 := by
    simpa [prefixWord, tailWord_4584445, baseEnd_4584445] using wordTrace_append hprefix tailTrace_4584445
  have hstable : (prefixWord ++ tailWord_4584445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584445).length < 2 ^ (prefixWord ++ tailWord_4584445).sum := by decide
  have hdescent : baseEnd_4584445 < baseStart_4584445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584455 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4584455 : Nat := 118140960795 + 4584455 * 2 ^ 59
def prefixEnd_4584455 : Nat := 4983230072969 + 3 ^ 40 * 4584455 * 2
def baseEnd_4584455 : Nat := 2354028953907966032428981

theorem tailTrace_4584455 : CollatzResearch.WordTrace tailWord_4584455 prefixEnd_4584455 2354028953907966032428981 := by
  unfold tailWord_4584455
  simp only [CollatzResearch.WordTrace]
  refine ⟨167208810606309972424274819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111472540404206648282849879 167208810606309972424274819)
  ·
    refine ⟨250813215909464958636412229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167208810606309972424274819 250813215909464958636412229)
    ·
      refine ⟨47027477983024679744327293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250813215909464958636412229 47027477983024679744327293)
      ·
        refine ⟨17635304243634254904122735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47027477983024679744327293 17635304243634254904122735)
        ·
          refine ⟨26452956365451382356184103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17635304243634254904122735 26452956365451382356184103)
          ·
            refine ⟨39679434548177073534276155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26452956365451382356184103 39679434548177073534276155)
            ·
              refine ⟨59519151822265610301414233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39679434548177073534276155 59519151822265610301414233)
              ·
                refine ⟨44639363866699207726060675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59519151822265610301414233 44639363866699207726060675)
                ·
                  refine ⟨66959045800048811589091013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44639363866699207726060675 66959045800048811589091013)
                  ·
                    refine ⟨12554821087509152172954565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66959045800048811589091013 12554821087509152172954565)
                    ·
                      refine ⟨2354028953907966032428981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12554821087509152172954565 2354028953907966032428981)
                      ·
                        rfl

theorem cell23_4584455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4584455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584455 prefixEnd_4584455 := by exact prefixLift 4584455
  have htrace : WordTrace (prefixWord ++ tailWord_4584455) baseStart_4584455 baseEnd_4584455 := by
    simpa [prefixWord, tailWord_4584455, baseEnd_4584455] using wordTrace_append hprefix tailTrace_4584455
  have hstable : (prefixWord ++ tailWord_4584455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584455).length < 2 ^ (prefixWord ++ tailWord_4584455).sum := by decide
  have hdescent : baseEnd_4584455 < baseStart_4584455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584476 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_4584476 : Nat := 118140960795 + 4584476 * 2 ^ 59
def prefixEnd_4584476 : Nat := 4983230072969 + 3 ^ 40 * 4584476 * 2
def baseEnd_4584476 : Nat := 2354039737001710450266385

theorem tailTrace_4584476 : CollatzResearch.WordTrace tailWord_4584476 prefixEnd_4584476 2354039737001710450266385 := by
  unfold tailWord_4584476
  simp only [CollatzResearch.WordTrace]
  refine ⟨83604788269616946505394641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111473051026155928673859521 83604788269616946505394641)
  ·
    refine ⟨62703591202212709879045981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83604788269616946505394641 62703591202212709879045981)
    ·
      refine ⟨23513846700829766204642243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62703591202212709879045981 23513846700829766204642243)
      ·
        refine ⟨35270770051244649306963365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23513846700829766204642243 35270770051244649306963365)
        ·
          refine ⟨6613269384608371745055631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35270770051244649306963365 6613269384608371745055631)
          ·
            refine ⟨9919904076912557617583447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613269384608371745055631 9919904076912557617583447)
            ·
              refine ⟨14879856115368836426375171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9919904076912557617583447 14879856115368836426375171)
              ·
                refine ⟨22319784173053254639562757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14879856115368836426375171 22319784173053254639562757)
                ·
                  refine ⟨4184959532447485244918017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22319784173053254639562757 4184959532447485244918017)
                  ·
                    refine ⟨3138719649335613933688513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4184959532447485244918017 3138719649335613933688513)
                    ·
                      refine ⟨2354039737001710450266385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138719649335613933688513 2354039737001710450266385)
                      ·
                        rfl

theorem cell23_4584476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_4584476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584476 prefixEnd_4584476 := by exact prefixLift 4584476
  have htrace : WordTrace (prefixWord ++ tailWord_4584476) baseStart_4584476 baseEnd_4584476 := by
    simpa [prefixWord, tailWord_4584476, baseEnd_4584476] using wordTrace_append hprefix tailTrace_4584476
  have hstable : (prefixWord ++ tailWord_4584476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584476).length < 2 ^ (prefixWord ++ tailWord_4584476).sum := by decide
  have hdescent : baseEnd_4584476 < baseStart_4584476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584482 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 7]
def baseStart_4584482 : Nat := 118140960795 + 4584482 * 2 ^ 59
def prefixEnd_4584482 : Nat := 4983230072969 + 3 ^ 40 * 4584482 * 2
def baseEnd_4584482 : Nat := 261560313098404158532373

theorem tailTrace_4584482 : CollatzResearch.WordTrace tailWord_4584482 prefixEnd_4584482 261560313098404158532373 := by
  unfold tailWord_4584482
  simp only [CollatzResearch.WordTrace]
  refine ⟨41802448844303039008876925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111473196918141437357005133 41802448844303039008876925)
  ·
    refine ⟨15675918316613639628328847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41802448844303039008876925 15675918316613639628328847)
    ·
      refine ⟨23513877474920459442493271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15675918316613639628328847 23513877474920459442493271)
      ·
        refine ⟨35270816212380689163739907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23513877474920459442493271 35270816212380689163739907)
        ·
          refine ⟨52906224318571033745609861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35270816212380689163739907 52906224318571033745609861)
          ·
            refine ⟨9919917059732068827301849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52906224318571033745609861 9919917059732068827301849)
            ·
              refine ⟨7439937794799051620476387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9919917059732068827301849 7439937794799051620476387)
              ·
                refine ⟨11159906692198577430714581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7439937794799051620476387 11159906692198577430714581)
                ·
                  refine ⟨261560313098404158532373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11159906692198577430714581 261560313098404158532373)
                  ·
                    rfl

theorem cell23_4584482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_4584482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584482 prefixEnd_4584482 := by exact prefixLift 4584482
  have htrace : WordTrace (prefixWord ++ tailWord_4584482) baseStart_4584482 baseEnd_4584482 := by
    simpa [prefixWord, tailWord_4584482, baseEnd_4584482] using wordTrace_append hprefix tailTrace_4584482
  have hstable : (prefixWord ++ tailWord_4584482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584482).length < 2 ^ (prefixWord ++ tailWord_4584482).sum := by decide
  have hdescent : baseEnd_4584482 < baseStart_4584482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584515 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 4]
def baseStart_4584515 : Nat := 118140960795 + 4584515 * 2 ^ 59
def prefixEnd_4584515 : Nat := 4983230072969 + 3 ^ 40 * 4584515 * 2
def baseEnd_4584515 : Nat := 2354059762747235797678705

theorem tailTrace_4584515 : CollatzResearch.WordTrace tailWord_4584515 prefixEnd_4584515 2354059762747235797678705 := by
  unfold tailWord_4584515
  simp only [CollatzResearch.WordTrace]
  refine ⟨167210998986092602671458999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111473999324061735114305999 167210998986092602671458999)
  ·
    refine ⟨250816498479138904007188499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167210998986092602671458999 250816498479138904007188499)
    ·
      refine ⟨376224747718708356010782749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250816498479138904007188499 376224747718708356010782749)
      ·
        refine ⟨141084280394515633504043531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376224747718708356010782749 141084280394515633504043531)
        ·
          refine ⟨211626420591773450256065297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141084280394515633504043531 211626420591773450256065297)
          ·
            refine ⟨158719815443830087692048973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211626420591773450256065297 158719815443830087692048973)
            ·
              refine ⟨59519930791436282884518365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158719815443830087692048973 59519930791436282884518365)
              ·
                refine ⟨22319974046788606081694387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59519930791436282884518365 22319974046788606081694387)
                ·
                  refine ⟨33479961070182909122541581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22319974046788606081694387 33479961070182909122541581)
                  ·
                    refine ⟨12554985401318590920953093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33479961070182909122541581 12554985401318590920953093)
                    ·
                      refine ⟨2354059762747235797678705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12554985401318590920953093 2354059762747235797678705)
                      ·
                        rfl

theorem cell23_4584515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_4584515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584515 prefixEnd_4584515 := by exact prefixLift 4584515
  have htrace : WordTrace (prefixWord ++ tailWord_4584515) baseStart_4584515 baseEnd_4584515 := by
    simpa [prefixWord, tailWord_4584515, baseEnd_4584515] using wordTrace_append hprefix tailTrace_4584515
  have hstable : (prefixWord ++ tailWord_4584515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584515).length < 2 ^ (prefixWord ++ tailWord_4584515).sum := by decide
  have hdescent : baseEnd_4584515 < baseStart_4584515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584532 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_4584532 : Nat := 118140960795 + 4584532 * 2 ^ 59
def prefixEnd_4584532 : Nat := 4983230072969 + 3 ^ 40 * 4584532 * 2
def baseEnd_4584532 : Nat := 2354068491918362231166127

theorem tailTrace_4584532 : CollatzResearch.WordTrace tailWord_4584532 prefixEnd_4584532 2354068491918362231166127 := by
  unfold tailWord_4584532
  simp only [CollatzResearch.WordTrace]
  refine ⟨83605809513515507287413925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111474412684687343049885233 83605809513515507287413925)
  ·
    refine ⟨15676089283784157616390111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83605809513515507287413925 15676089283784157616390111)
    ·
      refine ⟨23514133925676236424585167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15676089283784157616390111 23514133925676236424585167)
      ·
        refine ⟨35271200888514354636877751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23514133925676236424585167 35271200888514354636877751)
        ·
          refine ⟨52906801332771531955316627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35271200888514354636877751 52906801332771531955316627)
          ·
            refine ⟨79360201999157297932974941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52906801332771531955316627 79360201999157297932974941)
            ·
              refine ⟨29760075749683986724865603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79360201999157297932974941 29760075749683986724865603)
              ·
                refine ⟨44640113624525980087298405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29760075749683986724865603 44640113624525980087298405)
                ·
                  refine ⟨8370021304598621266368451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44640113624525980087298405 8370021304598621266368451)
                  ·
                    refine ⟨12555031956897931899552677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8370021304598621266368451 12555031956897931899552677)
                    ·
                      refine ⟨2354068491918362231166127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12555031956897931899552677 2354068491918362231166127)
                      ·
                        rfl

theorem cell23_4584532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_4584532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584532 prefixEnd_4584532 := by exact prefixLift 4584532
  have htrace : WordTrace (prefixWord ++ tailWord_4584532) baseStart_4584532 baseEnd_4584532 := by
    simpa [prefixWord, tailWord_4584532, baseEnd_4584532] using wordTrace_append hprefix tailTrace_4584532
  have hstable : (prefixWord ++ tailWord_4584532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584532).length < 2 ^ (prefixWord ++ tailWord_4584532).sum := by decide
  have hdescent : baseEnd_4584532 < baseStart_4584532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584545 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_4584545 : Nat := 118140960795 + 4584545 * 2 ^ 59
def prefixEnd_4584545 : Nat := 4983230072969 + 3 ^ 40 * 4584545 * 2
def baseEnd_4584545 : Nat := 2354075167166870680303567

theorem tailTrace_4584545 : CollatzResearch.WordTrace tailWord_4584545 prefixEnd_4584545 2354075167166870680303567 := by
  unfold tailWord_4584545
  simp only [CollatzResearch.WordTrace]
  refine ⟨167212093175983917795051089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111474728783989278530034059 167212093175983917795051089)
  ·
    refine ⟨125409069881987938346288317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167212093175983917795051089 125409069881987938346288317)
    ·
      refine ⟨47028401205745476879858119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125409069881987938346288317 47028401205745476879858119)
      ·
        refine ⟨70542601808618215319787179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47028401205745476879858119 70542601808618215319787179)
        ·
          refine ⟨105813902712927322979680769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70542601808618215319787179 105813902712927322979680769)
          ·
            refine ⟨79360427034695492234760577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105813902712927322979680769 79360427034695492234760577)
            ·
              refine ⟨59520320276021619176070433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79360427034695492234760577 59520320276021619176070433)
              ·
                refine ⟨44640240207016214382052825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59520320276021619176070433 44640240207016214382052825)
                ·
                  refine ⟨33480180155262160786539619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44640240207016214382052825 33480180155262160786539619)
                  ·
                    refine ⟨50220270232893241179809429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33480180155262160786539619 50220270232893241179809429)
                    ·
                      refine ⟨2354075167166870680303567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50220270232893241179809429 2354075167166870680303567)
                      ·
                        rfl

theorem cell23_4584545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_4584545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584545 prefixEnd_4584545 := by exact prefixLift 4584545
  have htrace : WordTrace (prefixWord ++ tailWord_4584545) baseStart_4584545 baseEnd_4584545 := by
    simpa [prefixWord, tailWord_4584545, baseEnd_4584545] using wordTrace_append hprefix tailTrace_4584545
  have hstable : (prefixWord ++ tailWord_4584545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584545).length < 2 ^ (prefixWord ++ tailWord_4584545).sum := by decide
  have hdescent : baseEnd_4584545 < baseStart_4584545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584609 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_4584609 : Nat := 118140960795 + 4584609 * 2 ^ 59
def prefixEnd_4584609 : Nat := 4983230072969 + 3 ^ 40 * 4584609 * 2
def baseEnd_4584609 : Nat := 2354108029928758429903273

theorem tailTrace_4584609 : CollatzResearch.WordTrace tailWord_4584609 prefixEnd_4584609 2354108029928758429903273 := by
  unfold tailWord_4584609
  simp only [CollatzResearch.WordTrace]
  refine ⟨167214427447752056725380881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111476284965168037816920587 167214427447752056725380881)
  ·
    refine ⟨125410820585814042544035661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167214427447752056725380881 125410820585814042544035661)
    ·
      refine ⟨47029057719680265954013373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125410820585814042544035661 47029057719680265954013373)
      ·
        refine ⟨17635896644880099732755015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47029057719680265954013373 17635896644880099732755015)
        ·
          refine ⟨26453844967320149599132523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17635896644880099732755015 26453844967320149599132523)
          ·
            refine ⟨39680767450980224398698785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26453844967320149599132523 39680767450980224398698785)
            ·
              refine ⟨29760575588235168299024089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39680767450980224398698785 29760575588235168299024089)
              ·
                refine ⟨22320431691176376224268067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29760575588235168299024089 22320431691176376224268067)
                ·
                  refine ⟨33480647536764564336402101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22320431691176376224268067 33480647536764564336402101)
                  ·
                    refine ⟨3138810706571677906537697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33480647536764564336402101 3138810706571677906537697)
                    ·
                      refine ⟨2354108029928758429903273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138810706571677906537697 2354108029928758429903273)
                      ·
                        rfl

theorem cell23_4584609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_4584609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584609 prefixEnd_4584609 := by exact prefixLift 4584609
  have htrace : WordTrace (prefixWord ++ tailWord_4584609) baseStart_4584609 baseEnd_4584609 := by
    simpa [prefixWord, tailWord_4584609, baseEnd_4584609] using wordTrace_append hprefix tailTrace_4584609
  have hstable : (prefixWord ++ tailWord_4584609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584609).length < 2 ^ (prefixWord ++ tailWord_4584609).sum := by decide
  have hdescent : baseEnd_4584609 < baseStart_4584609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584626 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_4584626 : Nat := 118140960795 + 4584626 * 2 ^ 59
def prefixEnd_4584626 : Nat := 4983230072969 + 3 ^ 40 * 4584626 * 2
def baseEnd_4584626 : Nat := 2354116759099884863390695

theorem tailTrace_4584626 : CollatzResearch.WordTrace tailWord_4584626 prefixEnd_4584626 2354116759099884863390695 := by
  unfold tailWord_4584626
  simp only [CollatzResearch.WordTrace]
  refine ⟨41803761872172617157187433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111476698325793645752499821 41803761872172617157187433)
  ·
    refine ⟨31352821404129462867890575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41803761872172617157187433 31352821404129462867890575)
    ·
      refine ⟨47029232106194194301835863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31352821404129462867890575 47029232106194194301835863)
      ·
        refine ⟨70543848159291291452753795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47029232106194194301835863 70543848159291291452753795)
        ·
          refine ⟨105815772238936937179130693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70543848159291291452753795 105815772238936937179130693)
          ·
            refine ⟨19840457294800675721087005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105815772238936937179130693 19840457294800675721087005)
            ·
              refine ⟨7440171485550253395407627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19840457294800675721087005 7440171485550253395407627)
              ·
                refine ⟨11160257228325380093111441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7440171485550253395407627 11160257228325380093111441)
                ·
                  refine ⟨8370192921244035069833581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11160257228325380093111441 8370192921244035069833581)
                  ·
                    refine ⟨3138822345466513151187593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8370192921244035069833581 3138822345466513151187593)
                    ·
                      refine ⟨2354116759099884863390695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138822345466513151187593 2354116759099884863390695)
                      ·
                        rfl

theorem cell23_4584626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_4584626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584626 prefixEnd_4584626 := by exact prefixLift 4584626
  have htrace : WordTrace (prefixWord ++ tailWord_4584626) baseStart_4584626 baseEnd_4584626 := by
    simpa [prefixWord, tailWord_4584626, baseEnd_4584626] using wordTrace_append hprefix tailTrace_4584626
  have hstable : (prefixWord ++ tailWord_4584626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584626).length < 2 ^ (prefixWord ++ tailWord_4584626).sum := by decide
  have hdescent : baseEnd_4584626 < baseStart_4584626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584633 : List Nat := [1, 2, 1, 4, 1, 4, 2, 3, 1, 1, 3]
def baseStart_4584633 : Nat := 118140960795 + 4584633 * 2 ^ 59
def prefixEnd_4584633 : Nat := 4983230072969 + 3 ^ 40 * 4584633 * 2
def baseEnd_4584633 : Nat := 2354120353464466336003163

theorem tailTrace_4584633 : CollatzResearch.WordTrace tailWord_4584633 prefixEnd_4584633 2354120353464466336003163 := by
  unfold tailWord_4584633
  simp only [CollatzResearch.WordTrace]
  refine ⟨167215302799665108824254553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111476868533110072549503035 167215302799665108824254553)
  ·
    refine ⟨125411477099748831618190915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167215302799665108824254553 125411477099748831618190915)
    ·
      refine ⟨188117215649623247427286373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125411477099748831618190915 188117215649623247427286373)
      ·
        refine ⟨35271977934304358892616195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188117215649623247427286373 35271977934304358892616195)
        ·
          refine ⟨52907966901456538338924293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35271977934304358892616195 52907966901456538338924293)
          ·
            refine ⟨9920243794023100938548305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52907966901456538338924293 9920243794023100938548305)
            ·
              refine ⟨7440182845517325703911229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9920243794023100938548305 7440182845517325703911229)
              ·
                refine ⟨2790068567068997138966711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7440182845517325703911229 2790068567068997138966711)
                ·
                  refine ⟨4185102850603495708450067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790068567068997138966711 4185102850603495708450067)
                  ·
                    refine ⟨6277654275905243562675101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4185102850603495708450067 6277654275905243562675101)
                    ·
                      refine ⟨2354120353464466336003163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6277654275905243562675101 2354120353464466336003163)
                      ·
                        rfl

theorem cell23_4584633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_4584633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584633 prefixEnd_4584633 := by exact prefixLift 4584633
  have htrace : WordTrace (prefixWord ++ tailWord_4584633) baseStart_4584633 baseEnd_4584633 := by
    simpa [prefixWord, tailWord_4584633, baseEnd_4584633] using wordTrace_append hprefix tailTrace_4584633
  have hstable : (prefixWord ++ tailWord_4584633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584633).length < 2 ^ (prefixWord ++ tailWord_4584633).sum := by decide
  have hdescent : baseEnd_4584633 < baseStart_4584633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584636 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_4584636 : Nat := 118140960795 + 4584636 * 2 ^ 59
def prefixEnd_4584636 : Nat := 4983230072969 + 3 ^ 40 * 4584636 * 2
def baseEnd_4584636 : Nat := 784707297968809941421883

theorem tailTrace_4584636 : CollatzResearch.WordTrace tailWord_4584636 prefixEnd_4584636 784707297968809941421883 := by
  unfold tailWord_4584636
  simp only [CollatzResearch.WordTrace]
  refine ⟨83607706109327120168306881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111476941479102826891075841 83607706109327120168306881)
  ·
    refine ⟨62705779581995340126230161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83607706109327120168306881 62705779581995340126230161)
    ·
      refine ⟨47029334686496505094672621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62705779581995340126230161 47029334686496505094672621)
      ·
        refine ⟨17636000507436189410502233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47029334686496505094672621 17636000507436189410502233)
        ·
          refine ⟨13227000380577142057876675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17636000507436189410502233 13227000380577142057876675)
          ·
            refine ⟨19840500570865713086815013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13227000380577142057876675 19840500570865713086815013)
            ·
              refine ⟨3720093857037321203777815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19840500570865713086815013 3720093857037321203777815)
              ·
                refine ⟨5580140785555981805666723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3720093857037321203777815 5580140785555981805666723)
                ·
                  refine ⟨8370211178333972708500085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5580140785555981805666723 8370211178333972708500085)
                  ·
                    refine ⟨784707297968809941421883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8370211178333972708500085 784707297968809941421883)
                    ·
                      rfl

theorem cell23_4584636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_4584636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584636 prefixEnd_4584636 := by exact prefixLift 4584636
  have htrace : WordTrace (prefixWord ++ tailWord_4584636) baseStart_4584636 baseEnd_4584636 := by
    simpa [prefixWord, tailWord_4584636, baseEnd_4584636] using wordTrace_append hprefix tailTrace_4584636
  have hstable : (prefixWord ++ tailWord_4584636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584636).length < 2 ^ (prefixWord ++ tailWord_4584636).sum := by decide
  have hdescent : baseEnd_4584636 < baseStart_4584636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584679 : List Nat := [1, 1, 5, 3, 2, 1, 1, 9]
def baseStart_4584679 : Nat := 118140960795 + 4584679 * 2 ^ 59
def prefixEnd_4584679 : Nat := 4983230072969 + 3 ^ 40 * 4584679 * 2
def baseEnd_4584679 : Nat := 87190517539799005778813

theorem tailTrace_4584679 : CollatzResearch.WordTrace tailWord_4584679 prefixEnd_4584679 87190517539799005778813 := by
  unfold tailWord_4584679
  simp only [CollatzResearch.WordTrace]
  refine ⟨167216980557498458680429091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111477987038332305786952727 167216980557498458680429091)
  ·
    refine ⟨250825470836247688020643637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167216980557498458680429091 250825470836247688020643637)
    ·
      refine ⟨23514887890898220751935341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250825470836247688020643637 23514887890898220751935341)
      ·
        refine ⟨8818082959086832781975753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23514887890898220751935341 8818082959086832781975753)
        ·
          refine ⟨6613562219315124586481815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8818082959086832781975753 6613562219315124586481815)
          ·
            refine ⟨9920343328972686879722723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613562219315124586481815 9920343328972686879722723)
            ·
              refine ⟨14880514993459030319584085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9920343328972686879722723 14880514993459030319584085)
              ·
                refine ⟨87190517539799005778813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14880514993459030319584085 87190517539799005778813)
                ·
                  rfl

theorem cell23_4584679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 9].length) (baseStart_4584679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584679 prefixEnd_4584679 := by exact prefixLift 4584679
  have htrace : WordTrace (prefixWord ++ tailWord_4584679) baseStart_4584679 baseEnd_4584679 := by
    simpa [prefixWord, tailWord_4584679, baseEnd_4584679] using wordTrace_append hprefix tailTrace_4584679
  have hstable : (prefixWord ++ tailWord_4584679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584679).length < 2 ^ (prefixWord ++ tailWord_4584679).sum := by decide
  have hdescent : baseEnd_4584679 < baseStart_4584679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584729 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 7, 4, 2]
def baseStart_4584729 : Nat := 118140960795 + 4584729 * 2 ^ 59
def prefixEnd_4584729 : Nat := 4983230072969 + 3 ^ 40 * 4584729 * 2
def baseEnd_4584729 : Nat := 2354169647607297960402721

theorem tailTrace_4584729 : CollatzResearch.WordTrace tailWord_4584729 prefixEnd_4584729 2354169647607297960402721 := by
  unfold tailWord_4584729
  simp only [CollatzResearch.WordTrace]
  refine ⟨167218804207317317219749241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111479202804878211479832827 167218804207317317219749241)
  ·
    refine ⟨125414103155487987914811931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167218804207317317219749241 125414103155487987914811931)
    ·
      refine ⟨188121154733231981872217897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125414103155487987914811931 188121154733231981872217897)
      ·
        refine ⟨141090866049923986404163423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188121154733231981872217897 141090866049923986404163423)
        ·
          refine ⟨211636299074885979606245135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141090866049923986404163423 211636299074885979606245135)
          ·
            refine ⟨317454448612328969409367703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211636299074885979606245135 317454448612328969409367703)
            ·
              refine ⟨476181672918493454114051555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317454448612328969409367703 476181672918493454114051555)
              ·
                refine ⟨714272509377740181171077333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476181672918493454114051555 714272509377740181171077333)
                ·
                  refine ⟨16740761938540785496197125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 714272509377740181171077333 16740761938540785496197125)
                  ·
                    refine ⟨3138892863476397280536961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16740761938540785496197125 3138892863476397280536961)
                    ·
                      refine ⟨2354169647607297960402721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138892863476397280536961 2354169647607297960402721)
                      ·
                        rfl

theorem cell23_4584729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_4584729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584729 prefixEnd_4584729 := by exact prefixLift 4584729
  have htrace : WordTrace (prefixWord ++ tailWord_4584729) baseStart_4584729 baseEnd_4584729 := by
    simpa [prefixWord, tailWord_4584729, baseEnd_4584729] using wordTrace_append hprefix tailTrace_4584729
  have hstable : (prefixWord ++ tailWord_4584729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584729).length < 2 ^ (prefixWord ++ tailWord_4584729).sum := by decide
  have hdescent : baseEnd_4584729 < baseStart_4584729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584733 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_4584733 : Nat := 118140960795 + 4584733 * 2 ^ 59
def prefixEnd_4584733 : Nat := 4983230072969 + 3 ^ 40 * 4584733 * 2
def baseEnd_4584733 : Nat := 2354171701529915944752703

theorem tailTrace_4584733 : CollatzResearch.WordTrace tailWord_4584733 prefixEnd_4584733 2354171701529915944752703 := by
  unfold tailWord_4584733
  simp only [CollatzResearch.WordTrace]
  refine ⟨167218950099302825902894853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111479300066201883935263235 167218950099302825902894853)
  ·
    refine ⟨31353553143619279856792785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167218950099302825902894853 31353553143619279856792785)
    ·
      refine ⟨23515164857714459892594589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31353553143619279856792785 23515164857714459892594589)
      ·
        refine ⟨8818186821642922459722971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23515164857714459892594589 8818186821642922459722971)
        ·
          refine ⟨13227280232464383689584457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8818186821642922459722971 13227280232464383689584457)
          ·
            refine ⟨9920460174348287767188343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13227280232464383689584457 9920460174348287767188343)
            ·
              refine ⟨14880690261522431650782515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9920460174348287767188343 14880690261522431650782515)
              ·
                refine ⟨22321035392283647476173773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14880690261522431650782515 22321035392283647476173773)
                ·
                  refine ⟨8370388272106367803565165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22321035392283647476173773 8370388272106367803565165)
                  ·
                    refine ⟨3138895602039887926336937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8370388272106367803565165 3138895602039887926336937)
                    ·
                      refine ⟨2354171701529915944752703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138895602039887926336937 2354171701529915944752703)
                      ·
                        rfl

theorem cell23_4584733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_4584733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584733 prefixEnd_4584733 := by exact prefixLift 4584733
  have htrace : WordTrace (prefixWord ++ tailWord_4584733) baseStart_4584733 baseEnd_4584733 := by
    simpa [prefixWord, tailWord_4584733, baseEnd_4584733] using wordTrace_append hprefix tailTrace_4584733
  have hstable : (prefixWord ++ tailWord_4584733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584733).length < 2 ^ (prefixWord ++ tailWord_4584733).sum := by decide
  have hdescent : baseEnd_4584733 < baseStart_4584733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584758 : List Nat := [5, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4584758 : Nat := 118140960795 + 4584758 * 2 ^ 59
def prefixEnd_4584758 : Nat := 4983230072969 + 3 ^ 40 * 4584758 * 2
def baseEnd_4584758 : Nat := 2354184538546278346940089

theorem tailTrace_4584758 : CollatzResearch.WordTrace tailWord_4584758 prefixEnd_4584758 2354184538546278346940089 := by
  unfold tailWord_4584758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10451241370263265948284683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111479907949474836781703285 10451241370263265948284683)
  ·
    refine ⟨15676862055394898922427025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10451241370263265948284683 15676862055394898922427025)
    ·
      refine ⟨11757646541546174191820269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15676862055394898922427025 11757646541546174191820269)
      ·
        refine ⟨4409117453079815321932601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11757646541546174191820269 4409117453079815321932601)
        ·
          refine ⟨3306838089809861491449451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4409117453079815321932601 3306838089809861491449451)
          ·
            refine ⟨4960257134714792237174177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306838089809861491449451 4960257134714792237174177)
            ·
              refine ⟨3720192851036094177880633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4960257134714792237174177 3720192851036094177880633)
              ·
                refine ⟨2790144638277070633410475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3720192851036094177880633 2790144638277070633410475)
                ·
                  refine ⟨4185216957415605950115713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790144638277070633410475 4185216957415605950115713)
                  ·
                    refine ⟨3138912718061704462586785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4185216957415605950115713 3138912718061704462586785)
                    ·
                      refine ⟨2354184538546278346940089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138912718061704462586785 2354184538546278346940089)
                      ·
                        rfl

theorem cell23_4584758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4584758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584758 prefixEnd_4584758 := by exact prefixLift 4584758
  have htrace : WordTrace (prefixWord ++ tailWord_4584758) baseStart_4584758 baseEnd_4584758 := by
    simpa [prefixWord, tailWord_4584758, baseEnd_4584758] using wordTrace_append hprefix tailTrace_4584758
  have hstable : (prefixWord ++ tailWord_4584758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584758).length < 2 ^ (prefixWord ++ tailWord_4584758).sum := by decide
  have hdescent : baseEnd_4584758 < baseStart_4584758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584814 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4584814 : Nat := 118140960795 + 4584814 * 2 ^ 59
def prefixEnd_4584814 : Nat := 4983230072969 + 3 ^ 40 * 4584814 * 2
def baseEnd_4584814 : Nat := 2354213293462930127839831

theorem tailTrace_4584814 : CollatzResearch.WordTrace tailWord_4584814 prefixEnd_4584814 2354213293462930127839831 := by
  unfold tailWord_4584814
  simp only [CollatzResearch.WordTrace]
  refine ⟨20902738051501172092074187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111481269608006251157728997 20902738051501172092074187)
  ·
    refine ⟨31354107077251758138111281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20902738051501172092074187 31354107077251758138111281)
    ·
      refine ⟨23515580307938818603583461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31354107077251758138111281 23515580307938818603583461)
      ·
        refine ⟨4409171307738528488171899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23515580307938818603583461 4409171307738528488171899)
        ·
          refine ⟨6613756961607792732257849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409171307738528488171899 6613756961607792732257849)
          ·
            refine ⟨4960317721205844549193387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6613756961607792732257849 4960317721205844549193387)
            ·
              refine ⟨7440476581808766823790081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960317721205844549193387 7440476581808766823790081)
              ·
                refine ⟨5580357436356575117842561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7440476581808766823790081 5580357436356575117842561)
                ·
                  refine ⟨4185268077267431338381921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5580357436356575117842561 4185268077267431338381921)
                  ·
                    refine ⟨3138951057950573503786441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4185268077267431338381921 3138951057950573503786441)
                    ·
                      refine ⟨2354213293462930127839831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3138951057950573503786441 2354213293462930127839831)
                      ·
                        rfl

theorem cell23_4584814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4584814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584814 prefixEnd_4584814 := by exact prefixLift 4584814
  have htrace : WordTrace (prefixWord ++ tailWord_4584814) baseStart_4584814 baseEnd_4584814 := by
    simpa [prefixWord, tailWord_4584814, baseEnd_4584814] using wordTrace_append hprefix tailTrace_4584814
  have hstable : (prefixWord ++ tailWord_4584814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584814).length < 2 ^ (prefixWord ++ tailWord_4584814).sum := by decide
  have hdescent : baseEnd_4584814 < baseStart_4584814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584896 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 3, 5, 2]
def baseStart_4584896 : Nat := 118140960795 + 4584896 * 2 ^ 59
def prefixEnd_4584896 : Nat := 4983230072969 + 3 ^ 40 * 4584896 * 2
def baseEnd_4584896 : Nat := 2354255398876598807014453

theorem tailTrace_4584896 : CollatzResearch.WordTrace tailWord_4584896 prefixEnd_4584896 2354255398876598807014453 := by
  unfold tailWord_4584896
  simp only [CollatzResearch.WordTrace]
  refine ⟨83612447598856152370539271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111483263465141536494052361 83612447598856152370539271)
  ·
    refine ⟨125418671398284228555808907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83612447598856152370539271 125418671398284228555808907)
    ·
      refine ⟨188128007097426342833713361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125418671398284228555808907 188128007097426342833713361)
      ·
        refine ⟨141096005323069757125285021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188128007097426342833713361 141096005323069757125285021)
        ·
          refine ⟨52911001996151158921981883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141096005323069757125285021 52911001996151158921981883)
          ·
            refine ⟨79366502994226738382972825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52911001996151158921981883 79366502994226738382972825)
            ·
              refine ⟨59524877245670053787229619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79366502994226738382972825 59524877245670053787229619)
              ·
                refine ⟨89287315868505080680844429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59524877245670053787229619 89287315868505080680844429)
                ·
                  refine ⟨33482743450689405255316661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89287315868505080680844429 33482743450689405255316661)
                  ·
                    refine ⟨3139007198502131742685937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33482743450689405255316661 3139007198502131742685937)
                    ·
                      refine ⟨2354255398876598807014453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139007198502131742685937 2354255398876598807014453)
                      ·
                        rfl

theorem cell23_4584896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_4584896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584896 prefixEnd_4584896 := by exact prefixLift 4584896
  have htrace : WordTrace (prefixWord ++ tailWord_4584896) baseStart_4584896 baseEnd_4584896 := by
    simpa [prefixWord, tailWord_4584896, baseEnd_4584896] using wordTrace_append hprefix tailTrace_4584896
  have hstable : (prefixWord ++ tailWord_4584896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584896).length < 2 ^ (prefixWord ++ tailWord_4584896).sum := by decide
  have hdescent : baseEnd_4584896 < baseStart_4584896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584906 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_4584906 : Nat := 118140960795 + 4584906 * 2 ^ 59
def prefixEnd_4584906 : Nat := 4983230072969 + 3 ^ 40 * 4584906 * 2
def baseEnd_4584906 : Nat := 784753511227714589296469

theorem tailTrace_4584906 : CollatzResearch.WordTrace tailWord_4584906 prefixEnd_4584906 784753511227714589296469 := by
  unfold tailWord_4584906
  simp only [CollatzResearch.WordTrace]
  refine ⟨41806314981919019112235643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111483506618450717632628381 41806314981919019112235643)
  ·
    refine ⟨62709472472878528668353465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41806314981919019112235643 62709472472878528668353465)
    ·
      refine ⟨47032104354658896501265099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62709472472878528668353465 47032104354658896501265099)
      ·
        refine ⟨70548156531988344751897649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47032104354658896501265099 70548156531988344751897649)
        ·
          refine ⟨52911117398991258563923237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70548156531988344751897649 52911117398991258563923237)
          ·
            refine ⟨9920834512310860980735607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52911117398991258563923237 9920834512310860980735607)
            ·
              refine ⟨14881251768466291471103411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9920834512310860980735607 14881251768466291471103411)
              ·
                refine ⟨22321877652699437206655117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14881251768466291471103411 22321877652699437206655117)
                ·
                  refine ⟨8370704119762288952495669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22321877652699437206655117 8370704119762288952495669)
                  ·
                    refine ⟨784753511227714589296469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8370704119762288952495669 784753511227714589296469)
                    ·
                      rfl

theorem cell23_4584906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_4584906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584906 prefixEnd_4584906 := by exact prefixLift 4584906
  have htrace : WordTrace (prefixWord ++ tailWord_4584906) baseStart_4584906 baseEnd_4584906 := by
    simpa [prefixWord, tailWord_4584906, baseEnd_4584906] using wordTrace_append hprefix tailTrace_4584906
  have hstable : (prefixWord ++ tailWord_4584906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584906).length < 2 ^ (prefixWord ++ tailWord_4584906).sum := by decide
  have hdescent : baseEnd_4584906 < baseStart_4584906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584939 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 6]
def baseStart_4584939 : Nat := 118140960795 + 4584939 * 2 ^ 59
def prefixEnd_4584939 : Nat := 4983230072969 + 3 ^ 40 * 4584939 * 2
def baseEnd_4584939 : Nat := 2354277478544742138776755

theorem tailTrace_4584939 : CollatzResearch.WordTrace tailWord_4584939 prefixEnd_4584939 2354277478544742138776755 := by
  unfold tailWord_4584939
  simp only [CollatzResearch.WordTrace]
  refine ⟨167226463536556523084893871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111484309024371015389929247 167226463536556523084893871)
  ·
    refine ⟨250839695304834784627340807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167226463536556523084893871 250839695304834784627340807)
    ·
      refine ⟨376259542957252176941011211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250839695304834784627340807 376259542957252176941011211)
      ·
        refine ⟨564389314435878265411516817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376259542957252176941011211 564389314435878265411516817)
        ·
          refine ⟨423291985826908699058637613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564389314435878265411516817 423291985826908699058637613)
          ·
            refine ⟨158734494685090762146989105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423291985826908699058637613 158734494685090762146989105)
            ·
              refine ⟨119050871013818071610241829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158734494685090762146989105 119050871013818071610241829)
              ·
                refine ⟨22322038315090888426920343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119050871013818071610241829 22322038315090888426920343)
                ·
                  refine ⟨33483057472636332640380515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22322038315090888426920343 33483057472636332640380515)
                  ·
                    refine ⟨50224586208954498960570773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33483057472636332640380515 50224586208954498960570773)
                    ·
                      refine ⟨2354277478544742138776755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50224586208954498960570773 2354277478544742138776755)
                      ·
                        rfl

theorem cell23_4584939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_4584939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584939 prefixEnd_4584939 := by exact prefixLift 4584939
  have htrace : WordTrace (prefixWord ++ tailWord_4584939) baseStart_4584939 baseEnd_4584939 := by
    simpa [prefixWord, tailWord_4584939, baseEnd_4584939] using wordTrace_append hprefix tailTrace_4584939
  have hstable : (prefixWord ++ tailWord_4584939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584939).length < 2 ^ (prefixWord ++ tailWord_4584939).sum := by decide
  have hdescent : baseEnd_4584939 < baseStart_4584939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584956 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_4584956 : Nat := 118140960795 + 4584956 * 2 ^ 59
def prefixEnd_4584956 : Nat := 4983230072969 + 3 ^ 40 * 4584956 * 2
def baseEnd_4584956 : Nat := 2354286207715868572264177

theorem tailTrace_4584956 : CollatzResearch.WordTrace tailWord_4584956 prefixEnd_4584956 2354286207715868572264177 := by
  unfold tailWord_4584956
  simp only [CollatzResearch.WordTrace]
  refine ⟨83613541788747467494131361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111484722384996623325508481 83613541788747467494131361)
  ·
    refine ⟨62710156341560600620598521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83613541788747467494131361 62710156341560600620598521)
    ·
      refine ⟨47032617256170450465448891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62710156341560600620598521 47032617256170450465448891)
      ·
        refine ⟨70548925884255675698173337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47032617256170450465448891 70548925884255675698173337)
        ·
          refine ⟨52911694413191756773630003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70548925884255675698173337 52911694413191756773630003)
          ·
            refine ⟨79367541619787635160445005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52911694413191756773630003 79367541619787635160445005)
            ·
              refine ⟨29762828107420363185166877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79367541619787635160445005 29762828107420363185166877)
              ·
                refine ⟨11161060540282636194437579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29762828107420363185166877 11161060540282636194437579)
                ·
                  refine ⟨16741590810423954291656369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11161060540282636194437579 16741590810423954291656369)
                  ·
                    refine ⟨12556193107817965718742277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16741590810423954291656369 12556193107817965718742277)
                    ·
                      refine ⟨2354286207715868572264177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12556193107817965718742277 2354286207715868572264177)
                      ·
                        rfl

theorem cell23_4584956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_4584956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584956 prefixEnd_4584956 := by exact prefixLift 4584956
  have htrace : WordTrace (prefixWord ++ tailWord_4584956) baseStart_4584956 baseEnd_4584956 := by
    simpa [prefixWord, tailWord_4584956, baseEnd_4584956] using wordTrace_append hprefix tailTrace_4584956
  have hstable : (prefixWord ++ tailWord_4584956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584956).length < 2 ^ (prefixWord ++ tailWord_4584956).sum := by decide
  have hdescent : baseEnd_4584956 < baseStart_4584956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584964 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4584964 : Nat := 118140960795 + 4584964 * 2 ^ 59
def prefixEnd_4584964 : Nat := 4983230072969 + 3 ^ 40 * 4584964 * 2
def baseEnd_4584964 : Nat := 2354290315561104540964141

theorem tailTrace_4584964 : CollatzResearch.WordTrace tailWord_4584964 prefixEnd_4584964 2354290315561104540964141 := by
  unfold tailWord_4584964
  simp only [CollatzResearch.WordTrace]
  refine ⟨83613687680732976177276973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111484916907643968236369297 83613687680732976177276973)
  ·
    refine ⟨31355132880274866066478865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83613687680732976177276973 31355132880274866066478865)
    ·
      refine ⟨23516349660206149549859149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31355132880274866066478865 23516349660206149549859149)
      ·
        refine ⟨8818631122577306081197181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23516349660206149549859149 8818631122577306081197181)
        ·
          refine ⟨3306986670966489780448943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8818631122577306081197181 3306986670966489780448943)
          ·
            refine ⟨4960480006449734670673415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306986670966489780448943 4960480006449734670673415)
            ·
              refine ⟨7440720009674602006010123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960480006449734670673415 7440720009674602006010123)
              ·
                refine ⟨11161080014511903009015185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7440720009674602006010123 11161080014511903009015185)
                ·
                  refine ⟨8370810010883927256761389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11161080014511903009015185 8370810010883927256761389)
                  ·
                    refine ⟨3139053754081472721285521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8370810010883927256761389 3139053754081472721285521)
                    ·
                      refine ⟨2354290315561104540964141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139053754081472721285521 2354290315561104540964141)
                      ·
                        rfl

theorem cell23_4584964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4584964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584964 prefixEnd_4584964 := by exact prefixLift 4584964
  have htrace : WordTrace (prefixWord ++ tailWord_4584964) baseStart_4584964 baseEnd_4584964 := by
    simpa [prefixWord, tailWord_4584964, baseEnd_4584964] using wordTrace_append hprefix tailTrace_4584964
  have hstable : (prefixWord ++ tailWord_4584964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584964).length < 2 ^ (prefixWord ++ tailWord_4584964).sum := by decide
  have hdescent : baseEnd_4584964 < baseStart_4584964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4584977 : List Nat := [1, 2, 2, 1, 1, 2, 6, 3, 1, 2, 2]
def baseStart_4584977 : Nat := 118140960795 + 4584977 * 2 ^ 59
def prefixEnd_4584977 : Nat := 4983230072969 + 3 ^ 40 * 4584977 * 2
def baseEnd_4584977 : Nat := 2354296990809612990101581

theorem tailTrace_4584977 : CollatzResearch.WordTrace tailWord_4584977 prefixEnd_4584977 2354296990809612990101581 := by
  unfold tailWord_4584977
  simp only [CollatzResearch.WordTrace]
  refine ⟨167227849510418855574777185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111485233006945903716518123 167227849510418855574777185)
  ·
    refine ⟨125420887132814141681082889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167227849510418855574777185 125420887132814141681082889)
    ·
      refine ⟨94065665349610606260812167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125420887132814141681082889 94065665349610606260812167)
      ·
        refine ⟨141098498024415909391218251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94065665349610606260812167 141098498024415909391218251)
        ·
          refine ⟨211647747036623864086827377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141098498024415909391218251 211647747036623864086827377)
          ·
            refine ⟨158735810277467898065120533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211647747036623864086827377 158735810277467898065120533)
            ·
              refine ⟨7440741106756307721802525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158735810277467898065120533 7440741106756307721802525)
              ·
                refine ⟨2790277915033615395675947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7440741106756307721802525 2790277915033615395675947)
                ·
                  refine ⟨4185416872550423093513921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790277915033615395675947 4185416872550423093513921)
                  ·
                    refine ⟨3139062654412817320135441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4185416872550423093513921 3139062654412817320135441)
                    ·
                      refine ⟨2354296990809612990101581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139062654412817320135441 2354296990809612990101581)
                      ·
                        rfl

theorem cell23_4584977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_4584977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4584977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4584977 prefixEnd_4584977 := by exact prefixLift 4584977
  have htrace : WordTrace (prefixWord ++ tailWord_4584977) baseStart_4584977 baseEnd_4584977 := by
    simpa [prefixWord, tailWord_4584977, baseEnd_4584977] using wordTrace_append hprefix tailTrace_4584977
  have hstable : (prefixWord ++ tailWord_4584977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4584977).length < 2 ^ (prefixWord ++ tailWord_4584977).sum := by decide
  have hdescent : baseEnd_4584977 < baseStart_4584977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4584977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585033 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 1, 4, 2]
def baseStart_4585033 : Nat := 118140960795 + 4585033 * 2 ^ 59
def prefixEnd_4585033 : Nat := 4983230072969 + 3 ^ 40 * 4585033 * 2
def baseEnd_4585033 : Nat := 2354325745726264771001323

theorem tailTrace_4585033 : CollatzResearch.WordTrace tailWord_4585033 prefixEnd_4585033 2354325745726264771001323 := by
  unfold tailWord_4585033
  simp only [CollatzResearch.WordTrace]
  refine ⟨167229891998215977138815753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111486594665477318092543835 167229891998215977138815753)
  ·
    refine ⟨125422418998661982854111815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167229891998215977138815753 125422418998661982854111815)
    ·
      refine ⟨188133628497992974281167723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125422418998661982854111815 188133628497992974281167723)
      ·
        refine ⟨282200442746989461421751585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188133628497992974281167723 282200442746989461421751585)
        ·
          refine ⟨211650332060242096066313689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282200442746989461421751585 211650332060242096066313689)
          ·
            refine ⟨158737749045181572049735267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211650332060242096066313689 158737749045181572049735267)
            ·
              refine ⟨238106623567772358074602901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158737749045181572049735267 238106623567772358074602901)
              ·
                refine ⟨11161247979739329284747011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 238106623567772358074602901 11161247979739329284747011)
                ·
                  refine ⟨16741871969608993927120517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11161247979739329284747011 16741871969608993927120517)
                  ·
                    refine ⟨3139100994301686361335097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16741871969608993927120517 3139100994301686361335097)
                    ·
                      refine ⟨2354325745726264771001323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139100994301686361335097 2354325745726264771001323)
                      ·
                        rfl

theorem cell23_4585033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 4, 2].length) (baseStart_4585033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585033 prefixEnd_4585033 := by exact prefixLift 4585033
  have htrace : WordTrace (prefixWord ++ tailWord_4585033) baseStart_4585033 baseEnd_4585033 := by
    simpa [prefixWord, tailWord_4585033, baseEnd_4585033] using wordTrace_append hprefix tailTrace_4585033
  have hstable : (prefixWord ++ tailWord_4585033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585033).length < 2 ^ (prefixWord ++ tailWord_4585033).sum := by decide
  have hdescent : baseEnd_4585033 < baseStart_4585033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585036 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_4585036 : Nat := 118140960795 + 4585036 * 2 ^ 59
def prefixEnd_4585036 : Nat := 4983230072969 + 3 ^ 40 * 4585036 * 2
def baseEnd_4585036 : Nat := 2354327286168228259263809

theorem tailTrace_4585036 : CollatzResearch.WordTrace tailWord_4585036 prefixEnd_4585036 2354327286168228259263809 := by
  unfold tailWord_4585036
  simp only [CollatzResearch.WordTrace]
  refine ⟨83615000708602554325587481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111486667611470072434116641 83615000708602554325587481)
  ·
    refine ⟨62711250531451915744190611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83615000708602554325587481 62711250531451915744190611)
    ·
      refine ⟨94066875797177873616285917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62711250531451915744190611 94066875797177873616285917)
      ·
        refine ⟨35275078423941702606107219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94066875797177873616285917 35275078423941702606107219)
        ·
          refine ⟨52912617635912553909160829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35275078423941702606107219 52912617635912553909160829)
          ·
            refine ⟨19842231613467207715935311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52912617635912553909160829 19842231613467207715935311)
            ·
              refine ⟨29763347420200811573902967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19842231613467207715935311 29763347420200811573902967)
              ·
                refine ⟨44645021130301217360854451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29763347420200811573902967 44645021130301217360854451)
                ·
                  refine ⟨66967531695451826041281677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44645021130301217360854451 66967531695451826041281677)
                  ·
                    refine ⟨25112824385794434765480629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66967531695451826041281677 25112824385794434765480629)
                    ·
                      refine ⟨2354327286168228259263809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25112824385794434765480629 2354327286168228259263809)
                      ·
                        rfl

theorem cell23_4585036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_4585036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585036 prefixEnd_4585036 := by exact prefixLift 4585036
  have htrace : WordTrace (prefixWord ++ tailWord_4585036) baseStart_4585036 baseEnd_4585036 := by
    simpa [prefixWord, tailWord_4585036, baseEnd_4585036] using wordTrace_append hprefix tailTrace_4585036
  have hstable : (prefixWord ++ tailWord_4585036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585036).length < 2 ^ (prefixWord ++ tailWord_4585036).sum := by decide
  have hdescent : baseEnd_4585036 < baseStart_4585036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585233 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_4585233 : Nat := 118140960795 + 4585233 * 2 ^ 59
def prefixEnd_4585233 : Nat := 4983230072969 + 3 ^ 40 * 4585233 * 2
def baseEnd_4585233 : Nat := 2354428441857163988500403

theorem tailTrace_4585233 : CollatzResearch.WordTrace tailWord_4585233 prefixEnd_4585233 2354428441857163988500403 := by
  unfold tailWord_4585233
  simp only [CollatzResearch.WordTrace]
  refine ⟨167237186597491411296096353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111491457731660940864064235 167237186597491411296096353)
  ·
    refine ⟨125427889948118558472072265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167237186597491411296096353 125427889948118558472072265)
    ·
      refine ⟨94070917461088918854054199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125427889948118558472072265 94070917461088918854054199)
      ·
        refine ⟨141106376191633378281081299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94070917461088918854054199 141106376191633378281081299)
        ·
          refine ⟨211659564287450067421621949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141106376191633378281081299 211659564287450067421621949)
          ·
            refine ⟨79372336607793775283108231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211659564287450067421621949 79372336607793775283108231)
            ·
              refine ⟨119058504911690662924662347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79372336607793775283108231 119058504911690662924662347)
              ·
                refine ⟨178587757367535994386993521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119058504911690662924662347 178587757367535994386993521)
                ·
                  refine ⟨133940818025651995790245141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178587757367535994386993521 133940818025651995790245141)
                  ·
                    refine ⟨6278475844952437302667741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 133940818025651995790245141 6278475844952437302667741)
                    ·
                      refine ⟨2354428441857163988500403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6278475844952437302667741 2354428441857163988500403)
                      ·
                        rfl

theorem cell23_4585233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_4585233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585233 prefixEnd_4585233 := by exact prefixLift 4585233
  have htrace : WordTrace (prefixWord ++ tailWord_4585233) baseStart_4585233 baseEnd_4585233 := by
    simpa [prefixWord, tailWord_4585233, baseEnd_4585233] using wordTrace_append hprefix tailTrace_4585233
  have hstable : (prefixWord ++ tailWord_4585233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585233).length < 2 ^ (prefixWord ++ tailWord_4585233).sum := by decide
  have hdescent : baseEnd_4585233 < baseStart_4585233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585247 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 5, 2, 2]
def baseStart_4585247 : Nat := 118140960795 + 4585247 * 2 ^ 59
def prefixEnd_4585247 : Nat := 4983230072969 + 3 ^ 40 * 4585247 * 2
def baseEnd_4585247 : Nat := 2354435630586326933725339

theorem tailTrace_4585247 : CollatzResearch.WordTrace tailWord_4585247 prefixEnd_4585247 2354435630586326933725339 := by
  unfold tailWord_4585247
  simp only [CollatzResearch.WordTrace]
  refine ⟨167237697219440691687105995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111491798146293794458070663 167237697219440691687105995)
  ·
    refine ⟨250856545829161037530658993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167237697219440691687105995 250856545829161037530658993)
    ·
      refine ⟨188142409371870778147994245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250856545829161037530658993 188142409371870778147994245)
      ·
        refine ⟨35276701757225770902748921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188142409371870778147994245 35276701757225770902748921)
        ·
          refine ⟨26457526317919328177061691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35276701757225770902748921 26457526317919328177061691)
          ·
            refine ⟨39686289476878992265592537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26457526317919328177061691 39686289476878992265592537)
            ·
              refine ⟨29764717107659244199194403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39686289476878992265592537 29764717107659244199194403)
              ·
                refine ⟨44647075661488866298791605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29764717107659244199194403 44647075661488866298791605)
                ·
                  refine ⟨4185663343264581215511713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44647075661488866298791605 4185663343264581215511713)
                  ·
                    refine ⟨3139247507448435911633785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4185663343264581215511713 3139247507448435911633785)
                    ·
                      refine ⟨2354435630586326933725339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139247507448435911633785 2354435630586326933725339)
                      ·
                        rfl

theorem cell23_4585247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_4585247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585247 prefixEnd_4585247 := by exact prefixLift 4585247
  have htrace : WordTrace (prefixWord ++ tailWord_4585247) baseStart_4585247 baseEnd_4585247 := by
    simpa [prefixWord, tailWord_4585247, baseEnd_4585247] using wordTrace_append hprefix tailTrace_4585247
  have hstable : (prefixWord ++ tailWord_4585247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585247).length < 2 ^ (prefixWord ++ tailWord_4585247).sum := by decide
  have hdescent : baseEnd_4585247 < baseStart_4585247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585253 : List Nat := [1, 3, 1, 2, 3, 2, 2, 9]
def baseStart_4585253 : Nat := 118140960795 + 4585253 * 2 ^ 59
def prefixEnd_4585253 : Nat := 4983230072969 + 3 ^ 40 * 4585253 * 2
def baseEnd_4585253 : Nat := 87201433758157552231493

theorem tailTrace_4585253 : CollatzResearch.WordTrace tailWord_4585253 prefixEnd_4585253 87201433758157552231493 := by
  unfold tailWord_4585253
  simp only [CollatzResearch.WordTrace]
  refine ⟨167237916057418954711824413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111491944038279303141216275 167237916057418954711824413)
  ·
    refine ⟨62714218521532108016934155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167237916057418954711824413 62714218521532108016934155)
    ·
      refine ⟨94071327782298162025401233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62714218521532108016934155 94071327782298162025401233)
      ·
        refine ⟨70553495836723621519050925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94071327782298162025401233 70553495836723621519050925)
        ·
          refine ⟨26457560938771358069644097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70553495836723621519050925 26457560938771358069644097)
          ·
            refine ⟨19843170704078518552233073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26457560938771358069644097 19843170704078518552233073)
            ·
              refine ⟨14882378028058888914174805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19843170704078518552233073 14882378028058888914174805)
              ·
                refine ⟨87201433758157552231493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14882378028058888914174805 87201433758157552231493)
                ·
                  rfl

theorem cell23_4585253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 9].length) (baseStart_4585253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585253 prefixEnd_4585253 := by exact prefixLift 4585253
  have htrace : WordTrace (prefixWord ++ tailWord_4585253) baseStart_4585253 baseEnd_4585253 := by
    simpa [prefixWord, tailWord_4585253, baseEnd_4585253] using wordTrace_append hprefix tailTrace_4585253
  have hstable : (prefixWord ++ tailWord_4585253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585253).length < 2 ^ (prefixWord ++ tailWord_4585253).sum := by decide
  have hdescent : baseEnd_4585253 < baseStart_4585253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585260 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_4585260 : Nat := 118140960795 + 4585260 * 2 ^ 59
def prefixEnd_4585260 : Nat := 4983230072969 + 3 ^ 40 * 4585260 * 2
def baseEnd_4585260 : Nat := 2354442305834835382862779

theorem tailTrace_4585260 : CollatzResearch.WordTrace tailWord_4585260 prefixEnd_4585260 2354442305834835382862779 := by
  unfold tailWord_4585260
  simp only [CollatzResearch.WordTrace]
  refine ⟨83619085684196797453664617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111492114245595729938219489 83619085684196797453664617)
  ·
    refine ⟨62714314263147598090248463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83619085684196797453664617 62714314263147598090248463)
    ·
      refine ⟨94071471394721397135372695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62714314263147598090248463 94071471394721397135372695)
      ·
        refine ⟨141107207092082095703059043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94071471394721397135372695 141107207092082095703059043)
        ·
          refine ⟨211660810638123143554588565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141107207092082095703059043 211660810638123143554588565)
          ·
            refine ⟨9921600498662022354121339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211660810638123143554588565 9921600498662022354121339)
            ·
              refine ⟨14882400747993033531182009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9921600498662022354121339 14882400747993033531182009)
              ·
                refine ⟨11161800560994775148386507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14882400747993033531182009 11161800560994775148386507)
                ·
                  refine ⟨16742700841492162722579761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11161800560994775148386507 16742700841492162722579761)
                  ·
                    refine ⟨12557025631119122041934821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16742700841492162722579761 12557025631119122041934821)
                    ·
                      refine ⟨2354442305834835382862779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12557025631119122041934821 2354442305834835382862779)
                      ·
                        rfl

theorem cell23_4585260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_4585260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585260 prefixEnd_4585260 := by exact prefixLift 4585260
  have htrace : WordTrace (prefixWord ++ tailWord_4585260) baseStart_4585260 baseEnd_4585260 := by
    simpa [prefixWord, tailWord_4585260, baseEnd_4585260] using wordTrace_append hprefix tailTrace_4585260
  have hstable : (prefixWord ++ tailWord_4585260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585260).length < 2 ^ (prefixWord ++ tailWord_4585260).sum := by decide
  have hdescent : baseEnd_4585260 < baseStart_4585260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585267 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 5]
def baseStart_4585267 : Nat := 118140960795 + 4585267 * 2 ^ 59
def prefixEnd_4585267 : Nat := 4983230072969 + 3 ^ 40 * 4585267 * 2
def baseEnd_4585267 : Nat := 2354445900199416855475247

theorem tailTrace_4585267 : CollatzResearch.WordTrace tailWord_4585267 prefixEnd_4585267 2354445900199416855475247 := by
  unfold tailWord_4585267
  simp only [CollatzResearch.WordTrace]
  refine ⟨167238426679368235102834055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111492284452912156735222703 167238426679368235102834055)
  ·
    refine ⟨250857640019052352654251083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167238426679368235102834055 250857640019052352654251083)
    ·
      refine ⟨376286460028578528981376625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250857640019052352654251083 376286460028578528981376625)
      ·
        refine ⟨282214845021433896736032469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376286460028578528981376625 282214845021433896736032469)
        ·
          refine ⟨6614410430189856954750761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 282214845021433896736032469 6614410430189856954750761)
          ·
            refine ⟨4960807822642392716063071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6614410430189856954750761 4960807822642392716063071)
            ·
              refine ⟨7441211733963589074094607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960807822642392716063071 7441211733963589074094607)
              ·
                refine ⟨11161817600945383611141911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441211733963589074094607 11161817600945383611141911)
                ·
                  refine ⟨16742726401418075416712867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11161817600945383611141911 16742726401418075416712867)
                  ·
                    refine ⟨25114089602127113125069301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16742726401418075416712867 25114089602127113125069301)
                    ·
                      refine ⟨2354445900199416855475247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25114089602127113125069301 2354445900199416855475247)
                      ·
                        rfl

theorem cell23_4585267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 5].length) (baseStart_4585267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585267 prefixEnd_4585267 := by exact prefixLift 4585267
  have htrace : WordTrace (prefixWord ++ tailWord_4585267) baseStart_4585267 baseEnd_4585267 := by
    simpa [prefixWord, tailWord_4585267, baseEnd_4585267] using wordTrace_append hprefix tailTrace_4585267
  have hstable : (prefixWord ++ tailWord_4585267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585267).length < 2 ^ (prefixWord ++ tailWord_4585267).sum := by decide
  have hdescent : baseEnd_4585267 < baseStart_4585267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585270 : List Nat := [5, 1, 2, 2, 1, 12]
def baseStart_4585270 : Nat := 118140960795 + 4585270 * 2 ^ 59
def prefixEnd_4585270 : Nat := 4983230072969 + 3 ^ 40 * 4585270 * 2
def baseEnd_4585270 : Nat := 9689084117865762731431

theorem tailTrace_4585270 : CollatzResearch.WordTrace tailWord_4585270 prefixEnd_4585270 9689084117865762731431 := by
  unfold tailWord_4585270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10452408506147335413449579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111492357398904911076795509 10452408506147335413449579)
  ·
    refine ⟨15678612759221003120174369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10452408506147335413449579 15678612759221003120174369)
    ·
      refine ⟨11758959569415752340130777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15678612759221003120174369 11758959569415752340130777)
      ·
        refine ⟨8819219677061814255098083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11758959569415752340130777 8819219677061814255098083)
        ·
          refine ⟨13228829515592721382647125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8819219677061814255098083 13228829515592721382647125)
          ·
            refine ⟨9689084117865762731431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13228829515592721382647125 9689084117865762731431)
            ·
              rfl

theorem cell23_4585270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 12].length) (baseStart_4585270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585270 prefixEnd_4585270 := by exact prefixLift 4585270
  have htrace : WordTrace (prefixWord ++ tailWord_4585270) baseStart_4585270 baseEnd_4585270 := by
    simpa [prefixWord, tailWord_4585270, baseEnd_4585270] using wordTrace_append hprefix tailTrace_4585270
  have hstable : (prefixWord ++ tailWord_4585270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585270).length < 2 ^ (prefixWord ++ tailWord_4585270).sum := by decide
  have hdescent : baseEnd_4585270 < baseStart_4585270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585283 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 2, 7]
def baseStart_4585283 : Nat := 118140960795 + 4585283 * 2 ^ 59
def prefixEnd_4585283 : Nat := 4983230072969 + 3 ^ 40 * 4585283 * 2
def baseEnd_4585283 : Nat := 784818038629962930958391

theorem tailTrace_4585283 : CollatzResearch.WordTrace tailWord_4585283 prefixEnd_4585283 784818038629962930958391 := by
  unfold tailWord_4585283
  simp only [CollatzResearch.WordTrace]
  refine ⟨167239010247310269835416503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111492673498206846556944335 167239010247310269835416503)
  ·
    refine ⟨250858515370965404753124755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167239010247310269835416503 250858515370965404753124755)
    ·
      refine ⟨376287773056448107129687133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250858515370965404753124755 376287773056448107129687133)
      ·
        refine ⟨141107914896168040173632675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376287773056448107129687133 141107914896168040173632675)
        ·
          refine ⟨211661872344252060260449013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141107914896168040173632675 211661872344252060260449013)
          ·
            refine ⟨19843300532273630649417095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211661872344252060260449013 19843300532273630649417095)
            ·
              refine ⟨29764950798410445974125643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19843300532273630649417095 29764950798410445974125643)
              ·
                refine ⟨44647426197615668961188465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29764950798410445974125643 44647426197615668961188465)
                ·
                  refine ⟨33485569648211751720891349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44647426197615668961188465 33485569648211751720891349)
                  ·
                    refine ⟨784818038629962930958391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33485569648211751720891349 784818038629962930958391)
                    ·
                      rfl

theorem cell23_4585283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 7].length) (baseStart_4585283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585283 prefixEnd_4585283 := by exact prefixLift 4585283
  have htrace : WordTrace (prefixWord ++ tailWord_4585283) baseStart_4585283 baseEnd_4585283 := by
    simpa [prefixWord, tailWord_4585283, baseEnd_4585283] using wordTrace_append hprefix tailTrace_4585283
  have hstable : (prefixWord ++ tailWord_4585283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585283).length < 2 ^ (prefixWord ++ tailWord_4585283).sum := by decide
  have hdescent : baseEnd_4585283 < baseStart_4585283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585297 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_4585297 : Nat := 118140960795 + 4585297 * 2 ^ 59
def prefixEnd_4585297 : Nat := 4983230072969 + 3 ^ 40 * 4585297 * 2
def baseEnd_4585297 : Nat := 2354461304619051738100109

theorem tailTrace_4585297 : CollatzResearch.WordTrace tailWord_4585297 prefixEnd_4585297 2354461304619051738100109 := by
  unfold tailWord_4585297
  simp only [CollatzResearch.WordTrace]
  refine ⟨167239520869259550226426145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111493013912839700150950763 167239520869259550226426145)
  ·
    refine ⟨125429640651944662669819609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167239520869259550226426145 125429640651944662669819609)
    ·
      refine ⟨94072230488958497002364707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125429640651944662669819609 94072230488958497002364707)
      ·
        refine ⟨141108345733437745503547061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94072230488958497002364707 141108345733437745503547061)
        ·
          refine ⟨13228907412509788640957537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141108345733437745503547061 13228907412509788640957537)
          ·
            refine ⟨9921680559382341480718153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13228907412509788640957537 9921680559382341480718153)
            ·
              refine ⟨7441260419536756110538615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9921680559382341480718153 7441260419536756110538615)
              ·
                refine ⟨11161890629305134165807923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441260419536756110538615 11161890629305134165807923)
                ·
                  refine ⟨16742835943957701248711885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11161890629305134165807923 16742835943957701248711885)
                  ·
                    refine ⟨6278563478984137968266957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16742835943957701248711885 6278563478984137968266957)
                    ·
                      refine ⟨2354461304619051738100109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6278563478984137968266957 2354461304619051738100109)
                      ·
                        rfl

theorem cell23_4585297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_4585297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585297 prefixEnd_4585297 := by exact prefixLift 4585297
  have htrace : WordTrace (prefixWord ++ tailWord_4585297) baseStart_4585297 baseEnd_4585297 := by
    simpa [prefixWord, tailWord_4585297, baseEnd_4585297] using wordTrace_append hprefix tailTrace_4585297
  have hstable : (prefixWord ++ tailWord_4585297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585297).length < 2 ^ (prefixWord ++ tailWord_4585297).sum := by decide
  have hdescent : baseEnd_4585297 < baseStart_4585297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585313 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 1, 8]
def baseStart_4585313 : Nat := 118140960795 + 4585313 * 2 ^ 59
def prefixEnd_4585313 : Nat := 4983230072969 + 3 ^ 40 * 4585313 * 2
def baseEnd_4585313 : Nat := 784823173436507891833345

theorem tailTrace_4585313 : CollatzResearch.WordTrace tailWord_4585313 prefixEnd_4585313 784823173436507891833345 := by
  unfold tailWord_4585313
  simp only [CollatzResearch.WordTrace]
  refine ⟨167240104437201584959008593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111493402958134389972672395 167240104437201584959008593)
  ·
    refine ⟨125430078327901188719256445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167240104437201584959008593 125430078327901188719256445)
    ·
      refine ⟨47036279372962945769721167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125430078327901188719256445 47036279372962945769721167)
      ·
        refine ⟨70554419059444418654581751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47036279372962945769721167 70554419059444418654581751)
        ·
          refine ⟨105831628589166627981872627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70554419059444418654581751 105831628589166627981872627)
          ·
            refine ⟨158747442883749941972808941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105831628589166627981872627 158747442883749941972808941)
            ·
              refine ⟨59530291081406228239803353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158747442883749941972808941 59530291081406228239803353)
              ·
                refine ⟨44647718311054671179852515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59530291081406228239803353 44647718311054671179852515)
                ·
                  refine ⟨66971577466582006769778773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44647718311054671179852515 66971577466582006769778773)
                  ·
                    refine ⟨784823173436507891833345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66971577466582006769778773 784823173436507891833345)
                    ·
                      rfl

theorem cell23_4585313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_4585313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585313 prefixEnd_4585313 := by exact prefixLift 4585313
  have htrace : WordTrace (prefixWord ++ tailWord_4585313) baseStart_4585313 baseEnd_4585313 := by
    simpa [prefixWord, tailWord_4585313, baseEnd_4585313] using wordTrace_append hprefix tailTrace_4585313
  have hstable : (prefixWord ++ tailWord_4585313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585313).length < 2 ^ (prefixWord ++ tailWord_4585313).sum := by decide
  have hdescent : baseEnd_4585313 < baseStart_4585313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585323 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 5]
def baseStart_4585323 : Nat := 118140960795 + 4585323 * 2 ^ 59
def prefixEnd_4585323 : Nat := 4983230072969 + 3 ^ 40 * 4585323 * 2
def baseEnd_4585323 : Nat := 2354474655116068636374989

theorem tailTrace_4585323 : CollatzResearch.WordTrace tailWord_4585323 prefixEnd_4585323 2354474655116068636374989 := by
  unfold tailWord_4585323
  simp only [CollatzResearch.WordTrace]
  refine ⟨167240469167165356666872623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111493646111443571111248415 167240469167165356666872623)
  ·
    refine ⟨250860703750748035000308935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167240469167165356666872623 250860703750748035000308935)
    ·
      refine ⟨376291055626122052500463403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250860703750748035000308935 376291055626122052500463403)
      ·
        refine ⟨564436583439183078750695105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376291055626122052500463403 564436583439183078750695105)
        ·
          refine ⟨423327437579387309063021329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564436583439183078750695105 423327437579387309063021329)
          ·
            refine ⟨317495578184540481797265997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423327437579387309063021329 317495578184540481797265997)
            ·
              refine ⟨119060841819202680673974749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317495578184540481797265997 119060841819202680673974749)
              ·
                refine ⟨44647815682201005252740531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119060841819202680673974749 44647815682201005252740531)
                ·
                  refine ⟨66971723523301507879110797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44647815682201005252740531 66971723523301507879110797)
                  ·
                    refine ⟨25114396321238065454666549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66971723523301507879110797 25114396321238065454666549)
                    ·
                      refine ⟨2354474655116068636374989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25114396321238065454666549 2354474655116068636374989)
                      ·
                        rfl

theorem cell23_4585323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_4585323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585323 prefixEnd_4585323 := by exact prefixLift 4585323
  have htrace : WordTrace (prefixWord ++ tailWord_4585323) baseStart_4585323 baseEnd_4585323 := by
    simpa [prefixWord, tailWord_4585323, baseEnd_4585323] using wordTrace_append hprefix tailTrace_4585323
  have hstable : (prefixWord ++ tailWord_4585323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585323).length < 2 ^ (prefixWord ++ tailWord_4585323).sum := by decide
  have hdescent : baseEnd_4585323 < baseStart_4585323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585324 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 1, 3, 2]
def baseStart_4585324 : Nat := 118140960795 + 4585324 * 2 ^ 59
def prefixEnd_4585324 : Nat := 4983230072969 + 3 ^ 40 * 4585324 * 2
def baseEnd_4585324 : Nat := 2354475168596723132462485

theorem tailTrace_4585324 : CollatzResearch.WordTrace tailWord_4585324 prefixEnd_4585324 2354475168596723132462485 := by
  unfold tailWord_4585324
  simp only [CollatzResearch.WordTrace]
  refine ⟨83620252820080866918829513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111493670426774489225106017 83620252820080866918829513)
  ·
    refine ⟨62715189615060650189122135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83620252820080866918829513 62715189615060650189122135)
    ·
      refine ⟨94072784422590975283683203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62715189615060650189122135 94072784422590975283683203)
      ·
        refine ⟨141109176633886462925524805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94072784422590975283683203 141109176633886462925524805)
        ·
          refine ⟨26457970618853711798535901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141109176633886462925524805 26457970618853711798535901)
          ·
            refine ⟨9921738982070141924450963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26457970618853711798535901 9921738982070141924450963)
            ·
              refine ⟨14882608473105212886676445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9921738982070141924450963 14882608473105212886676445)
              ·
                refine ⟨5580978177414454832503667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14882608473105212886676445 5580978177414454832503667)
                ·
                  refine ⟨8371467266121682248755501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5580978177414454832503667 8371467266121682248755501)
                  ·
                    refine ⟨3139300224795630843283313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8371467266121682248755501 3139300224795630843283313)
                    ·
                      refine ⟨2354475168596723132462485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139300224795630843283313 2354475168596723132462485)
                      ·
                        rfl

theorem cell23_4585324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_4585324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585324 prefixEnd_4585324 := by exact prefixLift 4585324
  have htrace : WordTrace (prefixWord ++ tailWord_4585324) baseStart_4585324 baseEnd_4585324 := by
    simpa [prefixWord, tailWord_4585324, baseEnd_4585324] using wordTrace_append hprefix tailTrace_4585324
  have hstable : (prefixWord ++ tailWord_4585324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585324).length < 2 ^ (prefixWord ++ tailWord_4585324).sum := by decide
  have hdescent : baseEnd_4585324 < baseStart_4585324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585358 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4585358 : Nat := 118140960795 + 4585358 * 2 ^ 59
def prefixEnd_4585358 : Nat := 4983230072969 + 3 ^ 40 * 4585358 * 2
def baseEnd_4585358 : Nat := 2354492626938975999437329

theorem tailTrace_4585358 : CollatzResearch.WordTrace tailWord_4585358 prefixEnd_4585358 2354492626938975999437329 := by
  unfold tailWord_4585358
  simp only [CollatzResearch.WordTrace]
  refine ⟨20905218215254819705549591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111494497148025705096264485 20905218215254819705549591)
  ·
    refine ⟨31357827322882229558324387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20905218215254819705549591 31357827322882229558324387)
    ·
      refine ⟨47036740984323344337486581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31357827322882229558324387 47036740984323344337486581)
      ·
        refine ⟨4409694467280313531639367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47036740984323344337486581 4409694467280313531639367)
        ·
          refine ⟨6614541700920470297459051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409694467280313531639367 6614541700920470297459051)
          ·
            refine ⟨9921812551380705446188577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614541700920470297459051 9921812551380705446188577)
            ·
              refine ⟨7441359413535529084641433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9921812551380705446188577 7441359413535529084641433)
              ·
                refine ⟨5581019560151646813481075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7441359413535529084641433 5581019560151646813481075)
                ·
                  refine ⟨8371529340227470220221613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5581019560151646813481075 8371529340227470220221613)
                  ·
                    refine ⟨3139323502585301332583105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8371529340227470220221613 3139323502585301332583105)
                    ·
                      refine ⟨2354492626938975999437329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139323502585301332583105 2354492626938975999437329)
                      ·
                        rfl

theorem cell23_4585358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4585358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585358 prefixEnd_4585358 := by exact prefixLift 4585358
  have htrace : WordTrace (prefixWord ++ tailWord_4585358) baseStart_4585358 baseEnd_4585358 := by
    simpa [prefixWord, tailWord_4585358, baseEnd_4585358] using wordTrace_append hprefix tailTrace_4585358
  have hstable : (prefixWord ++ tailWord_4585358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585358).length < 2 ^ (prefixWord ++ tailWord_4585358).sum := by decide
  have hdescent : baseEnd_4585358 < baseStart_4585358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585363 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 6]
def baseStart_4585363 : Nat := 118140960795 + 4585363 * 2 ^ 59
def prefixEnd_4585363 : Nat := 4983230072969 + 3 ^ 40 * 4585363 * 2
def baseEnd_4585363 : Nat := 2354495194342248479874805

theorem tailTrace_4585363 : CollatzResearch.WordTrace tailWord_4585363 prefixEnd_4585363 2354495194342248479874805 := by
  unfold tailWord_4585363
  simp only [CollatzResearch.WordTrace]
  refine ⟨167241928087020443498328743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111494618724680295665552495 167241928087020443498328743)
  ·
    refine ⟨250862892130530665247493115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167241928087020443498328743 250862892130530665247493115)
    ·
      refine ⟨376294338195795997871239673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250862892130530665247493115 376294338195795997871239673)
      ·
        refine ⟨282220753646846998403429755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376294338195795997871239673 282220753646846998403429755)
        ·
          refine ⟨423331130470270497605144633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282220753646846998403429755 423331130470270497605144633)
          ·
            refine ⟨317498347852702873203858475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423331130470270497605144633 317498347852702873203858475)
            ·
              refine ⟨476247521779054309805787713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317498347852702873203858475 476247521779054309805787713)
              ·
                refine ⟨357185641334290732354340785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476247521779054309805787713 357185641334290732354340785)
                ·
                  refine ⟨267889231000718049265755589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357185641334290732354340785 267889231000718049265755589)
                  ·
                    refine ⟨50229230812634634237329173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267889231000718049265755589 50229230812634634237329173)
                    ·
                      refine ⟨2354495194342248479874805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50229230812634634237329173 2354495194342248479874805)
                      ·
                        rfl

theorem cell23_4585363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_4585363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585363 prefixEnd_4585363 := by exact prefixLift 4585363
  have htrace : WordTrace (prefixWord ++ tailWord_4585363) baseStart_4585363 baseEnd_4585363 := by
    simpa [prefixWord, tailWord_4585363, baseEnd_4585363] using wordTrace_append hprefix tailTrace_4585363
  have hstable : (prefixWord ++ tailWord_4585363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585363).length < 2 ^ (prefixWord ++ tailWord_4585363).sum := by decide
  have hdescent : baseEnd_4585363 < baseStart_4585363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585400 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_4585400 : Nat := 118140960795 + 4585400 * 2 ^ 59
def prefixEnd_4585400 : Nat := 4983230072969 + 3 ^ 40 * 4585400 * 2
def baseEnd_4585400 : Nat := 2354514193126464835112135

theorem tailTrace_4585400 : CollatzResearch.WordTrace tailWord_4585400 prefixEnd_4585400 2354514193126464835112135 := by
  unfold tailWord_4585400
  simp only [CollatzResearch.WordTrace]
  refine ⟨83621638793943199408712827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111495518391924265878283769 83621638793943199408712827)
  ·
    refine ⟨125432458190914799113069241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83621638793943199408712827 125432458190914799113069241)
    ·
      refine ⟨94074343643186099334801931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125432458190914799113069241 94074343643186099334801931)
      ·
        refine ⟨141111515464779149002202897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94074343643186099334801931 141111515464779149002202897)
        ·
          refine ⟨105833636598584361751652173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141111515464779149002202897 105833636598584361751652173)
          ·
            refine ⟨39687613724469135656869565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105833636598584361751652173 39687613724469135656869565)
            ·
              refine ⟨14882855146675925871326087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39687613724469135656869565 14882855146675925871326087)
              ·
                refine ⟨22324282720013888806989131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14882855146675925871326087 22324282720013888806989131)
                ·
                  refine ⟨33486424080020833210483697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22324282720013888806989131 33486424080020833210483697)
                  ·
                    refine ⟨25114818060015624907862773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33486424080020833210483697 25114818060015624907862773)
                    ·
                      refine ⟨2354514193126464835112135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25114818060015624907862773 2354514193126464835112135)
                      ·
                        rfl

theorem cell23_4585400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_4585400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585400 prefixEnd_4585400 := by exact prefixLift 4585400
  have htrace : WordTrace (prefixWord ++ tailWord_4585400) baseStart_4585400 baseEnd_4585400 := by
    simpa [prefixWord, tailWord_4585400, baseEnd_4585400] using wordTrace_append hprefix tailTrace_4585400
  have hstable : (prefixWord ++ tailWord_4585400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585400).length < 2 ^ (prefixWord ++ tailWord_4585400).sum := by decide
  have hdescent : baseEnd_4585400 < baseStart_4585400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585527 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 1, 6]
def baseStart_4585527 : Nat := 118140960795 + 4585527 * 2 ^ 59
def prefixEnd_4585527 : Nat := 4983230072969 + 3 ^ 40 * 4585527 * 2
def baseEnd_4585527 : Nat := 784859801723195279408017

theorem tailTrace_4585527 : CollatzResearch.WordTrace tailWord_4585527 prefixEnd_4585527 784859801723195279408017 := by
  unfold tailWord_4585527
  simp only [CollatzResearch.WordTrace]
  refine ⟨167247909658426299507298835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111498606438950866338199223 167247909658426299507298835)
  ·
    refine ⟨250871864487639449260948253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167247909658426299507298835 250871864487639449260948253)
    ·
      refine ⟨94076949182864793472855595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250871864487639449260948253 94076949182864793472855595)
      ·
        refine ⟨141115423774297190209283393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94076949182864793472855595 141115423774297190209283393)
        ·
          refine ⟨105836567830722892656962545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141115423774297190209283393 105836567830722892656962545)
          ·
            refine ⟨79377425873042169492721909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105836567830722892656962545 79377425873042169492721909)
            ·
              refine ⟨7441633675597703389942679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79377425873042169492721909 7441633675597703389942679)
              ·
                refine ⟨11162450513396555084914019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441633675597703389942679 11162450513396555084914019)
                ·
                  refine ⟨16743675770094832627371029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11162450513396555084914019 16743675770094832627371029)
                  ·
                    refine ⟨784859801723195279408017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16743675770094832627371029 784859801723195279408017)
                    ·
                      rfl

theorem cell23_4585527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_4585527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585527 prefixEnd_4585527 := by exact prefixLift 4585527
  have htrace : WordTrace (prefixWord ++ tailWord_4585527) baseStart_4585527 baseEnd_4585527 := by
    simpa [prefixWord, tailWord_4585527, baseEnd_4585527] using wordTrace_append hprefix tailTrace_4585527
  have hstable : (prefixWord ++ tailWord_4585527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585527).length < 2 ^ (prefixWord ++ tailWord_4585527).sum := by decide
  have hdescent : baseEnd_4585527 < baseStart_4585527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585557 : List Nat := [1, 3, 2, 2, 1, 5, 9]
def baseStart_4585557 : Nat := 118140960795 + 4585557 * 2 ^ 59
def prefixEnd_4585557 : Nat := 4983230072969 + 3 ^ 40 * 4585557 * 2
def baseEnd_4585557 : Nat := 29069071723323712603073

theorem tailTrace_4585557 : CollatzResearch.WordTrace tailWord_4585557 prefixEnd_4585557 29069071723323712603073 := by
  unfold tailWord_4585557
  simp only [CollatzResearch.WordTrace]
  refine ⟨167249003848317614630890925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111499335898878409753927283 167249003848317614630890925)
  ·
    refine ⟨62718376443119105486584097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167249003848317614630890925 62718376443119105486584097)
    ·
      refine ⟨47038782332339329114938073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62718376443119105486584097 47038782332339329114938073)
      ·
        refine ⟨35279086749254496836203555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47038782332339329114938073 35279086749254496836203555)
        ·
          refine ⟨52918630123881745254305333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35279086749254496836203555 52918630123881745254305333)
          ·
            refine ⟨4961121574113913617591125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52918630123881745254305333 4961121574113913617591125)
            ·
              refine ⟨29069071723323712603073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4961121574113913617591125 29069071723323712603073)
              ·
                rfl

theorem cell23_4585557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 9].length) (baseStart_4585557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585557 prefixEnd_4585557 := by exact prefixLift 4585557
  have htrace : WordTrace (prefixWord ++ tailWord_4585557) baseStart_4585557 baseEnd_4585557 := by
    simpa [prefixWord, tailWord_4585557, baseEnd_4585557] using wordTrace_append hprefix tailTrace_4585557
  have hstable : (prefixWord ++ tailWord_4585557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585557).length < 2 ^ (prefixWord ++ tailWord_4585557).sum := by decide
  have hdescent : baseEnd_4585557 < baseStart_4585557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585567 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 3]
def baseStart_4585567 : Nat := 118140960795 + 4585567 * 2 ^ 59
def prefixEnd_4585567 : Nat := 4983230072969 + 3 ^ 40 * 4585567 * 2
def baseEnd_4585567 : Nat := 2354599944395765681723867

theorem tailTrace_4585567 : CollatzResearch.WordTrace tailWord_4585567 prefixEnd_4585567 2354599944395765681723867 := by
  unfold tailWord_4585567
  simp only [CollatzResearch.WordTrace]
  refine ⟨167249368578281386338754955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111499579052187590892503303 167249368578281386338754955)
  ·
    refine ⟨250874052867422079508132433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167249368578281386338754955 250874052867422079508132433)
    ·
      refine ⟨188155539650566559631099325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250874052867422079508132433 188155539650566559631099325)
      ·
        refine ⟨70558327368962459861662247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188155539650566559631099325 70558327368962459861662247)
        ·
          refine ⟨105837491053443689792493371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70558327368962459861662247 105837491053443689792493371)
          ·
            refine ⟨158756236580165534688740057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105837491053443689792493371 158756236580165534688740057)
            ·
              refine ⟨119067177435124151016555043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158756236580165534688740057 119067177435124151016555043)
              ·
                refine ⟨178600766152686226524832565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119067177435124151016555043 178600766152686226524832565)
                ·
                  refine ⟨16743821826814333736703053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178600766152686226524832565 16743821826814333736703053)
                  ·
                    refine ⟨6278933185055375151263645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16743821826814333736703053 6278933185055375151263645)
                    ·
                      refine ⟨2354599944395765681723867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6278933185055375151263645 2354599944395765681723867)
                      ·
                        rfl

theorem cell23_4585567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_4585567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585567 prefixEnd_4585567 := by exact prefixLift 4585567
  have htrace : WordTrace (prefixWord ++ tailWord_4585567) baseStart_4585567 baseEnd_4585567 := by
    simpa [prefixWord, tailWord_4585567, baseEnd_4585567] using wordTrace_append hprefix tailTrace_4585567
  have hstable : (prefixWord ++ tailWord_4585567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585567).length < 2 ^ (prefixWord ++ tailWord_4585567).sum := by decide
  have hdescent : baseEnd_4585567 < baseStart_4585567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585568 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 3, 2, 2]
def baseStart_4585568 : Nat := 118140960795 + 4585568 * 2 ^ 59
def prefixEnd_4585568 : Nat := 4983230072969 + 3 ^ 40 * 4585568 * 2
def baseEnd_4585568 : Nat := 2354600457876420177811363

theorem tailTrace_4585568 : CollatzResearch.WordTrace tailWord_4585568 prefixEnd_4585568 2354600457876420177811363 := by
  unfold tailWord_4585568
  simp only [CollatzResearch.WordTrace]
  refine ⟨83624702525638881754770679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111499603367518509006360905 83624702525638881754770679)
  ·
    refine ⟨125437053788458322632156019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83624702525638881754770679 125437053788458322632156019)
    ·
      refine ⟨188155580682687483948234029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125437053788458322632156019 188155580682687483948234029)
      ·
        refine ⟨70558342756007806480587761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188155580682687483948234029 70558342756007806480587761)
        ·
          refine ⟨52918757067005854860440821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70558342756007806480587761 52918757067005854860440821)
          ·
            refine ⟨4961133475031798893166327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52918757067005854860440821 4961133475031798893166327)
            ·
              refine ⟨7441700212547698339749491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4961133475031798893166327 7441700212547698339749491)
              ·
                refine ⟨11162550318821547509624237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441700212547698339749491 11162550318821547509624237)
                ·
                  refine ⟨4185956369558080316109089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11162550318821547509624237 4185956369558080316109089)
                  ·
                    refine ⟨3139467277168560237081817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4185956369558080316109089 3139467277168560237081817)
                    ·
                      refine ⟨2354600457876420177811363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139467277168560237081817 2354600457876420177811363)
                      ·
                        rfl

theorem cell23_4585568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_4585568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585568 prefixEnd_4585568 := by exact prefixLift 4585568
  have htrace : WordTrace (prefixWord ++ tailWord_4585568) baseStart_4585568 baseEnd_4585568 := by
    simpa [prefixWord, tailWord_4585568, baseEnd_4585568] using wordTrace_append hprefix tailTrace_4585568
  have hstable : (prefixWord ++ tailWord_4585568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585568).length < 2 ^ (prefixWord ++ tailWord_4585568).sum := by decide
  have hdescent : baseEnd_4585568 < baseStart_4585568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585601 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_4585601 : Nat := 118140960795 + 4585601 * 2 ^ 59
def prefixEnd_4585601 : Nat := 4983230072969 + 3 ^ 40 * 4585601 * 2
def baseEnd_4585601 : Nat := 2354617402738018548698711

theorem tailTrace_4585601 : CollatzResearch.WordTrace tailWord_4585601 prefixEnd_4585601 2354617402738018548698711 := by
  unfold tailWord_4585601
  simp only [CollatzResearch.WordTrace]
  refine ⟨167250608660158210145492657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111500405773438806763661771 167250608660158210145492657)
  ·
    refine ⟨125437956495118657609119493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167250608660158210145492657 125437956495118657609119493)
    ·
      refine ⟨23519616842834748301709905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125437956495118657609119493 23519616842834748301709905)
      ·
        refine ⟨17639712632126061226282429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23519616842834748301709905 17639712632126061226282429)
        ·
          refine ⟨6614892237047272959855911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17639712632126061226282429 6614892237047272959855911)
          ·
            refine ⟨9922338355570909439783867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614892237047272959855911 9922338355570909439783867)
            ·
              refine ⟨14883507533356364159675801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9922338355570909439783867 14883507533356364159675801)
              ·
                refine ⟨11162630650017273119756851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14883507533356364159675801 11162630650017273119756851)
                ·
                  refine ⟨16743945975025909679635277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11162630650017273119756851 16743945975025909679635277)
                  ·
                    refine ⟨6278979740634716129863229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16743945975025909679635277 6278979740634716129863229)
                    ·
                      refine ⟨2354617402738018548698711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6278979740634716129863229 2354617402738018548698711)
                      ·
                        rfl

theorem cell23_4585601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_4585601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585601 prefixEnd_4585601 := by exact prefixLift 4585601
  have htrace : WordTrace (prefixWord ++ tailWord_4585601) baseStart_4585601 baseEnd_4585601 := by
    simpa [prefixWord, tailWord_4585601, baseEnd_4585601] using wordTrace_append hprefix tailTrace_4585601
  have hstable : (prefixWord ++ tailWord_4585601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585601).length < 2 ^ (prefixWord ++ tailWord_4585601).sum := by decide
  have hdescent : baseEnd_4585601 < baseStart_4585601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585618 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_4585618 : Nat := 118140960795 + 4585618 * 2 ^ 59
def prefixEnd_4585618 : Nat := 4983230072969 + 3 ^ 40 * 4585618 * 2
def baseEnd_4585618 : Nat := 2354626131909144982186133

theorem tailTrace_4585618 : CollatzResearch.WordTrace tailWord_4585618 prefixEnd_4585618 2354626131909144982186133 := by
  unfold tailWord_4585618
  simp only [CollatzResearch.WordTrace]
  refine ⟨41812807175274155512215377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111500819134064414699241005 41812807175274155512215377)
  ·
    refine ⟨31359605381455616634161533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41812807175274155512215377 31359605381455616634161533)
    ·
      refine ⟨11759852018045856237810575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31359605381455616634161533 11759852018045856237810575)
      ·
        refine ⟨17639778027068784356715863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11759852018045856237810575 17639778027068784356715863)
        ·
          refine ⟨26459667040603176535073795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17639778027068784356715863 26459667040603176535073795)
          ·
            refine ⟨39689500560904764802610693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26459667040603176535073795 39689500560904764802610693)
            ·
              refine ⟨7441781355169643400489505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39689500560904764802610693 7441781355169643400489505)
              ·
                refine ⟨5581336016377232550367129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7441781355169643400489505 5581336016377232550367129)
                ·
                  refine ⟨4186002012282924412775347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5581336016377232550367129 4186002012282924412775347)
                  ·
                    refine ⟨6279003018424386619163021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4186002012282924412775347 6279003018424386619163021)
                    ·
                      refine ⟨2354626131909144982186133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6279003018424386619163021 2354626131909144982186133)
                      ·
                        rfl

theorem cell23_4585618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_4585618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585618 prefixEnd_4585618 := by exact prefixLift 4585618
  have htrace : WordTrace (prefixWord ++ tailWord_4585618) baseStart_4585618 baseEnd_4585618 := by
    simpa [prefixWord, tailWord_4585618, baseEnd_4585618] using wordTrace_append hprefix tailTrace_4585618
  have hstable : (prefixWord ++ tailWord_4585618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585618).length < 2 ^ (prefixWord ++ tailWord_4585618).sum := by decide
  have hdescent : baseEnd_4585618 < baseStart_4585618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585627 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 3]
def baseStart_4585627 : Nat := 118140960795 + 4585627 * 2 ^ 59
def prefixEnd_4585627 : Nat := 4983230072969 + 3 ^ 40 * 4585627 * 2
def baseEnd_4585627 : Nat := 2354630753235035446973591

theorem tailTrace_4585627 : CollatzResearch.WordTrace tailWord_4585627 prefixEnd_4585627 2354630753235035446973591 := by
  unfold tailWord_4585627
  simp only [CollatzResearch.WordTrace]
  refine ⟨167251556958064016585939135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111501037972042677723959423 167251556958064016585939135)
  ·
    refine ⟨250877335437096024878908703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167251556958064016585939135 250877335437096024878908703)
    ·
      refine ⟨376316003155644037318363055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250877335437096024878908703 376316003155644037318363055)
      ·
        refine ⟨564474004733466055977544583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376316003155644037318363055 564474004733466055977544583)
        ·
          refine ⟨846711007100199083966316875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564474004733466055977544583 846711007100199083966316875)
          ·
            refine ⟨1270066510650298625949475313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 846711007100199083966316875 1270066510650298625949475313)
            ·
              refine ⟨952549882987723969462106485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270066510650298625949475313 952549882987723969462106485)
              ·
                refine ⟨89301551530099122137072483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 952549882987723969462106485 89301551530099122137072483)
                ·
                  refine ⟨133952327295148683205608725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89301551530099122137072483 133952327295148683205608725)
                  ·
                    refine ⟨6279015341960094525262909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 133952327295148683205608725 6279015341960094525262909)
                    ·
                      refine ⟨2354630753235035446973591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6279015341960094525262909 2354630753235035446973591)
                      ·
                        rfl

theorem cell23_4585627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 3].length) (baseStart_4585627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585627 prefixEnd_4585627 := by exact prefixLift 4585627
  have htrace : WordTrace (prefixWord ++ tailWord_4585627) baseStart_4585627 baseEnd_4585627 := by
    simpa [prefixWord, tailWord_4585627, baseEnd_4585627] using wordTrace_append hprefix tailTrace_4585627
  have hstable : (prefixWord ++ tailWord_4585627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585627).length < 2 ^ (prefixWord ++ tailWord_4585627).sum := by decide
  have hdescent : baseEnd_4585627 < baseStart_4585627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585634 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_4585634 : Nat := 118140960795 + 4585634 * 2 ^ 59
def prefixEnd_4585634 : Nat := 4983230072969 + 3 ^ 40 * 4585634 * 2
def baseEnd_4585634 : Nat := 784878115866538973195353

theorem tailTrace_4585634 : CollatzResearch.WordTrace tailWord_4585634 prefixEnd_4585634 784878115866538973195353 := by
  unfold tailWord_4585634
  simp only [CollatzResearch.WordTrace]
  refine ⟨41812953067259664195360989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111501208179359104520962637 41812953067259664195360989)
  ·
    refine ⟨15679857400222374073260371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41812953067259664195360989 15679857400222374073260371)
    ·
      refine ⟨23519786100333561109890557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15679857400222374073260371 23519786100333561109890557)
      ·
        refine ⟨8819919787625085416208959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23519786100333561109890557 8819919787625085416208959)
        ·
          refine ⟨13229879681437628124313439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8819919787625085416208959 13229879681437628124313439)
          ·
            refine ⟨19844819522156442186470159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13229879681437628124313439 19844819522156442186470159)
            ·
              refine ⟨29767229283234663279705239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19844819522156442186470159 29767229283234663279705239)
              ·
                refine ⟨44650843924851994919557859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29767229283234663279705239 44650843924851994919557859)
                ·
                  refine ⟨66976265887277992379336789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44650843924851994919557859 66976265887277992379336789)
                  ·
                    refine ⟨784878115866538973195353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66976265887277992379336789 784878115866538973195353)
                    ·
                      rfl

theorem cell23_4585634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_4585634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585634 prefixEnd_4585634 := by exact prefixLift 4585634
  have htrace : WordTrace (prefixWord ++ tailWord_4585634) baseStart_4585634 baseEnd_4585634 := by
    simpa [prefixWord, tailWord_4585634, baseEnd_4585634] using wordTrace_append hprefix tailTrace_4585634
  have hstable : (prefixWord ++ tailWord_4585634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585634).length < 2 ^ (prefixWord ++ tailWord_4585634).sum := by decide
  have hdescent : baseEnd_4585634 < baseStart_4585634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585662 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_4585662 : Nat := 118140960795 + 4585662 * 2 ^ 59
def prefixEnd_4585662 : Nat := 4983230072969 + 3 ^ 40 * 4585662 * 2
def baseEnd_4585662 : Nat := 2354648725057942810035931

theorem tailTrace_4585662 : CollatzResearch.WordTrace tailWord_4585662 prefixEnd_4585662 2354648725057942810035931 := by
  unfold tailWord_4585662
  simp only [CollatzResearch.WordTrace]
  refine ⟨20906604189117152195432905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111501889008624811708975493 20906604189117152195432905)
  ·
    refine ⟨15679953141837864146574679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20906604189117152195432905 15679953141837864146574679)
    ·
      refine ⟨23519929712756796219862019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15679953141837864146574679 23519929712756796219862019)
      ·
        refine ⟨35279894569135194329793029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23519929712756796219862019 35279894569135194329793029)
        ·
          refine ⟨6614980231712848936836193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35279894569135194329793029 6614980231712848936836193)
          ·
            refine ⟨4961235173784636702627145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6614980231712848936836193 4961235173784636702627145)
            ·
              refine ⟨3720926380338477526970359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4961235173784636702627145 3720926380338477526970359)
              ·
                refine ⟨5581389570507716290455539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3720926380338477526970359 5581389570507716290455539)
                ·
                  refine ⟨8372084355761574435683309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5581389570507716290455539 8372084355761574435683309)
                  ·
                    refine ⟨3139531633410590413381241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8372084355761574435683309 3139531633410590413381241)
                    ·
                      refine ⟨2354648725057942810035931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139531633410590413381241 2354648725057942810035931)
                      ·
                        rfl

theorem cell23_4585662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_4585662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585662 prefixEnd_4585662 := by exact prefixLift 4585662
  have htrace : WordTrace (prefixWord ++ tailWord_4585662) baseStart_4585662 baseEnd_4585662 := by
    simpa [prefixWord, tailWord_4585662, baseEnd_4585662] using wordTrace_append hprefix tailTrace_4585662
  have hstable : (prefixWord ++ tailWord_4585662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585662).length < 2 ^ (prefixWord ++ tailWord_4585662).sum := by decide
  have hdescent : baseEnd_4585662 < baseStart_4585662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585674 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_4585674 : Nat := 118140960795 + 4585674 * 2 ^ 59
def prefixEnd_4585674 : Nat := 4983230072969 + 3 ^ 40 * 4585674 * 2
def baseEnd_4585674 : Nat := 2354654886825796763085875

theorem tailTrace_4585674 : CollatzResearch.WordTrace tailWord_4585674 prefixEnd_4585674 2354654886825796763085875 := by
  unfold tailWord_4585674
  simp only [CollatzResearch.WordTrace]
  refine ⟨41813317797223435903225019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111502180792595829075266717 41813317797223435903225019)
  ·
    refine ⟨62719976695835153854837529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41813317797223435903225019 62719976695835153854837529)
    ·
      refine ⟨47039982521876365391128147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62719976695835153854837529 47039982521876365391128147)
      ·
        refine ⟨70559973782814548086692221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47039982521876365391128147 70559973782814548086692221)
        ·
          refine ⟨26459990168555455532509583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70559973782814548086692221 26459990168555455532509583)
          ·
            refine ⟨39689985252833183298764375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26459990168555455532509583 39689985252833183298764375)
            ·
              refine ⟨59534977879249774948146563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39689985252833183298764375 59534977879249774948146563)
              ·
                refine ⟨89302466818874662422219845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59534977879249774948146563 89302466818874662422219845)
                ·
                  refine ⟨16744212528538999204166221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89302466818874662422219845 16744212528538999204166221)
                  ·
                    refine ⟨6279079698202124701562333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16744212528538999204166221 6279079698202124701562333)
                    ·
                      refine ⟨2354654886825796763085875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6279079698202124701562333 2354654886825796763085875)
                      ·
                        rfl

theorem cell23_4585674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_4585674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585674 prefixEnd_4585674 := by exact prefixLift 4585674
  have htrace : WordTrace (prefixWord ++ tailWord_4585674) baseStart_4585674 baseEnd_4585674 := by
    simpa [prefixWord, tailWord_4585674, baseEnd_4585674] using wordTrace_append hprefix tailTrace_4585674
  have hstable : (prefixWord ++ tailWord_4585674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585674).length < 2 ^ (prefixWord ++ tailWord_4585674).sum := by decide
  have hdescent : baseEnd_4585674 < baseStart_4585674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585687 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_4585687 : Nat := 118140960795 + 4585687 * 2 ^ 59
def prefixEnd_4585687 : Nat := 4983230072969 + 3 ^ 40 * 4585687 * 2
def baseEnd_4585687 : Nat := 2354661562074305212223315

theorem tailTrace_4585687 : CollatzResearch.WordTrace tailWord_4585687 prefixEnd_4585687 2354661562074305212223315 := by
  unfold tailWord_4585687
  simp only [CollatzResearch.WordTrace]
  refine ⟨167253745337846646833123315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111502496891897764555415543 167253745337846646833123315)
  ·
    refine ⟨250880618006769970249684973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167253745337846646833123315 250880618006769970249684973)
    ·
      refine ⟨94080231752538738843631865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250880618006769970249684973 94080231752538738843631865)
      ·
        refine ⟨70560173814404054132723899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94080231752538738843631865 70560173814404054132723899)
        ·
          refine ⟨105840260721606081199085849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70560173814404054132723899 105840260721606081199085849)
          ·
            refine ⟨79380195541204560899314387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105840260721606081199085849 79380195541204560899314387)
            ·
              refine ⟨119070293311806841348971581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79380195541204560899314387 119070293311806841348971581)
              ·
                refine ⟨44651359991927565505864343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119070293311806841348971581 44651359991927565505864343)
                ·
                  refine ⟨66977039987891348258796515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44651359991927565505864343 66977039987891348258796515)
                  ·
                    refine ⟨100465559981837022388194773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66977039987891348258796515 100465559981837022388194773)
                    ·
                      refine ⟨2354661562074305212223315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100465559981837022388194773 2354661562074305212223315)
                      ·
                        rfl

theorem cell23_4585687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_4585687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585687 prefixEnd_4585687 := by exact prefixLift 4585687
  have htrace : WordTrace (prefixWord ++ tailWord_4585687) baseStart_4585687 baseEnd_4585687 := by
    simpa [prefixWord, tailWord_4585687, baseEnd_4585687] using wordTrace_append hprefix tailTrace_4585687
  have hstable : (prefixWord ++ tailWord_4585687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585687).length < 2 ^ (prefixWord ++ tailWord_4585687).sum := by decide
  have hdescent : baseEnd_4585687 < baseStart_4585687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585692 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4585692 : Nat := 118140960795 + 4585692 * 2 ^ 59
def prefixEnd_4585692 : Nat := 4983230072969 + 3 ^ 40 * 4585692 * 2
def baseEnd_4585692 : Nat := 2354664129477577692660793

theorem tailTrace_4585692 : CollatzResearch.WordTrace tailWord_4585692 prefixEnd_4585692 2354664129477577692660793 := by
  unfold tailWord_4585692
  simp only [CollatzResearch.WordTrace]
  refine ⟨83626963851414266343527665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111502618468552355124703553 83626963851414266343527665)
  ·
    refine ⟨62720222888560699757645749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83626963851414266343527665 62720222888560699757645749)
    ·
      refine ⟨5880020895802565602279289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62720222888560699757645749 5880020895802565602279289)
      ·
        refine ⟨4410015671851924201709467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5880020895802565602279289 4410015671851924201709467)
        ·
          refine ⟨6615023507777886302564201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4410015671851924201709467 6615023507777886302564201)
          ·
            refine ⟨4961267630833414726923151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6615023507777886302564201 4961267630833414726923151)
            ·
              refine ⟨7441901446250122090384727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4961267630833414726923151 7441901446250122090384727)
              ·
                refine ⟨11162852169375183135577091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441901446250122090384727 11162852169375183135577091)
                ·
                  refine ⟨16744278254062774703365637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11162852169375183135577091 16744278254062774703365637)
                  ·
                    refine ⟨3139552172636770256881057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16744278254062774703365637 3139552172636770256881057)
                    ·
                      refine ⟨2354664129477577692660793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139552172636770256881057 2354664129477577692660793)
                      ·
                        rfl

theorem cell23_4585692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4585692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585692 prefixEnd_4585692 := by exact prefixLift 4585692
  have htrace : WordTrace (prefixWord ++ tailWord_4585692) baseStart_4585692 baseEnd_4585692 := by
    simpa [prefixWord, tailWord_4585692, baseEnd_4585692] using wordTrace_append hprefix tailTrace_4585692
  have hstable : (prefixWord ++ tailWord_4585692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585692).length < 2 ^ (prefixWord ++ tailWord_4585692).sum := by decide
  have hdescent : baseEnd_4585692 < baseStart_4585692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585707 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 2, 8]
def baseStart_4585707 : Nat := 118140960795 + 4585707 * 2 ^ 59
def prefixEnd_4585707 : Nat := 4983230072969 + 3 ^ 40 * 4585707 * 2
def baseEnd_4585707 : Nat := 784890610562465044657741

theorem tailTrace_4585707 : CollatzResearch.WordTrace tailWord_4585707 prefixEnd_4585707 784890610562465044657741 := by
  unfold tailWord_4585707
  simp only [CollatzResearch.WordTrace]
  refine ⟨167254474797774190248851375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111502983198516126832567583 167254474797774190248851375)
  ·
    refine ⟨250881712196661285373277063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167254474797774190248851375 250881712196661285373277063)
    ·
      refine ⟨376322568294991928059915595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250881712196661285373277063 376322568294991928059915595)
      ·
        refine ⟨564483852442487892089873393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376322568294991928059915595 564483852442487892089873393)
        ·
          refine ⟨423362889331865919067405045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564483852442487892089873393 423362889331865919067405045)
          ·
            refine ⟨39690270874862429912569223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 423362889331865919067405045 39690270874862429912569223)
            ·
              refine ⟨59535406312293644868853835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39690270874862429912569223 59535406312293644868853835)
              ·
                refine ⟨89303109468440467303280753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59535406312293644868853835 89303109468440467303280753)
                ·
                  refine ⟨66977332101330350477460565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89303109468440467303280753 66977332101330350477460565)
                  ·
                    refine ⟨784890610562465044657741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66977332101330350477460565 784890610562465044657741)
                    ·
                      rfl

theorem cell23_4585707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 8].length) (baseStart_4585707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585707 prefixEnd_4585707 := by exact prefixLift 4585707
  have htrace : WordTrace (prefixWord ++ tailWord_4585707) baseStart_4585707 baseEnd_4585707 := by
    simpa [prefixWord, tailWord_4585707, baseEnd_4585707] using wordTrace_append hprefix tailTrace_4585707
  have hstable : (prefixWord ++ tailWord_4585707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585707).length < 2 ^ (prefixWord ++ tailWord_4585707).sum := by decide
  have hdescent : baseEnd_4585707 < baseStart_4585707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585831 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 1, 6]
def baseStart_4585831 : Nat := 118140960795 + 4585831 * 2 ^ 59
def prefixEnd_4585831 : Nat := 4983230072969 + 3 ^ 40 * 4585831 * 2
def baseEnd_4585831 : Nat := 784911834429517549607551

theorem tailTrace_4585831 : CollatzResearch.WordTrace tailWord_4585831 prefixEnd_4585831 784911834429517549607551 := by
  unfold tailWord_4585831
  simp only [CollatzResearch.WordTrace]
  refine ⟨167258997449324959426365347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111505998299549972950910231 167258997449324959426365347)
  ·
    refine ⟨250888496173987439139548021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167258997449324959426365347 250888496173987439139548021)
    ·
      refine ⟨23520796516311322419332627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250888496173987439139548021 23520796516311322419332627)
      ·
        refine ⟨35281194774466983628998941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23520796516311322419332627 35281194774466983628998941)
        ·
          refine ⟨13230448040425118860874603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35281194774466983628998941 13230448040425118860874603)
          ·
            refine ⟨19845672060637678291311905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13230448040425118860874603 19845672060637678291311905)
            ·
              refine ⟨14884254045478258718483929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19845672060637678291311905 14884254045478258718483929)
              ·
                refine ⟨11163190534108694038862947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14884254045478258718483929 11163190534108694038862947)
                ·
                  refine ⟨16744785801163041058294421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11163190534108694038862947 16744785801163041058294421)
                  ·
                    refine ⟨784911834429517549607551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16744785801163041058294421 784911834429517549607551)
                    ·
                      rfl

theorem cell23_4585831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_4585831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585831 prefixEnd_4585831 := by exact prefixLift 4585831
  have htrace : WordTrace (prefixWord ++ tailWord_4585831) baseStart_4585831 baseEnd_4585831 := by
    simpa [prefixWord, tailWord_4585831, baseEnd_4585831] using wordTrace_append hprefix tailTrace_4585831
  have hstable : (prefixWord ++ tailWord_4585831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585831).length < 2 ^ (prefixWord ++ tailWord_4585831).sum := by decide
  have hdescent : baseEnd_4585831 < baseStart_4585831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585832 : List Nat := [2, 1, 4, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_4585832 : Nat := 118140960795 + 4585832 * 2 ^ 59
def prefixEnd_4585832 : Nat := 4983230072969 + 3 ^ 40 * 4585832 * 2
def baseEnd_4585832 : Nat := 2354736016769207144910149

theorem tailTrace_4585832 : CollatzResearch.WordTrace tailWord_4585832 prefixEnd_4585832 2354736016769207144910149 := by
  unfold tailWord_4585832
  simp only [CollatzResearch.WordTrace]
  refine ⟨83629516961160668298575875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111506022614880891064767833 83629516961160668298575875)
  ·
    refine ⟨125444275441741002447863813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83629516961160668298575875 125444275441741002447863813)
    ·
      refine ⟨23520801645326437958974465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125444275441741002447863813 23520801645326437958974465)
      ·
        refine ⟨17640601233994828469230849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23520801645326437958974465 17640601233994828469230849)
        ·
          refine ⟨13230450925496121351923137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17640601233994828469230849 13230450925496121351923137)
          ·
            refine ⟨9922838194122091013942353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13230450925496121351923137 9922838194122091013942353)
            ·
              refine ⟨7442128645591568260456765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9922838194122091013942353 7442128645591568260456765)
              ·
                refine ⟨2790798242096838097671287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7442128645591568260456765 2790798242096838097671287)
                ·
                  refine ⟨4186197363145257146506931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790798242096838097671287 4186197363145257146506931)
                  ·
                    refine ⟨6279296044717885719760397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4186197363145257146506931 6279296044717885719760397)
                    ·
                      refine ⟨2354736016769207144910149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6279296044717885719760397 2354736016769207144910149)
                      ·
                        rfl

theorem cell23_4585832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_4585832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585832 prefixEnd_4585832 := by exact prefixLift 4585832
  have htrace : WordTrace (prefixWord ++ tailWord_4585832) baseStart_4585832 baseEnd_4585832 := by
    simpa [prefixWord, tailWord_4585832, baseEnd_4585832] using wordTrace_append hprefix tailTrace_4585832
  have hstable : (prefixWord ++ tailWord_4585832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585832).length < 2 ^ (prefixWord ++ tailWord_4585832).sum := by decide
  have hdescent : baseEnd_4585832 < baseStart_4585832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585865 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 2, 4]
def baseStart_4585865 : Nat := 118140960795 + 4585865 * 2 ^ 59
def prefixEnd_4585865 : Nat := 4983230072969 + 3 ^ 40 * 4585865 * 2
def baseEnd_4585865 : Nat := 784917653876935171932499

theorem tailTrace_4585865 : CollatzResearch.WordTrace tailWord_4585865 prefixEnd_4585865 784917653876935171932499 := by
  unfold tailWord_4585865
  simp only [CollatzResearch.WordTrace]
  refine ⟨167260237531201783233103049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111506825020801188822068699 167260237531201783233103049)
  ·
    refine ⟨125445178148401337424827287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167260237531201783233103049 125445178148401337424827287)
    ·
      refine ⟨188167767222602006137240931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125445178148401337424827287 188167767222602006137240931)
      ·
        refine ⟨282251650833903009205861397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188167767222602006137240931 282251650833903009205861397)
        ·
          refine ⟨13230546132839203556524753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 282251650833903009205861397 13230546132839203556524753)
          ·
            refine ⟨9922909599629402667393565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13230546132839203556524753 9922909599629402667393565)
            ·
              refine ⟨3721091099861026000272587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9922909599629402667393565 3721091099861026000272587)
              ·
                refine ⟨5581636649791539000408881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3721091099861026000272587 5581636649791539000408881)
                ·
                  refine ⟨4186227487343654250306661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5581636649791539000408881 4186227487343654250306661)
                  ·
                    refine ⟨784917653876935171932499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4186227487343654250306661 784917653876935171932499)
                    ·
                      rfl

theorem cell23_4585865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 4].length) (baseStart_4585865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585865 prefixEnd_4585865 := by exact prefixLift 4585865
  have htrace : WordTrace (prefixWord ++ tailWord_4585865) baseStart_4585865 baseEnd_4585865 := by
    simpa [prefixWord, tailWord_4585865, baseEnd_4585865] using wordTrace_append hprefix tailTrace_4585865
  have hstable : (prefixWord ++ tailWord_4585865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585865).length < 2 ^ (prefixWord ++ tailWord_4585865).sum := by decide
  have hdescent : baseEnd_4585865 < baseStart_4585865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585868 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_4585868 : Nat := 118140960795 + 4585868 * 2 ^ 59
def prefixEnd_4585868 : Nat := 4983230072969 + 3 ^ 40 * 4585868 * 2
def baseEnd_4585868 : Nat := 2354754502072769004059983

theorem tailTrace_4585868 : CollatzResearch.WordTrace tailWord_4585868 prefixEnd_4585868 2354754502072769004059983 := by
  unfold tailWord_4585868
  simp only [CollatzResearch.WordTrace]
  refine ⟨83630173475095457372731129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111506897966793943163641505 83630173475095457372731129)
  ·
    refine ⟨62722630106321593029548347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83630173475095457372731129 62722630106321593029548347)
    ·
      refine ⟨94083945159482389544322521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62722630106321593029548347 94083945159482389544322521)
      ·
        refine ⟨70562958869611792158241891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94083945159482389544322521 70562958869611792158241891)
        ·
          refine ⟨105844438304417688237362837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70562958869611792158241891 105844438304417688237362837)
          ·
            refine ⟨4961458045519579136126383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105844438304417688237362837 4961458045519579136126383)
            ·
              refine ⟨7442187068279368704189575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4961458045519579136126383 7442187068279368704189575)
              ·
                refine ⟨11163280602419053056284363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7442187068279368704189575 11163280602419053056284363)
                ·
                  refine ⟨16744920903628579584426545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11163280602419053056284363 16744920903628579584426545)
                  ·
                    refine ⟨12558690677721434688319909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16744920903628579584426545 12558690677721434688319909)
                    ·
                      refine ⟨2354754502072769004059983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12558690677721434688319909 2354754502072769004059983)
                      ·
                        rfl

theorem cell23_4585868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_4585868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585868 prefixEnd_4585868 := by exact prefixLift 4585868
  have htrace : WordTrace (prefixWord ++ tailWord_4585868) baseStart_4585868 baseEnd_4585868 := by
    simpa [prefixWord, tailWord_4585868, baseEnd_4585868] using wordTrace_append hprefix tailTrace_4585868
  have hstable : (prefixWord ++ tailWord_4585868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585868).length < 2 ^ (prefixWord ++ tailWord_4585868).sum := by decide
  have hdescent : baseEnd_4585868 < baseStart_4585868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585888 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 4, 1, 3]
def baseStart_4585888 : Nat := 118140960795 + 4585888 * 2 ^ 59
def prefixEnd_4585888 : Nat := 4983230072969 + 3 ^ 40 * 4585888 * 2
def baseEnd_4585888 : Nat := 2354764771685858925809891

theorem tailTrace_4585888 : CollatzResearch.WordTrace tailWord_4585888 prefixEnd_4585888 2354764771685858925809891 := by
  unfold tailWord_4585888
  simp only [CollatzResearch.WordTrace]
  refine ⟨83630538205059229080595159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111507384273412305440793545 83630538205059229080595159)
  ·
    refine ⟨125445807307588843620892739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83630538205059229080595159 125445807307588843620892739)
    ·
      refine ⟨188168710961383265431339109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125445807307588843620892739 188168710961383265431339109)
      ·
        refine ⟨35281633305259362268376083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188168710961383265431339109 35281633305259362268376083)
        ·
          refine ⟨52922449957889043402564125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35281633305259362268376083 52922449957889043402564125)
          ·
            refine ⟨19845918734208391275961547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52922449957889043402564125 19845918734208391275961547)
            ·
              refine ⟨29768878101312586913942321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19845918734208391275961547 29768878101312586913942321)
              ·
                refine ⟨22326658575984440185456741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29768878101312586913942321 22326658575984440185456741)
                ·
                  refine ⟨4186248482997082534773139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22326658575984440185456741 4186248482997082534773139)
                  ·
                    refine ⟨6279372724495623802159709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4186248482997082534773139 6279372724495623802159709)
                    ·
                      refine ⟨2354764771685858925809891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6279372724495623802159709 2354764771685858925809891)
                      ·
                        rfl

theorem cell23_4585888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_4585888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585888 prefixEnd_4585888 := by exact prefixLift 4585888
  have htrace : WordTrace (prefixWord ++ tailWord_4585888) baseStart_4585888 baseEnd_4585888 := by
    simpa [prefixWord, tailWord_4585888, baseEnd_4585888] using wordTrace_append hprefix tailTrace_4585888
  have hstable : (prefixWord ++ tailWord_4585888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585888).length < 2 ^ (prefixWord ++ tailWord_4585888).sum := by decide
  have hdescent : baseEnd_4585888 < baseStart_4585888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585962 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_4585962 : Nat := 118140960795 + 4585962 * 2 ^ 59
def prefixEnd_4585962 : Nat := 4983230072969 + 3 ^ 40 * 4585962 * 2
def baseEnd_4585962 : Nat := 2354802769254291636284551

theorem tailTrace_4585962 : CollatzResearch.WordTrace tailWord_4585962 prefixEnd_4585962 2354802769254291636284551 := by
  unfold tailWord_4585962
  simp only [CollatzResearch.WordTrace]
  refine ⟨41815943852962592199846035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111509183607900245866256093 41815943852962592199846035)
  ·
    refine ⟨62723915779443888299769053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41815943852962592199846035 62723915779443888299769053)
    ·
      refine ⟨23521468417291458112413395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62723915779443888299769053 23521468417291458112413395)
      ·
        refine ⟨35282202625937187168620093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23521468417291458112413395 35282202625937187168620093)
        ·
          refine ⟨13230825984726445188232535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35282202625937187168620093 13230825984726445188232535)
          ·
            refine ⟨19846238977089667782348803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13230825984726445188232535 19846238977089667782348803)
            ·
              refine ⟨29769358465634501673523205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19846238977089667782348803 29769358465634501673523205)
              ·
                refine ⟨5581754712306469063785601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29769358465634501673523205 5581754712306469063785601)
                ·
                  refine ⟨4186316034229851797839201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5581754712306469063785601 4186316034229851797839201)
                  ·
                    refine ⟨3139737025672388848379401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4186316034229851797839201 3139737025672388848379401)
                    ·
                      refine ⟨2354802769254291636284551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139737025672388848379401 2354802769254291636284551)
                      ·
                        rfl

theorem cell23_4585962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_4585962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585962 prefixEnd_4585962 := by exact prefixLift 4585962
  have htrace : WordTrace (prefixWord ++ tailWord_4585962) baseStart_4585962 baseEnd_4585962 := by
    simpa [prefixWord, tailWord_4585962, baseEnd_4585962] using wordTrace_append hprefix tailTrace_4585962
  have hstable : (prefixWord ++ tailWord_4585962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585962).length < 2 ^ (prefixWord ++ tailWord_4585962).sum := by decide
  have hdescent : baseEnd_4585962 < baseStart_4585962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585968 : List Nat := [2, 1, 1, 1, 3, 3, 3, 4, 5]
def baseStart_4585968 : Nat := 118140960795 + 4585968 * 2 ^ 59
def prefixEnd_4585968 : Nat := 4983230072969 + 3 ^ 40 * 4585968 * 2
def baseEnd_4585968 : Nat := 261645094459802068089947

theorem tailTrace_4585968 : CollatzResearch.WordTrace tailWord_4585968 prefixEnd_4585968 261645094459802068089947 := by
  unfold tailWord_4585968
  simp only [CollatzResearch.WordTrace]
  refine ⟨83631997124914315912051279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111509329499885754549401705 83631997124914315912051279)
  ·
    refine ⟨125447995687371473868076919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83631997124914315912051279 125447995687371473868076919)
    ·
      refine ⟨188171993531057210802115379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125447995687371473868076919 188171993531057210802115379)
      ·
        refine ⟨282257990296585816203173069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188171993531057210802115379 282257990296585816203173069)
        ·
          refine ⟨105846746361219681076189901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282257990296585816203173069 105846746361219681076189901)
          ·
            refine ⟨39692529885457380403571213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105846746361219681076189901 39692529885457380403571213)
            ·
              refine ⟨14884698707046517651339205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39692529885457380403571213 14884698707046517651339205)
              ·
                refine ⟨2790881007571222059626101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14884698707046517651339205 2790881007571222059626101)
                ·
                  refine ⟨261645094459802068089947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2790881007571222059626101 261645094459802068089947)
                  ·
                    rfl

theorem cell23_4585968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 5].length) (baseStart_4585968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585968 prefixEnd_4585968 := by exact prefixLift 4585968
  have htrace : WordTrace (prefixWord ++ tailWord_4585968) baseStart_4585968 baseEnd_4585968 := by
    simpa [prefixWord, tailWord_4585968, baseEnd_4585968] using wordTrace_append hprefix tailTrace_4585968
  have hstable : (prefixWord ++ tailWord_4585968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585968).length < 2 ^ (prefixWord ++ tailWord_4585968).sum := by decide
  have hdescent : baseEnd_4585968 < baseStart_4585968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585981 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_4585981 : Nat := 118140960795 + 4585981 * 2 ^ 59
def prefixEnd_4585981 : Nat := 4983230072969 + 3 ^ 40 * 4585981 * 2
def baseEnd_4585981 : Nat := 784937508462242353982321

theorem tailTrace_4585981 : CollatzResearch.WordTrace tailWord_4585981 prefixEnd_4585981 784937508462242353982321 := by
  unfold tailWord_4585981
  simp only [CollatzResearch.WordTrace]
  refine ⟨167264468398781535044325797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111509645599187690029550531 167264468398781535044325797)
  ·
    refine ⟨31362087824771537820811087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167264468398781535044325797 31362087824771537820811087)
    ·
      refine ⟨47043131737157306731216631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31362087824771537820811087 47043131737157306731216631)
      ·
        refine ⟨70564697605735960096824947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47043131737157306731216631 70564697605735960096824947)
        ·
          refine ⟨105847046408603940145237421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70564697605735960096824947 105847046408603940145237421)
          ·
            refine ⟨39692642403226477554464033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105847046408603940145237421 39692642403226477554464033)
            ·
              refine ⟨29769481802419858165848025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39692642403226477554464033 29769481802419858165848025)
              ·
                refine ⟨22327111351814893624386019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29769481802419858165848025 22327111351814893624386019)
                ·
                  refine ⟨33490667027722340436579029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22327111351814893624386019 33490667027722340436579029)
                  ·
                    refine ⟨784937508462242353982321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33490667027722340436579029 784937508462242353982321)
                    ·
                      rfl

theorem cell23_4585981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_4585981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585981 prefixEnd_4585981 := by exact prefixLift 4585981
  have htrace : WordTrace (prefixWord ++ tailWord_4585981) baseStart_4585981 baseEnd_4585981 := by
    simpa [prefixWord, tailWord_4585981, baseEnd_4585981] using wordTrace_append hprefix tailTrace_4585981
  have hstable : (prefixWord ++ tailWord_4585981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585981).length < 2 ^ (prefixWord ++ tailWord_4585981).sum := by decide
  have hdescent : baseEnd_4585981 < baseStart_4585981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4585998 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_4585998 : Nat := 118140960795 + 4585998 * 2 ^ 59
def prefixEnd_4585998 : Nat := 4983230072969 + 3 ^ 40 * 4585998 * 2
def baseEnd_4585998 : Nat := 784940418185951165144795

theorem tailTrace_4585998 : CollatzResearch.WordTrace tailWord_4585998 prefixEnd_4585998 784940418185951165144795 := by
  unfold tailWord_4585998
  simp only [CollatzResearch.WordTrace]
  refine ⟨20908136054964993368461831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111510058959813297965129765 20908136054964993368461831)
  ·
    refine ⟨31362204082447490052692747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20908136054964993368461831 31362204082447490052692747)
    ·
      refine ⟨47043306123671235079039121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31362204082447490052692747 47043306123671235079039121)
      ·
        refine ⟨35282479592753426309279341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47043306123671235079039121 35282479592753426309279341)
        ·
          refine ⟨13230929847282534865979753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35282479592753426309279341 13230929847282534865979753)
          ·
            refine ⟨9923197385461901149484815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13230929847282534865979753 9923197385461901149484815)
            ·
              refine ⟨14884796078192851724227223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9923197385461901149484815 14884796078192851724227223)
              ·
                refine ⟨22327194117289277586340835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14884796078192851724227223 22327194117289277586340835)
                ·
                  refine ⟨33490791175933916379511253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22327194117289277586340835 33490791175933916379511253)
                  ·
                    refine ⟨784940418185951165144795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33490791175933916379511253 784940418185951165144795)
                    ·
                      rfl

theorem cell23_4585998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_4585998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4585998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4585998 prefixEnd_4585998 := by exact prefixLift 4585998
  have htrace : WordTrace (prefixWord ++ tailWord_4585998) baseStart_4585998 baseEnd_4585998 := by
    simpa [prefixWord, tailWord_4585998, baseEnd_4585998] using wordTrace_append hprefix tailTrace_4585998
  have hstable : (prefixWord ++ tailWord_4585998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4585998).length < 2 ^ (prefixWord ++ tailWord_4585998).sum := by decide
  have hdescent : baseEnd_4585998 < baseStart_4585998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4585998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586018 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_4586018 : Nat := 118140960795 + 4586018 * 2 ^ 59
def prefixEnd_4586018 : Nat := 4983230072969 + 3 ^ 40 * 4586018 * 2
def baseEnd_4586018 : Nat := 2354831524170943417184293

theorem tailTrace_4586018 : CollatzResearch.WordTrace tailWord_4586018 prefixEnd_4586018 2354831524170943417184293 := by
  unfold tailWord_4586018
  simp only [CollatzResearch.WordTrace]
  refine ⟨41816454474911872590855677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111510545266431660242281805 41816454474911872590855677)
  ·
    refine ⟨15681170428091952221570879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41816454474911872590855677 15681170428091952221570879)
    ·
      refine ⟨23521755642137928332356319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15681170428091952221570879 23521755642137928332356319)
      ·
        refine ⟨35282633463206892498534479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23521755642137928332356319 35282633463206892498534479)
        ·
          refine ⟨52923950194810338747801719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35282633463206892498534479 52923950194810338747801719)
          ·
            refine ⟨79385925292215508121702579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52923950194810338747801719 79385925292215508121702579)
            ·
              refine ⟨119078887938323262182553869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79385925292215508121702579 119078887938323262182553869)
              ·
                refine ⟨44654582976871223318457701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119078887938323262182553869 44654582976871223318457701)
                ·
                  refine ⟨8372734308163354372210819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44654582976871223318457701 8372734308163354372210819)
                  ·
                    refine ⟨12559101462245031558316229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8372734308163354372210819 12559101462245031558316229)
                    ·
                      refine ⟨2354831524170943417184293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12559101462245031558316229 2354831524170943417184293)
                      ·
                        rfl

theorem cell23_4586018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_4586018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586018 prefixEnd_4586018 := by exact prefixLift 4586018
  have htrace : WordTrace (prefixWord ++ tailWord_4586018) baseStart_4586018 baseEnd_4586018 := by
    simpa [prefixWord, tailWord_4586018, baseEnd_4586018] using wordTrace_append hprefix tailTrace_4586018
  have hstable : (prefixWord ++ tailWord_4586018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586018).length < 2 ^ (prefixWord ++ tailWord_4586018).sum := by decide
  have hdescent : baseEnd_4586018 < baseStart_4586018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586021 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_4586021 : Nat := 118140960795 + 4586021 * 2 ^ 59
def prefixEnd_4586021 : Nat := 4983230072969 + 3 ^ 40 * 4586021 * 2
def baseEnd_4586021 : Nat := 2354833064612906905446779

theorem tailTrace_4586021 : CollatzResearch.WordTrace tailWord_4586021 prefixEnd_4586021 2354833064612906905446779 := by
  unfold tailWord_4586021
  simp only [CollatzResearch.WordTrace]
  refine ⟨167265927318636621875781917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111510618212424414583854611 167265927318636621875781917)
  ·
    refine ⟨62724722744488733203418219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167265927318636621875781917 62724722744488733203418219)
    ·
      refine ⟨94087084116733099805127329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62724722744488733203418219 94087084116733099805127329)
      ·
        refine ⟨70565313087549824853845497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94087084116733099805127329 70565313087549824853845497)
        ·
          refine ⟨52923984815662368640384123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70565313087549824853845497 52923984815662368640384123)
          ·
            refine ⟨79385977223493552960576185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52923984815662368640384123 79385977223493552960576185)
            ·
              refine ⟨59539482917620164720432139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79385977223493552960576185 59539482917620164720432139)
              ·
                refine ⟨89309224376430247080648209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59539482917620164720432139 89309224376430247080648209)
                ·
                  refine ⟨66981918282322685310486157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89309224376430247080648209 66981918282322685310486157)
                  ·
                    refine ⟨25118219355871006991432309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66981918282322685310486157 25118219355871006991432309)
                    ·
                      refine ⟨2354833064612906905446779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25118219355871006991432309 2354833064612906905446779)
                      ·
                        rfl

theorem cell23_4586021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_4586021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586021 prefixEnd_4586021 := by exact prefixLift 4586021
  have htrace : WordTrace (prefixWord ++ tailWord_4586021) baseStart_4586021 baseEnd_4586021 := by
    simpa [prefixWord, tailWord_4586021, baseEnd_4586021] using wordTrace_append hprefix tailTrace_4586021
  have hstable : (prefixWord ++ tailWord_4586021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586021).length < 2 ^ (prefixWord ++ tailWord_4586021).sum := by decide
  have hdescent : baseEnd_4586021 < baseStart_4586021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586045 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_4586045 : Nat := 118140960795 + 4586045 * 2 ^ 59
def prefixEnd_4586045 : Nat := 4983230072969 + 3 ^ 40 * 4586045 * 2
def baseEnd_4586045 : Nat := 784948462716204937182223

theorem tailTrace_4586045 : CollatzResearch.WordTrace tailWord_4586045 prefixEnd_4586045 784948462716204937182223 := by
  unfold tailWord_4586045
  simp only [CollatzResearch.WordTrace]
  refine ⟨167266802670549673974655589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111511201780366449316437059 167266802670549673974655589)
  ·
    refine ⟨31362525500728063870247923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167266802670549673974655589 31362525500728063870247923)
    ·
      refine ⟨47043788251092095805371885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31362525500728063870247923 47043788251092095805371885)
      ·
        refine ⟨17641420594159535927014457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47043788251092095805371885 17641420594159535927014457)
        ·
          refine ⟨13231065445619651945260843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17641420594159535927014457 13231065445619651945260843)
          ·
            refine ⟨19846598168429477917891265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13231065445619651945260843 19846598168429477917891265)
            ·
              refine ⟨14884948626322108438418449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19846598168429477917891265 14884948626322108438418449)
              ·
                refine ⟨11163711469741581328813837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14884948626322108438418449 11163711469741581328813837)
                ·
                  refine ⟨4186391801153092998305189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11163711469741581328813837 4186391801153092998305189)
                  ·
                    refine ⟨784948462716204937182223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4186391801153092998305189 784948462716204937182223)
                    ·
                      rfl

theorem cell23_4586045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_4586045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586045 prefixEnd_4586045 := by exact prefixLift 4586045
  have htrace : WordTrace (prefixWord ++ tailWord_4586045) baseStart_4586045 baseEnd_4586045 := by
    simpa [prefixWord, tailWord_4586045, baseEnd_4586045] using wordTrace_append hprefix tailTrace_4586045
  have hstable : (prefixWord ++ tailWord_4586045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586045).length < 2 ^ (prefixWord ++ tailWord_4586045).sum := by decide
  have hdescent : baseEnd_4586045 < baseStart_4586045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586062 : List Nat := [4, 1, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_4586062 : Nat := 118140960795 + 4586062 * 2 ^ 59
def prefixEnd_4586062 : Nat := 4983230072969 + 3 ^ 40 * 4586062 * 2
def baseEnd_4586062 : Nat := 784951372439913748344697

theorem tailTrace_4586062 : CollatzResearch.WordTrace tailWord_4586062 prefixEnd_4586062 784951372439913748344697 := by
  unfold tailWord_4586062
  simp only [CollatzResearch.WordTrace]
  refine ⟨20908427838936010734753055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111511615140992057252016293 20908427838936010734753055)
  ·
    refine ⟨31362641758404016102129583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20908427838936010734753055 31362641758404016102129583)
    ·
      refine ⟨47043962637606024153194375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31362641758404016102129583 47043962637606024153194375)
      ·
        refine ⟨70565943956409036229791563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47043962637606024153194375 70565943956409036229791563)
        ·
          refine ⟨105848915934613554344687345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70565943956409036229791563 105848915934613554344687345)
          ·
            refine ⟨79386686950960165758515509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105848915934613554344687345 79386686950960165758515509)
            ·
              refine ⟨7442501901652515539860829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79386686950960165758515509 7442501901652515539860829)
              ·
                refine ⟨2790938213119693327447811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7442501901652515539860829 2790938213119693327447811)
                ·
                  refine ⟨4186407319679539991171717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790938213119693327447811 4186407319679539991171717)
                  ·
                    refine ⟨784951372439913748344697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4186407319679539991171717 784951372439913748344697)
                    ·
                      rfl

theorem cell23_4586062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_4586062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586062 prefixEnd_4586062 := by exact prefixLift 4586062
  have htrace : WordTrace (prefixWord ++ tailWord_4586062) baseStart_4586062 baseEnd_4586062 := by
    simpa [prefixWord, tailWord_4586062, baseEnd_4586062] using wordTrace_append hprefix tailTrace_4586062
  have hstable : (prefixWord ++ tailWord_4586062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586062).length < 2 ^ (prefixWord ++ tailWord_4586062).sum := by decide
  have hdescent : baseEnd_4586062 < baseStart_4586062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586105 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 1, 5]
def baseStart_4586105 : Nat := 118140960795 + 4586105 * 2 ^ 59
def prefixEnd_4586105 : Nat := 4983230072969 + 3 ^ 40 * 4586105 * 2
def baseEnd_4586105 : Nat := 784958732329294858932131

theorem tailTrace_4586105 : CollatzResearch.WordTrace tailWord_4586105 prefixEnd_4586105 784958732329294858932131 := by
  unfold tailWord_4586105
  simp only [CollatzResearch.WordTrace]
  refine ⟨167268991050332304221839769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111512660700221536147893179 167268991050332304221839769)
  ·
    refine ⟨125451743287749228166379827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167268991050332304221839769 125451743287749228166379827)
    ·
      refine ⟨188177614931623842249569741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125451743287749228166379827 188177614931623842249569741)
      ·
        refine ⟨70566605599358940843588653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188177614931623842249569741 70566605599358940843588653)
        ·
          refine ⟨26462477099759602816345745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70566605599358940843588653 26462477099759602816345745)
          ·
            refine ⟨19846857824819702112259309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26462477099759602816345745 19846857824819702112259309)
            ·
              refine ⟨7442571684307388292097241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19846857824819702112259309 7442571684307388292097241)
              ·
                refine ⟨5581928763230541219072931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7442571684307388292097241 5581928763230541219072931)
                ·
                  refine ⟨8372893144845811828609397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5581928763230541219072931 8372893144845811828609397)
                  ·
                    refine ⟨784958732329294858932131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8372893144845811828609397 784958732329294858932131)
                    ·
                      rfl

theorem cell23_4586105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_4586105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586105 prefixEnd_4586105 := by exact prefixLift 4586105
  have htrace : WordTrace (prefixWord ++ tailWord_4586105) baseStart_4586105 baseEnd_4586105 := by
    simpa [prefixWord, tailWord_4586105, baseEnd_4586105] using wordTrace_append hprefix tailTrace_4586105
  have hstable : (prefixWord ++ tailWord_4586105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586105).length < 2 ^ (prefixWord ++ tailWord_4586105).sum := by decide
  have hdescent : baseEnd_4586105 < baseStart_4586105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586112 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 2, 3, 2]
def baseStart_4586112 : Nat := 118140960795 + 4586112 * 2 ^ 59
def prefixEnd_4586112 : Nat := 4983230072969 + 3 ^ 40 * 4586112 * 2
def baseEnd_4586112 : Nat := 2354879791352466049408861

theorem tailTrace_4586112 : CollatzResearch.WordTrace tailWord_4586112 prefixEnd_4586112 2354879791352466049408861 := by
  unfold tailWord_4586112
  simp only [CollatzResearch.WordTrace]
  refine ⟨83634623180653472208672295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111512830907537962944896393 83634623180653472208672295)
  ·
    refine ⟨125451934770980208313008443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83634623180653472208672295 125451934770980208313008443)
    ·
      refine ⟨188177902156470312469512665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125451934770980208313008443 188177902156470312469512665)
      ·
        refine ⟨141133426617352734352134499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188177902156470312469512665 141133426617352734352134499)
        ·
          refine ⟨211700139926029101528201749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141133426617352734352134499 211700139926029101528201749)
          ·
            refine ⟨9923444059032614134134457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211700139926029101528201749 9923444059032614134134457)
            ·
              refine ⟨7442583044274460600600843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9923444059032614134134457 7442583044274460600600843)
              ·
                refine ⟨11163874566411690900901265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7442583044274460600600843 11163874566411690900901265)
                ·
                  refine ⟨8372905924808768175675949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11163874566411690900901265 8372905924808768175675949)
                  ·
                    refine ⟨3139839721803288065878481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8372905924808768175675949 3139839721803288065878481)
                    ·
                      refine ⟨2354879791352466049408861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139839721803288065878481 2354879791352466049408861)
                      ·
                        rfl

theorem cell23_4586112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_4586112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586112 prefixEnd_4586112 := by exact prefixLift 4586112
  have htrace : WordTrace (prefixWord ++ tailWord_4586112) baseStart_4586112 baseEnd_4586112 := by
    simpa [prefixWord, tailWord_4586112, baseEnd_4586112] using wordTrace_append hprefix tailTrace_4586112
  have hstable : (prefixWord ++ tailWord_4586112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586112).length < 2 ^ (prefixWord ++ tailWord_4586112).sum := by decide
  have hdescent : baseEnd_4586112 < baseStart_4586112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586175 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 3]
def baseStart_4586175 : Nat := 118140960795 + 4586175 * 2 ^ 59
def prefixEnd_4586175 : Nat := 4983230072969 + 3 ^ 40 * 4586175 * 2
def baseEnd_4586175 : Nat := 2354912140633699302921071

theorem tailTrace_4586175 : CollatzResearch.WordTrace tailWord_4586175 prefixEnd_4586175 2354912140633699302921071 := by
  unfold tailWord_4586175
  simp only [CollatzResearch.WordTrace]
  refine ⟨167271544160078706176887979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111514362773385804117925319 167271544160078706176887979)
  ·
    refine ⟨250907316240118059265331969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167271544160078706176887979 250907316240118059265331969)
    ·
      refine ⟨188180487180088544448998977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250907316240118059265331969 188180487180088544448998977)
      ·
        refine ⟨141135365385066408336749233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188180487180088544448998977 141135365385066408336749233)
        ·
          refine ⟨105851524038799806252561925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141135365385066408336749233 105851524038799806252561925)
          ·
            refine ⟨19847160757274963672355361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105851524038799806252561925 19847160757274963672355361)
            ·
              refine ⟨14885370567956222754266521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19847160757274963672355361 14885370567956222754266521)
              ·
                refine ⟨11164027925967167065699891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14885370567956222754266521 11164027925967167065699891)
                ·
                  refine ⟨16746041888950750598549837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11164027925967167065699891 16746041888950750598549837)
                  ·
                    refine ⟨6279765708356531474456189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16746041888950750598549837 6279765708356531474456189)
                    ·
                      refine ⟨2354912140633699302921071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6279765708356531474456189 2354912140633699302921071)
                      ·
                        rfl

theorem cell23_4586175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_4586175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586175 prefixEnd_4586175 := by exact prefixLift 4586175
  have htrace : WordTrace (prefixWord ++ tailWord_4586175) baseStart_4586175 baseEnd_4586175 := by
    simpa [prefixWord, tailWord_4586175, baseEnd_4586175] using wordTrace_append hprefix tailTrace_4586175
  have hstable : (prefixWord ++ tailWord_4586175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586175).length < 2 ^ (prefixWord ++ tailWord_4586175).sum := by decide
  have hdescent : baseEnd_4586175 < baseStart_4586175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586176 : List Nat := [2, 1, 1, 2, 4, 3, 2, 3, 1, 2, 2]
def baseStart_4586176 : Nat := 118140960795 + 4586176 * 2 ^ 59
def prefixEnd_4586176 : Nat := 4983230072969 + 3 ^ 40 * 4586176 * 2
def baseEnd_4586176 : Nat := 2354912654114353799008567

theorem tailTrace_4586176 : CollatzResearch.WordTrace tailWord_4586176 prefixEnd_4586176 2354912654114353799008567 := by
  unfold tailWord_4586176
  simp only [CollatzResearch.WordTrace]
  refine ⟨83635790316537541673837191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111514387088716722231782921 83635790316537541673837191)
  ·
    refine ⟨125453685474806312510755787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83635790316537541673837191 125453685474806312510755787)
    ·
      refine ⟨188180528212209468766133681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125453685474806312510755787 188180528212209468766133681)
      ·
        refine ⟨141135396159157101574600261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188180528212209468766133681 141135396159157101574600261)
        ·
          refine ⟨26462886779841956545237549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141135396159157101574600261 26462886779841956545237549)
          ·
            refine ⟨9923582542440733704464081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26462886779841956545237549 9923582542440733704464081)
            ·
              refine ⟨7442686906830550278348061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9923582542440733704464081 7442686906830550278348061)
              ·
                refine ⟨2791007590061456354380523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7442686906830550278348061 2791007590061456354380523)
                ·
                  refine ⟨4186511385092184531570785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791007590061456354380523 4186511385092184531570785)
                  ·
                    refine ⟨3139883538819138398678089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4186511385092184531570785 3139883538819138398678089)
                    ·
                      refine ⟨2354912654114353799008567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139883538819138398678089 2354912654114353799008567)
                      ·
                        rfl

theorem cell23_4586176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_4586176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586176 prefixEnd_4586176 := by exact prefixLift 4586176
  have htrace : WordTrace (prefixWord ++ tailWord_4586176) baseStart_4586176 baseEnd_4586176 := by
    simpa [prefixWord, tailWord_4586176, baseEnd_4586176] using wordTrace_append hprefix tailTrace_4586176
  have hstable : (prefixWord ++ tailWord_4586176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586176).length < 2 ^ (prefixWord ++ tailWord_4586176).sum := by decide
  have hdescent : baseEnd_4586176 < baseStart_4586176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586232 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 6, 2, 2]
def baseStart_4586232 : Nat := 118140960795 + 4586232 * 2 ^ 59
def prefixEnd_4586232 : Nat := 4983230072969 + 3 ^ 40 * 4586232 * 2
def baseEnd_4586232 : Nat := 2354941409031005579908309

theorem tailTrace_4586232 : CollatzResearch.WordTrace tailWord_4586232 prefixEnd_4586232 2354941409031005579908309 := by
  unfold tailWord_4586232
  simp only [CollatzResearch.WordTrace]
  refine ⟨83636811560436102455856475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111515748747248136607808633 83636811560436102455856475)
  ·
    refine ⟨125455217340654153683784713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83636811560436102455856475 125455217340654153683784713)
    ·
      refine ⟨94091413005490615262838535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125455217340654153683784713 94091413005490615262838535)
      ·
        refine ⟨141137119508235922894257803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94091413005490615262838535 141137119508235922894257803)
        ·
          refine ⟨211705679262353884341386705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141137119508235922894257803 211705679262353884341386705)
          ·
            refine ⟨158779259446765413256040029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211705679262353884341386705 158779259446765413256040029)
            ·
              refine ⟨59542222292537029971015011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158779259446765413256040029 59542222292537029971015011)
              ·
                refine ⟨89313333438805544956522517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59542222292537029971015011 89313333438805544956522517)
                ·
                  refine ⟨4186562504944009919836993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89313333438805544956522517 4186562504944009919836993)
                  ·
                    refine ⟨3139921878708007439877745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4186562504944009919836993 3139921878708007439877745)
                    ·
                      refine ⟨2354941409031005579908309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3139921878708007439877745 2354941409031005579908309)
                      ·
                        rfl

theorem cell23_4586232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_4586232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586232 prefixEnd_4586232 := by exact prefixLift 4586232
  have htrace : WordTrace (prefixWord ++ tailWord_4586232) baseStart_4586232 baseEnd_4586232 := by
    simpa [prefixWord, tailWord_4586232, baseEnd_4586232] using wordTrace_append hprefix tailTrace_4586232
  have hstable : (prefixWord ++ tailWord_4586232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586232).length < 2 ^ (prefixWord ++ tailWord_4586232).sum := by decide
  have hdescent : baseEnd_4586232 < baseStart_4586232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586315 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 9, 4]
def baseStart_4586315 : Nat := 118140960795 + 4586315 * 2 ^ 59
def prefixEnd_4586315 : Nat := 4983230072969 + 3 ^ 40 * 4586315 * 2
def baseEnd_4586315 : Nat := 784994675975109585056809

theorem tailTrace_4586315 : CollatzResearch.WordTrace tailWord_4586315 prefixEnd_4586315 784994675975109585056809 := by
  unfold tailWord_4586315
  simp only [CollatzResearch.WordTrace]
  refine ⟨167276650379571510086984399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111517766919714340057989599 167276650379571510086984399)
  ·
    refine ⟨250914975569357265130476599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167276650379571510086984399 250914975569357265130476599)
    ·
      refine ⟨376372463354035897695714899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250914975569357265130476599 376372463354035897695714899)
      ·
        refine ⟨564558695031053846543572349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376372463354035897695714899 564558695031053846543572349)
        ·
          refine ⟨211709510636645192453839631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 564558695031053846543572349 211709510636645192453839631)
          ·
            refine ⟨317564265954967788680759447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211709510636645192453839631 317564265954967788680759447)
            ·
              refine ⟨476346398932451683021139171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317564265954967788680759447 476346398932451683021139171)
              ·
                refine ⟨714519598398677524531708757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476346398932451683021139171 714519598398677524531708757)
                ·
                  refine ⟨4186638271867251120302981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 714519598398677524531708757 4186638271867251120302981)
                  ·
                    refine ⟨784994675975109585056809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4186638271867251120302981 784994675975109585056809)
                    ·
                      rfl

theorem cell23_4586315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 4].length) (baseStart_4586315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586315 prefixEnd_4586315 := by exact prefixLift 4586315
  have htrace : WordTrace (prefixWord ++ tailWord_4586315) baseStart_4586315 baseEnd_4586315 := by
    simpa [prefixWord, tailWord_4586315, baseEnd_4586315] using wordTrace_append hprefix tailTrace_4586315
  have hstable : (prefixWord ++ tailWord_4586315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586315).length < 2 ^ (prefixWord ++ tailWord_4586315).sum := by decide
  have hdescent : baseEnd_4586315 < baseStart_4586315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586339 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 4]
def baseStart_4586339 : Nat := 118140960795 + 4586339 * 2 ^ 59
def prefixEnd_4586339 : Nat := 4983230072969 + 3 ^ 40 * 4586339 * 2
def baseEnd_4586339 : Nat := 2354996351461036661270317

theorem tailTrace_4586339 : CollatzResearch.WordTrace tailWord_4586339 prefixEnd_4586339 2354996351461036661270317 := by
  unfold tailWord_4586339
  simp only [CollatzResearch.WordTrace]
  refine ⟨167277525731484562185858071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111518350487656374790572047 167277525731484562185858071)
  ·
    refine ⟨250916288597226843278787107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167277525731484562185858071 250916288597226843278787107)
    ·
      refine ⟨376374432895840264918180661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250916288597226843278787107 376374432895840264918180661)
      ·
        refine ⟨35285103083985024836079437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 376374432895840264918180661 35285103083985024836079437)
        ·
          refine ⟨13231913656494384313529789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35285103083985024836079437 13231913656494384313529789)
          ·
            refine ⟨4961967621185394117573671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13231913656494384313529789 4961967621185394117573671)
            ·
              refine ⟨7442951431778091176360507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4961967621185394117573671 7442951431778091176360507)
              ·
                refine ⟨11164427147667136764540761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7442951431778091176360507 11164427147667136764540761)
                ·
                  refine ⟨8373320360750352573405571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11164427147667136764540761 8373320360750352573405571)
                  ·
                    refine ⟨12559980541125528860108357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8373320360750352573405571 12559980541125528860108357)
                    ·
                      refine ⟨2354996351461036661270317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12559980541125528860108357 2354996351461036661270317)
                      ·
                        rfl

theorem cell23_4586339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_4586339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586339 prefixEnd_4586339 := by exact prefixLift 4586339
  have htrace : WordTrace (prefixWord ++ tailWord_4586339) baseStart_4586339 baseEnd_4586339 := by
    simpa [prefixWord, tailWord_4586339, baseEnd_4586339] using wordTrace_append hprefix tailTrace_4586339
  have hstable : (prefixWord ++ tailWord_4586339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586339).length < 2 ^ (prefixWord ++ tailWord_4586339).sum := by decide
  have hdescent : baseEnd_4586339 < baseStart_4586339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586365 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_4586365 : Nat := 118140960795 + 4586365 * 2 ^ 59
def prefixEnd_4586365 : Nat := 4983230072969 + 3 ^ 40 * 4586365 * 2
def baseEnd_4586365 : Nat := 2355009701958053559545197

theorem tailTrace_4586365 : CollatzResearch.WordTrace tailWord_4586365 prefixEnd_4586365 2355009701958053559545197 := by
  unfold tailWord_4586365
  simp only [CollatzResearch.WordTrace]
  refine ⟨167278474029390368626304549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111518982686260245750869699 167278474029390368626304549)
  ·
    refine ⟨31364713880510694117432103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167278474029390368626304549 31364713880510694117432103)
    ·
      refine ⟨47047070820766041176148155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31364713880510694117432103 47047070820766041176148155)
      ·
        refine ⟨70570606231149061764222233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47047070820766041176148155 70570606231149061764222233)
        ·
          refine ⟨52927954673361796323166675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70570606231149061764222233 52927954673361796323166675)
          ·
            refine ⟨79391932010042694484750013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52927954673361796323166675 79391932010042694484750013)
            ·
              refine ⟨29771974503766010431781255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79391932010042694484750013 29771974503766010431781255)
              ·
                refine ⟨44657961755649015647671883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29771974503766010431781255 44657961755649015647671883)
                ·
                  refine ⟨66986942633473523471507825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44657961755649015647671883 66986942633473523471507825)
                  ·
                    refine ⟨50240206975105142603630869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66986942633473523471507825 50240206975105142603630869)
                    ·
                      refine ⟨2355009701958053559545197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50240206975105142603630869 2355009701958053559545197)
                      ·
                        rfl

theorem cell23_4586365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_4586365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586365 prefixEnd_4586365 := by exact prefixLift 4586365
  have htrace : WordTrace (prefixWord ++ tailWord_4586365) baseStart_4586365 baseEnd_4586365 := by
    simpa [prefixWord, tailWord_4586365, baseEnd_4586365] using wordTrace_append hprefix tailTrace_4586365
  have hstable : (prefixWord ++ tailWord_4586365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586365).length < 2 ^ (prefixWord ++ tailWord_4586365).sum := by decide
  have hdescent : baseEnd_4586365 < baseStart_4586365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586389 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_4586389 : Nat := 118140960795 + 4586389 * 2 ^ 59
def prefixEnd_4586389 : Nat := 4983230072969 + 3 ^ 40 * 4586389 * 2
def baseEnd_4586389 : Nat := 2355022025493761465645087

theorem tailTrace_4586389 : CollatzResearch.WordTrace tailWord_4586389 prefixEnd_4586389 2355022025493761465645087 := by
  unfold tailWord_4586389
  simp only [CollatzResearch.WordTrace]
  refine ⟨167279349381303420725178221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111519566254202280483452147 167279349381303420725178221)
  ·
    refine ⟨62729756017988782771941833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167279349381303420725178221 62729756017988782771941833)
    ·
      refine ⟨47047317013491587078956375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62729756017988782771941833 47047317013491587078956375)
      ·
        refine ⟨70570975520237380618434563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47047317013491587078956375 70570975520237380618434563)
        ·
          refine ⟨105856463280356070927651845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70570975520237380618434563 105856463280356070927651845)
          ·
            refine ⟨19848086865066763298934721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105856463280356070927651845 19848086865066763298934721)
            ·
              refine ⟨14886065148800072474201041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19848086865066763298934721 14886065148800072474201041)
              ·
                refine ⟨11164548861600054355650781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14886065148800072474201041 11164548861600054355650781)
                ·
                  refine ⟨4186705823100020383369043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11164548861600054355650781 4186705823100020383369043)
                  ·
                    refine ⟨6280058734650030575053565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4186705823100020383369043 6280058734650030575053565)
                    ·
                      refine ⟨2355022025493761465645087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6280058734650030575053565 2355022025493761465645087)
                      ·
                        rfl

theorem cell23_4586389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_4586389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586389 prefixEnd_4586389 := by exact prefixLift 4586389
  have htrace : WordTrace (prefixWord ++ tailWord_4586389) baseStart_4586389 baseEnd_4586389 := by
    simpa [prefixWord, tailWord_4586389, baseEnd_4586389] using wordTrace_append hprefix tailTrace_4586389
  have hstable : (prefixWord ++ tailWord_4586389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586389).length < 2 ^ (prefixWord ++ tailWord_4586389).sum := by decide
  have hdescent : baseEnd_4586389 < baseStart_4586389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586399 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 1, 5, 2]
def baseStart_4586399 : Nat := 118140960795 + 4586399 * 2 ^ 59
def prefixEnd_4586399 : Nat := 4983230072969 + 3 ^ 40 * 4586399 * 2
def baseEnd_4586399 : Nat := 2355027160300306426520041

theorem tailTrace_4586399 : CollatzResearch.WordTrace tailWord_4586399 prefixEnd_4586399 2355027160300306426520041 := by
  unfold tailWord_4586399
  simp only [CollatzResearch.WordTrace]
  refine ⟨167279714111267192433042251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111519809407511461622028167 167279714111267192433042251)
  ·
    refine ⟨250919571166900788649563377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167279714111267192433042251 250919571166900788649563377)
    ·
      refine ⟨188189678375175591487172533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250919571166900788649563377 188189678375175591487172533)
      ·
        refine ⟨17642782347672711701922425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188189678375175591487172533 17642782347672711701922425)
        ·
          refine ⟨13232086760754533776441819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17642782347672711701922425 13232086760754533776441819)
          ·
            refine ⟨19848130141131800664662729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13232086760754533776441819 19848130141131800664662729)
            ·
              refine ⟨14886097605848850498497047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19848130141131800664662729 14886097605848850498497047)
              ·
                refine ⟨22329146408773275747745571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14886097605848850498497047 22329146408773275747745571)
                ·
                  refine ⟨33493719613159913621618357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22329146408773275747745571 33493719613159913621618357)
                  ·
                    refine ⟨3140036213733741902026721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33493719613159913621618357 3140036213733741902026721)
                    ·
                      refine ⟨2355027160300306426520041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140036213733741902026721 2355027160300306426520041)
                      ·
                        rfl

theorem cell23_4586399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_4586399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586399 prefixEnd_4586399 := by exact prefixLift 4586399
  have htrace : WordTrace (prefixWord ++ tailWord_4586399) baseStart_4586399 baseEnd_4586399 := by
    simpa [prefixWord, tailWord_4586399, baseEnd_4586399] using wordTrace_append hprefix tailTrace_4586399
  have hstable : (prefixWord ++ tailWord_4586399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586399).length < 2 ^ (prefixWord ++ tailWord_4586399).sum := by decide
  have hdescent : baseEnd_4586399 < baseStart_4586399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586412 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 8, 2]
def baseStart_4586412 : Nat := 118140960795 + 4586412 * 2 ^ 59
def prefixEnd_4586412 : Nat := 4983230072969 + 3 ^ 40 * 4586412 * 2
def baseEnd_4586412 : Nat := 2355033835548814875657481

theorem tailTrace_4586412 : CollatzResearch.WordTrace tailWord_4586412 prefixEnd_4586412 2355033835548814875657481 := by
  unfold tailWord_4586412
  simp only [CollatzResearch.WordTrace]
  refine ⟨83640094130110047826632745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111520125506813397102176993 83640094130110047826632745)
  ·
    refine ⟨62730070597582535869974559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83640094130110047826632745 62730070597582535869974559)
    ·
      refine ⟨94095105896373803804961839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62730070597582535869974559 94095105896373803804961839)
      ·
        refine ⟨141142658844560705707442759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94095105896373803804961839 141142658844560705707442759)
        ·
          refine ⟨211713988266841058561164139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141142658844560705707442759 211713988266841058561164139)
          ·
            refine ⟨317570982400261587841746209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211713988266841058561164139 317570982400261587841746209)
            ·
              refine ⟨238178236800196190881309657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317570982400261587841746209 238178236800196190881309657)
              ·
                refine ⟨178633677600147143160982243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238178236800196190881309657 178633677600147143160982243)
                ·
                  refine ⟨267950516400220714741473365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178633677600147143160982243 267950516400220714741473365)
                  ·
                    refine ⟨3140045114065086500876641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 267950516400220714741473365 3140045114065086500876641)
                    ·
                      refine ⟨2355033835548814875657481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140045114065086500876641 2355033835548814875657481)
                      ·
                        rfl

theorem cell23_4586412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_4586412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586412 prefixEnd_4586412 := by exact prefixLift 4586412
  have htrace : WordTrace (prefixWord ++ tailWord_4586412) baseStart_4586412 baseEnd_4586412 := by
    simpa [prefixWord, tailWord_4586412, baseEnd_4586412] using wordTrace_append hprefix tailTrace_4586412
  have hstable : (prefixWord ++ tailWord_4586412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586412).length < 2 ^ (prefixWord ++ tailWord_4586412).sum := by decide
  have hdescent : baseEnd_4586412 < baseStart_4586412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586432 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_4586432 : Nat := 118140960795 + 4586432 * 2 ^ 59
def prefixEnd_4586432 : Nat := 4983230072969 + 3 ^ 40 * 4586432 * 2
def baseEnd_4586432 : Nat := 2355044105161904797407389

theorem tailTrace_4586432 : CollatzResearch.WordTrace tailWord_4586432 prefixEnd_4586432 2355044105161904797407389 := by
  unfold tailWord_4586432
  simp only [CollatzResearch.WordTrace]
  refine ⟨83640458860073819534496775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111520611813431759379329033 83640458860073819534496775)
  ·
    refine ⟨125460688290110729301745163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83640458860073819534496775 125460688290110729301745163)
    ·
      refine ⟨188191032435166093952617745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125460688290110729301745163 188191032435166093952617745)
      ·
        refine ⟨141143274326374570464463309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188191032435166093952617745 141143274326374570464463309)
        ·
          refine ⟨52928727872390463924173741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141143274326374570464463309 52928727872390463924173741)
          ·
            refine ⟨19848272952146423971565153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52928727872390463924173741 19848272952146423971565153)
            ·
              refine ⟨14886204714109817978673865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19848272952146423971565153 14886204714109817978673865)
              ·
                refine ⟨11164653535582363484005399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14886204714109817978673865 11164653535582363484005399)
                ·
                  refine ⟨16746980303373545226008099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11164653535582363484005399 16746980303373545226008099)
                  ·
                    refine ⟨25120470455060317839012149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16746980303373545226008099 25120470455060317839012149)
                    ·
                      refine ⟨2355044105161904797407389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25120470455060317839012149 2355044105161904797407389)
                      ·
                        rfl

theorem cell23_4586432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_4586432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586432 prefixEnd_4586432 := by exact prefixLift 4586432
  have htrace : WordTrace (prefixWord ++ tailWord_4586432) baseStart_4586432 baseEnd_4586432 := by
    simpa [prefixWord, tailWord_4586432, baseEnd_4586432] using wordTrace_append hprefix tailTrace_4586432
  have hstable : (prefixWord ++ tailWord_4586432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586432).length < 2 ^ (prefixWord ++ tailWord_4586432).sum := by decide
  have hdescent : baseEnd_4586432 < baseStart_4586432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586442 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_4586442 : Nat := 118140960795 + 4586442 * 2 ^ 59
def prefixEnd_4586442 : Nat := 4983230072969 + 3 ^ 40 * 4586442 * 2
def baseEnd_4586442 : Nat := 2355049239968449758282343

theorem tailTrace_4586442 : CollatzResearch.WordTrace tailWord_4586442 prefixEnd_4586442 2355049239968449758282343 := by
  unfold tailWord_4586442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41820320612527852694214395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111520854966740940517905053 41820320612527852694214395)
  ·
    refine ⟨62730480918791779041321593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41820320612527852694214395 62730480918791779041321593)
    ·
      refine ⟨47047860689093834280991195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62730480918791779041321593 47047860689093834280991195)
      ·
        refine ⟨70571791033640751421486793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47047860689093834280991195 70571791033640751421486793)
        ·
          refine ⟨52928843275230563566115095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70571791033640751421486793 52928843275230563566115095)
          ·
            refine ⟨79393264912845845349172643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52928843275230563566115095 79393264912845845349172643)
            ·
              refine ⟨119089897369268768023758965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79393264912845845349172643 119089897369268768023758965)
              ·
                refine ⟨11164677878368947002227403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119089897369268768023758965 11164677878368947002227403)
                ·
                  refine ⟨16747016817553420503341105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11164677878368947002227403 16747016817553420503341105)
                  ·
                    refine ⟨12560262613165065377505829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16747016817553420503341105 12560262613165065377505829)
                    ·
                      refine ⟨2355049239968449758282343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12560262613165065377505829 2355049239968449758282343)
                      ·
                        rfl

theorem cell23_4586442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_4586442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586442 prefixEnd_4586442 := by exact prefixLift 4586442
  have htrace : WordTrace (prefixWord ++ tailWord_4586442) baseStart_4586442 baseEnd_4586442 := by
    simpa [prefixWord, tailWord_4586442, baseEnd_4586442] using wordTrace_append hprefix tailTrace_4586442
  have hstable : (prefixWord ++ tailWord_4586442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586442).length < 2 ^ (prefixWord ++ tailWord_4586442).sum := by decide
  have hdescent : baseEnd_4586442 < baseStart_4586442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586446 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_4586446 : Nat := 118140960795 + 4586446 * 2 ^ 59
def prefixEnd_4586446 : Nat := 4983230072969 + 3 ^ 40 * 4586446 * 2
def baseEnd_4586446 : Nat := 2355051293891067742632325

theorem tailTrace_4586446 : CollatzResearch.WordTrace tailWord_4586446 prefixEnd_4586446 2355051293891067742632325 := by
  unfold tailWord_4586446
  simp only [CollatzResearch.WordTrace]
  refine ⟨20910178542762114932500399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111520952228064612973335461 20910178542762114932500399)
  ·
    refine ⟨31365267814143172398750599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20910178542762114932500399 31365267814143172398750599)
    ·
      refine ⟨47047901721214758598125899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31365267814143172398750599 47047901721214758598125899)
      ·
        refine ⟨70571852581822137897188849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47047901721214758598125899 70571852581822137897188849)
        ·
          refine ⟨52928889436366603422891637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70571852581822137897188849 52928889436366603422891637)
          ·
            refine ⟨4962083384659369070896091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52928889436366603422891637 4962083384659369070896091)
            ·
              refine ⟨7443125076989053606344137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962083384659369070896091 7443125076989053606344137)
              ·
                refine ⟨5582343807741790204758103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7443125076989053606344137 5582343807741790204758103)
                ·
                  refine ⟨8373515711612685307137155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5582343807741790204758103 8373515711612685307137155)
                  ·
                    refine ⟨12560273567419027960705733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8373515711612685307137155 12560273567419027960705733)
                    ·
                      refine ⟨2355051293891067742632325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12560273567419027960705733 2355051293891067742632325)
                      ·
                        rfl

theorem cell23_4586446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_4586446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586446 prefixEnd_4586446 := by exact prefixLift 4586446
  have htrace : WordTrace (prefixWord ++ tailWord_4586446) baseStart_4586446 baseEnd_4586446 := by
    simpa [prefixWord, tailWord_4586446, baseEnd_4586446] using wordTrace_append hprefix tailTrace_4586446
  have hstable : (prefixWord ++ tailWord_4586446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586446).length < 2 ^ (prefixWord ++ tailWord_4586446).sum := by decide
  have hdescent : baseEnd_4586446 < baseStart_4586446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586452 : List Nat := [2, 4, 1, 2, 1, 2, 2, 9]
def baseStart_4586452 : Nat := 118140960795 + 4586452 * 2 ^ 59
def prefixEnd_4586452 : Nat := 4983230072969 + 3 ^ 40 * 4586452 * 2
def baseEnd_4586452 : Nat := 87224236102777582191011

theorem tailTrace_4586452 : CollatzResearch.WordTrace tailWord_4586452 prefixEnd_4586452 87224236102777582191011 := by
  unfold tailWord_4586452
  simp only [CollatzResearch.WordTrace]
  refine ⟨83640823590037591242360805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111521098120050121656481073 83640823590037591242360805)
  ·
    refine ⟨15682654423132048357942651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83640823590037591242360805 15682654423132048357942651)
    ·
      refine ⟨23523981634698072536913977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15682654423132048357942651 23523981634698072536913977)
      ·
        refine ⟨17642986226023554402685483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23523981634698072536913977 17642986226023554402685483)
        ·
          refine ⟨26464479339035331604028225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17642986226023554402685483 26464479339035331604028225)
          ·
            refine ⟨19848359504276498703021169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26464479339035331604028225 19848359504276498703021169)
            ·
              refine ⟨14886269628207374027265877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19848359504276498703021169 14886269628207374027265877)
              ·
                refine ⟨87224236102777582191011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14886269628207374027265877 87224236102777582191011)
                ·
                  rfl

theorem cell23_4586452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 9].length) (baseStart_4586452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586452 prefixEnd_4586452 := by exact prefixLift 4586452
  have htrace : WordTrace (prefixWord ++ tailWord_4586452) baseStart_4586452 baseEnd_4586452 := by
    simpa [prefixWord, tailWord_4586452, baseEnd_4586452] using wordTrace_append hprefix tailTrace_4586452
  have hstable : (prefixWord ++ tailWord_4586452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586452).length < 2 ^ (prefixWord ++ tailWord_4586452).sum := by decide
  have hdescent : baseEnd_4586452 < baseStart_4586452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586466 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4586466 : Nat := 118140960795 + 4586466 * 2 ^ 59
def prefixEnd_4586466 : Nat := 4983230072969 + 3 ^ 40 * 4586466 * 2
def baseEnd_4586466 : Nat := 2355061563504157664382233

theorem tailTrace_4586466 : CollatzResearch.WordTrace tailWord_4586466 prefixEnd_4586466 2355061563504157664382233 := by
  unfold tailWord_4586466
  simp only [CollatzResearch.WordTrace]
  refine ⟨41820539450506115718932813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111521438534682975250487501 41820539450506115718932813)
  ·
    refine ⟨15682702293939793394599805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41820539450506115718932813 15682702293939793394599805)
    ·
      refine ⟨5881013360227422522974927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15682702293939793394599805 5881013360227422522974927)
      ·
        refine ⟨8821520040341133784462391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5881013360227422522974927 8821520040341133784462391)
        ·
          refine ⟨13232280060511700676693587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8821520040341133784462391 13232280060511700676693587)
          ·
            refine ⟨19848420090767551015040381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13232280060511700676693587 19848420090767551015040381)
            ·
              refine ⟨7443157534037831630640143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19848420090767551015040381 7443157534037831630640143)
              ·
                refine ⟨11164736301056747445960215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7443157534037831630640143 11164736301056747445960215)
                ·
                  refine ⟨16747104451585121168940323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11164736301056747445960215 16747104451585121168940323)
                  ·
                    refine ⟨25120656677377681753410485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16747104451585121168940323 25120656677377681753410485)
                    ·
                      refine ⟨2355061563504157664382233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25120656677377681753410485 2355061563504157664382233)
                      ·
                        rfl

theorem cell23_4586466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4586466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586466 prefixEnd_4586466 := by exact prefixLift 4586466
  have htrace : WordTrace (prefixWord ++ tailWord_4586466) baseStart_4586466 baseEnd_4586466 := by
    simpa [prefixWord, tailWord_4586466, baseEnd_4586466] using wordTrace_append hprefix tailTrace_4586466
  have hstable : (prefixWord ++ tailWord_4586466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586466).length < 2 ^ (prefixWord ++ tailWord_4586466).sum := by decide
  have hdescent : baseEnd_4586466 < baseStart_4586466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586469 : List Nat := [1, 3, 1, 6, 2, 10]
def baseStart_4586469 : Nat := 118140960795 + 4586469 * 2 ^ 59
def prefixEnd_4586469 : Nat := 4983230072969 + 3 ^ 40 * 4586469 * 2
def baseEnd_4586469 : Nat := 9691617711712432726933

theorem tailTrace_4586469 : CollatzResearch.WordTrace tailWord_4586469 prefixEnd_4586469 9691617711712432726933 := by
  unfold tailWord_4586469
  simp only [CollatzResearch.WordTrace]
  refine ⟨167282267221013594388090461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111521511480675729592060307 167282267221013594388090461)
  ·
    refine ⟨62730850207880097895533923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167282267221013594388090461 62730850207880097895533923)
    ·
      refine ⟨94096275311820146843300885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62730850207880097895533923 94096275311820146843300885)
      ·
        refine ⟨4410762905241569383279729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94096275311820146843300885 4410762905241569383279729)
        ·
          refine ⟨3308072178931177037459797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4410762905241569383279729 3308072178931177037459797)
          ·
            refine ⟨9691617711712432726933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3308072178931177037459797 9691617711712432726933)
            ·
              rfl

theorem cell23_4586469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 10].length) (baseStart_4586469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586469 prefixEnd_4586469 := by exact prefixLift 4586469
  have htrace : WordTrace (prefixWord ++ tailWord_4586469) baseStart_4586469 baseEnd_4586469 := by
    simpa [prefixWord, tailWord_4586469, baseEnd_4586469] using wordTrace_append hprefix tailTrace_4586469
  have hstable : (prefixWord ++ tailWord_4586469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586469).length < 2 ^ (prefixWord ++ tailWord_4586469).sum := by decide
  have hdescent : baseEnd_4586469 < baseStart_4586469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586475 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 7]
def baseStart_4586475 : Nat := 118140960795 + 4586475 * 2 ^ 59
def prefixEnd_4586475 : Nat := 4983230072969 + 3 ^ 40 * 4586475 * 2
def baseEnd_4586475 : Nat := 2355066184830048129169691

theorem tailTrace_4586475 : CollatzResearch.WordTrace tailWord_4586475 prefixEnd_4586475 2355066184830048129169691 := by
  unfold tailWord_4586475
  simp only [CollatzResearch.WordTrace]
  refine ⟨167282486058991857412808879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111521657372661238275205919 167282486058991857412808879)
  ·
    refine ⟨250923729088487786119213319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167282486058991857412808879 250923729088487786119213319)
    ·
      refine ⟨376385593632731679178819979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250923729088487786119213319 376385593632731679178819979)
      ·
        refine ⟨564578390449097518768229969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376385593632731679178819979 564578390449097518768229969)
        ·
          refine ⟨423433792836823139076172477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564578390449097518768229969 423433792836823139076172477)
          ·
            refine ⟨158787672313808677153564679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423433792836823139076172477 158787672313808677153564679)
            ·
              refine ⟨238181508470713015730347019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158787672313808677153564679 238181508470713015730347019)
              ·
                refine ⟨357272262706069523595520529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238181508470713015730347019 357272262706069523595520529)
                ·
                  refine ⟨267954197029552142696640397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357272262706069523595520529 267954197029552142696640397)
                  ·
                    refine ⟨100482823886082053511240149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 267954197029552142696640397 100482823886082053511240149)
                    ·
                      refine ⟨2355066184830048129169691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100482823886082053511240149 2355066184830048129169691)
                      ·
                        rfl

theorem cell23_4586475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_4586475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586475 prefixEnd_4586475 := by exact prefixLift 4586475
  have htrace : WordTrace (prefixWord ++ tailWord_4586475) baseStart_4586475 baseEnd_4586475 := by
    simpa [prefixWord, tailWord_4586475, baseEnd_4586475] using wordTrace_append hprefix tailTrace_4586475
  have hstable : (prefixWord ++ tailWord_4586475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586475).length < 2 ^ (prefixWord ++ tailWord_4586475).sum := by decide
  have hdescent : baseEnd_4586475 < baseStart_4586475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586489 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 5, 3, 2]
def baseStart_4586489 : Nat := 118140960795 + 4586489 * 2 ^ 59
def prefixEnd_4586489 : Nat := 4983230072969 + 3 ^ 40 * 4586489 * 2
def baseEnd_4586489 : Nat := 2355073373559211074394627

theorem tailTrace_4586489 : CollatzResearch.WordTrace tailWord_4586489 prefixEnd_4586489 2355073373559211074394627 := by
  unfold tailWord_4586489
  simp only [CollatzResearch.WordTrace]
  refine ⟨167282996680941137803818521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111521997787294091869212347 167282996680941137803818521)
  ·
    refine ⟨125462247510705853352863891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167282996680941137803818521 125462247510705853352863891)
    ·
      refine ⟨188193371266058780029295837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125462247510705853352863891 188193371266058780029295837)
      ·
        refine ⟨70572514224772042510985939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188193371266058780029295837 70572514224772042510985939)
        ·
          refine ⟨105858771337158063766478909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70572514224772042510985939 105858771337158063766478909)
          ·
            refine ⟨39697039251434273912429591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105858771337158063766478909 39697039251434273912429591)
            ·
              refine ⟨59545558877151410868644387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39697039251434273912429591 59545558877151410868644387)
              ·
                refine ⟨89318338315727116302966581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59545558877151410868644387 89318338315727116302966581)
                ·
                  refine ⟨8373594217099417153403117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89318338315727116302966581 8373594217099417153403117)
                  ·
                    refine ⟨3140097831412281432526169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8373594217099417153403117 3140097831412281432526169)
                    ·
                      refine ⟨2355073373559211074394627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140097831412281432526169 2355073373559211074394627)
                      ·
                        rfl

theorem cell23_4586489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_4586489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586489 prefixEnd_4586489 := by exact prefixLift 4586489
  have htrace : WordTrace (prefixWord ++ tailWord_4586489) baseStart_4586489 baseEnd_4586489 := by
    simpa [prefixWord, tailWord_4586489, baseEnd_4586489] using wordTrace_append hprefix tailTrace_4586489
  have hstable : (prefixWord ++ tailWord_4586489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586489).length < 2 ^ (prefixWord ++ tailWord_4586489).sum := by decide
  have hdescent : baseEnd_4586489 < baseStart_4586489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586506 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_4586506 : Nat := 118140960795 + 4586506 * 2 ^ 59
def prefixEnd_4586506 : Nat := 4983230072969 + 3 ^ 40 * 4586506 * 2
def baseEnd_4586506 : Nat := 2355082102730337507882049

theorem tailTrace_4586506 : CollatzResearch.WordTrace tailWord_4586506 prefixEnd_4586506 2355082102730337507882049 := by
  unfold tailWord_4586506
  simp only [CollatzResearch.WordTrace]
  refine ⟨41820904180469887426796843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111522411147919699804791581 41820904180469887426796843)
  ·
    refine ⟨62731356270704831140195265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41820904180469887426796843 62731356270704831140195265)
    ·
      refine ⟨47048517203028623355146449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62731356270704831140195265 47048517203028623355146449)
      ·
        refine ⟨35286387902271467516359837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47048517203028623355146449 35286387902271467516359837)
        ·
          refine ⟨13232395463351800318634939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35286387902271467516359837 13232395463351800318634939)
          ·
            refine ⟨19848593195027700477952409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13232395463351800318634939 19848593195027700477952409)
            ·
              refine ⟨14886444896270775358464307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19848593195027700477952409 14886444896270775358464307)
              ·
                refine ⟨22329667344406163037696461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14886444896270775358464307 22329667344406163037696461)
                ·
                  refine ⟨8373625254152311139136173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22329667344406163037696461 8373625254152311139136173)
                  ·
                    refine ⟨3140109470307116677176065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8373625254152311139136173 3140109470307116677176065)
                    ·
                      refine ⟨2355082102730337507882049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140109470307116677176065 2355082102730337507882049)
                      ·
                        rfl

theorem cell23_4586506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_4586506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586506 prefixEnd_4586506 := by exact prefixLift 4586506
  have htrace : WordTrace (prefixWord ++ tailWord_4586506) baseStart_4586506 baseEnd_4586506 := by
    simpa [prefixWord, tailWord_4586506, baseEnd_4586506] using wordTrace_append hprefix tailTrace_4586506
  have hstable : (prefixWord ++ tailWord_4586506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586506).length < 2 ^ (prefixWord ++ tailWord_4586506).sum := by decide
  have hdescent : baseEnd_4586506 < baseStart_4586506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586514 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4586514 : Nat := 118140960795 + 4586514 * 2 ^ 59
def prefixEnd_4586514 : Nat := 4983230072969 + 3 ^ 40 * 4586514 * 2
def baseEnd_4586514 : Nat := 2355086210575573476582013

theorem tailTrace_4586514 : CollatzResearch.WordTrace tailWord_4586514 prefixEnd_4586514 2355086210575573476582013 := by
  unfold tailWord_4586514
  simp only [CollatzResearch.WordTrace]
  refine ⟨41820977126462641768369649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111522605670567044715652397 41820977126462641768369649)
  ·
    refine ⟨31365732844846981326277237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41820977126462641768369649 31365732844846981326277237)
    ·
      refine ⟨2940537454204404499338491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31365732844846981326277237 2940537454204404499338491)
      ·
        refine ⟨4410806181306606749007737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940537454204404499338491 4410806181306606749007737)
        ·
          refine ⟨3308104635979955061755803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4410806181306606749007737 3308104635979955061755803)
          ·
            refine ⟨4962156953969932592633705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308104635979955061755803 4962156953969932592633705)
            ·
              refine ⟨3721617715477449444475279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4962156953969932592633705 3721617715477449444475279)
              ·
                refine ⟨5582426573216174166712919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3721617715477449444475279 5582426573216174166712919)
                ·
                  refine ⟨8373639859824261250069379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5582426573216174166712919 8373639859824261250069379)
                  ·
                    refine ⟨12560459789736391875104069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8373639859824261250069379 12560459789736391875104069)
                    ·
                      refine ⟨2355086210575573476582013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12560459789736391875104069 2355086210575573476582013)
                      ·
                        rfl

theorem cell23_4586514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4586514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586514 prefixEnd_4586514 := by exact prefixLift 4586514
  have htrace : WordTrace (prefixWord ++ tailWord_4586514) baseStart_4586514 baseEnd_4586514 := by
    simpa [prefixWord, tailWord_4586514, baseEnd_4586514] using wordTrace_append hprefix tailTrace_4586514
  have hstable : (prefixWord ++ tailWord_4586514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586514).length < 2 ^ (prefixWord ++ tailWord_4586514).sum := by decide
  have hdescent : baseEnd_4586514 < baseStart_4586514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586522 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_4586522 : Nat := 118140960795 + 4586522 * 2 ^ 59
def prefixEnd_4586522 : Nat := 4983230072969 + 3 ^ 40 * 4586522 * 2
def baseEnd_4586522 : Nat := 2355090318420809445281975

theorem tailTrace_4586522 : CollatzResearch.WordTrace tailWord_4586522 prefixEnd_4586522 2355090318420809445281975 := by
  unfold tailWord_4586522
  simp only [CollatzResearch.WordTrace]
  refine ⟨41821050072455396109942455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111522800193214389626513213 41821050072455396109942455)
  ·
    refine ⟨62731575108683094164913683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41821050072455396109942455 62731575108683094164913683)
    ·
      refine ⟨94097362663024641247370525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62731575108683094164913683 94097362663024641247370525)
      ·
        refine ⟨35286510998634240467763947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94097362663024641247370525 35286510998634240467763947)
        ·
          refine ⟨52929766497951360701645921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35286510998634240467763947 52929766497951360701645921)
          ·
            refine ⟨39697324873463520526234441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52929766497951360701645921 39697324873463520526234441)
            ·
              refine ⟨29772993655097640394675831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39697324873463520526234441 29772993655097640394675831)
              ·
                refine ⟨44659490482646460592013747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29772993655097640394675831 44659490482646460592013747)
                ·
                  refine ⟨66989235723969690888020621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44659490482646460592013747 66989235723969690888020621)
                  ·
                    refine ⟨25120963396488634083007733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66989235723969690888020621 25120963396488634083007733)
                    ·
                      refine ⟨2355090318420809445281975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25120963396488634083007733 2355090318420809445281975)
                      ·
                        rfl

theorem cell23_4586522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_4586522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586522 prefixEnd_4586522 := by exact prefixLift 4586522
  have htrace : WordTrace (prefixWord ++ tailWord_4586522) baseStart_4586522 baseEnd_4586522 := by
    simpa [prefixWord, tailWord_4586522, baseEnd_4586522] using wordTrace_append hprefix tailTrace_4586522
  have hstable : (prefixWord ++ tailWord_4586522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586522).length < 2 ^ (prefixWord ++ tailWord_4586522).sum := by decide
  have hdescent : baseEnd_4586522 < baseStart_4586522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586553 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 1, 4, 2]
def baseStart_4586553 : Nat := 118140960795 + 4586553 * 2 ^ 59
def prefixEnd_4586553 : Nat := 4983230072969 + 3 ^ 40 * 4586553 * 2
def baseEnd_4586553 : Nat := 2355106236321098823994333

theorem tailTrace_4586553 : CollatzResearch.WordTrace tailWord_4586553 prefixEnd_4586553 2355106236321098823994333 := by
  unfold tailWord_4586553
  simp only [CollatzResearch.WordTrace]
  refine ⟨167285330952709276734148313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111523553968472851156098875 167285330952709276734148313)
  ·
    refine ⟨125463998214531957550611235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167285330952709276734148313 125463998214531957550611235)
    ·
      refine ⟨188195997321797936325916853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125463998214531957550611235 188195997321797936325916853)
      ·
        refine ⟨17643374748918556530554705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188195997321797936325916853 17643374748918556530554705)
        ·
          refine ⟨13232531061688917397916029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17643374748918556530554705 13232531061688917397916029)
          ·
            refine ⟨4962199148133344024218511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13232531061688917397916029 4962199148133344024218511)
            ·
              refine ⟨7443298722200016036327767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962199148133344024218511 7443298722200016036327767)
              ·
                refine ⟨11164948083300024054491651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7443298722200016036327767 11164948083300024054491651)
                ·
                  refine ⟨16747422124950036081737477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11164948083300024054491651 16747422124950036081737477)
                  ·
                    refine ⟨3140141648428131765325777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16747422124950036081737477 3140141648428131765325777)
                    ·
                      refine ⟨2355106236321098823994333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140141648428131765325777 2355106236321098823994333)
                      ·
                        rfl

theorem cell23_4586553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_4586553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586553 prefixEnd_4586553 := by exact prefixLift 4586553
  have htrace : WordTrace (prefixWord ++ tailWord_4586553) baseStart_4586553 baseEnd_4586553 := by
    simpa [prefixWord, tailWord_4586553, baseEnd_4586553] using wordTrace_append hprefix tailTrace_4586553
  have hstable : (prefixWord ++ tailWord_4586553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586553).length < 2 ^ (prefixWord ++ tailWord_4586553).sum := by decide
  have hdescent : baseEnd_4586553 < baseStart_4586553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586599 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_4586599 : Nat := 118140960795 + 4586599 * 2 ^ 59
def prefixEnd_4586599 : Nat := 4983230072969 + 3 ^ 40 * 4586599 * 2
def baseEnd_4586599 : Nat := 2355129856431205644019121

theorem tailTrace_4586599 : CollatzResearch.WordTrace tailWord_4586599 prefixEnd_4586599 2355129856431205644019121 := by
  unfold tailWord_4586599
  simp only [CollatzResearch.WordTrace]
  refine ⟨167287008710542626590322851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111524672473695084393548567 167287008710542626590322851)
  ·
    refine ⟨250930513065813939885484277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167287008710542626590322851 250930513065813939885484277)
    ·
      refine ⟨23524735599920056864264151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250930513065813939885484277 23524735599920056864264151)
      ·
        refine ⟨35287103399880085296396227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23524735599920056864264151 35287103399880085296396227)
        ·
          refine ⟨52930655099820127944594341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35287103399880085296396227 52930655099820127944594341)
          ·
            refine ⟨9924497831216273989611439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52930655099820127944594341 9924497831216273989611439)
            ·
              refine ⟨14886746746824410984417159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9924497831216273989611439 14886746746824410984417159)
              ·
                refine ⟨22330120120236616476625739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14886746746824410984417159 22330120120236616476625739)
                ·
                  refine ⟨33495180180354924714938609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22330120120236616476625739 33495180180354924714938609)
                  ·
                    refine ⟨25121385135266193536203957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33495180180354924714938609 25121385135266193536203957)
                    ·
                      refine ⟨2355129856431205644019121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25121385135266193536203957 2355129856431205644019121)
                      ·
                        rfl

theorem cell23_4586599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_4586599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586599 prefixEnd_4586599 := by exact prefixLift 4586599
  have htrace : WordTrace (prefixWord ++ tailWord_4586599) baseStart_4586599 baseEnd_4586599 := by
    simpa [prefixWord, tailWord_4586599, baseEnd_4586599] using wordTrace_append hprefix tailTrace_4586599
  have hstable : (prefixWord ++ tailWord_4586599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586599).length < 2 ^ (prefixWord ++ tailWord_4586599).sum := by decide
  have hdescent : baseEnd_4586599 < baseStart_4586599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586619 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 3, 4]
def baseStart_4586619 : Nat := 118140960795 + 4586619 * 2 ^ 59
def prefixEnd_4586619 : Nat := 4983230072969 + 3 ^ 40 * 4586619 * 2
def baseEnd_4586619 : Nat := 785046708681431855256343

theorem tailTrace_4586619 : CollatzResearch.WordTrace tailWord_4586619 prefixEnd_4586619 785046708681431855256343 := by
  unfold tailWord_4586619
  simp only [CollatzResearch.WordTrace]
  refine ⟨167287738170470170006050911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111525158780313446670700607 167287738170470170006050911)
  ·
    refine ⟨250931607255705255009076367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167287738170470170006050911 250931607255705255009076367)
    ·
      refine ⟨376397410883557882513614551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250931607255705255009076367 376397410883557882513614551)
      ·
        refine ⟨564596116325336823770421827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376397410883557882513614551 564596116325336823770421827)
        ·
          refine ⟨846894174488005235655632741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564596116325336823770421827 846894174488005235655632741)
          ·
            refine ⟨158792657716500981685431139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 846894174488005235655632741 158792657716500981685431139)
            ·
              refine ⟨238188986574751472528146709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158792657716500981685431139 238188986574751472528146709)
              ·
                refine ⟨11165108745691475274756877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 238188986574751472528146709 11165108745691475274756877)
                ·
                  refine ⟨4186915779634303228033829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11165108745691475274756877 4186915779634303228033829)
                  ·
                    refine ⟨785046708681431855256343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4186915779634303228033829 785046708681431855256343)
                    ·
                      rfl

theorem cell23_4586619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 4].length) (baseStart_4586619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586619 prefixEnd_4586619 := by exact prefixLift 4586619
  have htrace : WordTrace (prefixWord ++ tailWord_4586619) baseStart_4586619 baseEnd_4586619 := by
    simpa [prefixWord, tailWord_4586619, baseEnd_4586619] using wordTrace_append hprefix tailTrace_4586619
  have hstable : (prefixWord ++ tailWord_4586619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586619).length < 2 ^ (prefixWord ++ tailWord_4586619).sum := by decide
  have hdescent : baseEnd_4586619 < baseStart_4586619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586653 : List Nat := [1, 4, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_4586653 : Nat := 118140960795 + 4586653 * 2 ^ 59
def prefixEnd_4586653 : Nat := 4983230072969 + 3 ^ 40 * 4586653 * 2
def baseEnd_4586653 : Nat := 785052528128849477581291

theorem tailTrace_4586653 : CollatzResearch.WordTrace tailWord_4586653 prefixEnd_4586653 785052528128849477581291 := by
  unfold tailWord_4586653
  simp only [CollatzResearch.WordTrace]
  refine ⟨167288978252346993812788613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111525985501564662541859075 167288978252346993812788613)
  ·
    refine ⟨31366683422315061339897865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167288978252346993812788613 31366683422315061339897865)
    ·
      refine ⟨23525012566736296004923399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31366683422315061339897865 23525012566736296004923399)
      ·
        refine ⟨35287518850104444007385099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23525012566736296004923399 35287518850104444007385099)
        ·
          refine ⟨52931278275156666011077649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35287518850104444007385099 52931278275156666011077649)
          ·
            refine ⟨39698458706367499508308237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52931278275156666011077649 39698458706367499508308237)
            ·
              refine ⟨14886922014887812315615589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39698458706367499508308237 14886922014887812315615589)
              ·
                refine ⟨2791297877791464809177923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14886922014887812315615589 2791297877791464809177923)
                ·
                  refine ⟨4186946816687197213766885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791297877791464809177923 4186946816687197213766885)
                  ·
                    refine ⟨785052528128849477581291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4186946816687197213766885 785052528128849477581291)
                    ·
                      rfl

theorem cell23_4586653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_4586653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586653 prefixEnd_4586653 := by exact prefixLift 4586653
  have htrace : WordTrace (prefixWord ++ tailWord_4586653) baseStart_4586653 baseEnd_4586653 := by
    simpa [prefixWord, tailWord_4586653, baseEnd_4586653] using wordTrace_append hprefix tailTrace_4586653
  have hstable : (prefixWord ++ tailWord_4586653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586653).length < 2 ^ (prefixWord ++ tailWord_4586653).sum := by decide
  have hdescent : baseEnd_4586653 < baseStart_4586653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586679 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 3, 5]
def baseStart_4586679 : Nat := 118140960795 + 4586679 * 2 ^ 59
def prefixEnd_4586679 : Nat := 4983230072969 + 3 ^ 40 * 4586679 * 2
def baseEnd_4586679 : Nat := 785056978294521777006251

theorem tailTrace_4586679 : CollatzResearch.WordTrace tailWord_4586679 prefixEnd_4586679 785056978294521777006251 := by
  unfold tailWord_4586679
  simp only [CollatzResearch.WordTrace]
  refine ⟨167289926550252800253235091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111526617700168533502156727 167289926550252800253235091)
  ·
    refine ⟨250934889825379200379852637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167289926550252800253235091 250934889825379200379852637)
    ·
      refine ⟨94100583684517200142444739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250934889825379200379852637 94100583684517200142444739)
      ·
        refine ⟨141150875526775800213667109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94100583684517200142444739 141150875526775800213667109)
        ·
          refine ⟨26465789161270462540062583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141150875526775800213667109 26465789161270462540062583)
          ·
            refine ⟨39698683741905693810093875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26465789161270462540062583 39698683741905693810093875)
            ·
              refine ⟨59548025612858540715140813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39698683741905693810093875 59548025612858540715140813)
              ·
                refine ⟨22330509604821952768177805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59548025612858540715140813 22330509604821952768177805)
                ·
                  refine ⟨8373941101808232288066677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22330509604821952768177805 8373941101808232288066677)
                  ·
                    refine ⟨785056978294521777006251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8373941101808232288066677 785056978294521777006251)
                    ·
                      rfl

theorem cell23_4586679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_4586679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586679 prefixEnd_4586679 := by exact prefixLift 4586679
  have htrace : WordTrace (prefixWord ++ tailWord_4586679) baseStart_4586679 baseEnd_4586679 := by
    simpa [prefixWord, tailWord_4586679, baseEnd_4586679] using wordTrace_append hprefix tailTrace_4586679
  have hstable : (prefixWord ++ tailWord_4586679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586679).length < 2 ^ (prefixWord ++ tailWord_4586679).sum := by decide
  have hdescent : baseEnd_4586679 < baseStart_4586679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586699 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 4]
def baseStart_4586699 : Nat := 118140960795 + 4586699 * 2 ^ 59
def prefixEnd_4586699 : Nat := 4983230072969 + 3 ^ 40 * 4586699 * 2
def baseEnd_4586699 : Nat := 2355181204496655252768661

theorem tailTrace_4586699 : CollatzResearch.WordTrace tailWord_4586699 prefixEnd_4586699 2355181204496655252768661 := by
  unfold tailWord_4586699
  simp only [CollatzResearch.WordTrace]
  refine ⟨167290656010180343668963151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111527104006786895779308767 167290656010180343668963151)
  ·
    refine ⟨250935984015270515503444727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167290656010180343668963151 250935984015270515503444727)
    ·
      refine ⟨376403976022905773255167091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250935984015270515503444727 376403976022905773255167091)
      ·
        refine ⟨564605964034358659882750637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376403976022905773255167091 564605964034358659882750637)
        ·
          refine ⟨211727236512884497456031489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 564605964034358659882750637 211727236512884497456031489)
          ·
            refine ⟨158795427384663373092023617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211727236512884497456031489 158795427384663373092023617)
            ·
              refine ⟨119096570538497529819017713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158795427384663373092023617 119096570538497529819017713)
              ·
                refine ⟨89322427903873147364263285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119096570538497529819017713 89322427903873147364263285)
                ·
                  refine ⟨8373977615988107565399683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89322427903873147364263285 8373977615988107565399683)
                  ·
                    refine ⟨12560966423982161348099525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8373977615988107565399683 12560966423982161348099525)
                    ·
                      refine ⟨2355181204496655252768661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12560966423982161348099525 2355181204496655252768661)
                      ·
                        rfl

theorem cell23_4586699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 4].length) (baseStart_4586699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586699 prefixEnd_4586699 := by exact prefixLift 4586699
  have htrace : WordTrace (prefixWord ++ tailWord_4586699) baseStart_4586699 baseEnd_4586699 := by
    simpa [prefixWord, tailWord_4586699, baseEnd_4586699] using wordTrace_append hprefix tailTrace_4586699
  have hstable : (prefixWord ++ tailWord_4586699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586699).length < 2 ^ (prefixWord ++ tailWord_4586699).sum := by decide
  have hdescent : baseEnd_4586699 < baseStart_4586699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586719 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_4586719 : Nat := 118140960795 + 4586719 * 2 ^ 59
def prefixEnd_4586719 : Nat := 4983230072969 + 3 ^ 40 * 4586719 * 2
def baseEnd_4586719 : Nat := 2355191474109745174518569

theorem tailTrace_4586719 : CollatzResearch.WordTrace tailWord_4586719 prefixEnd_4586719 2355191474109745174518569 := by
  unfold tailWord_4586719
  simp only [CollatzResearch.WordTrace]
  refine ⟨167291385470107887084691211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111527590313405258056460807 167291385470107887084691211)
  ·
    refine ⟨250937078205161830627036817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167291385470107887084691211 250937078205161830627036817)
    ·
      refine ⟨188202808653871372970277613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250937078205161830627036817 188202808653871372970277613)
      ·
        refine ⟨70576053245201764863854105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188202808653871372970277613 70576053245201764863854105)
        ·
          refine ⟨52932039933901323647890579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70576053245201764863854105 52932039933901323647890579)
          ·
            refine ⟨79398059900851985471835869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52932039933901323647890579 79398059900851985471835869)
            ·
              refine ⟨29774272462819494551938451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79398059900851985471835869 29774272462819494551938451)
              ·
                refine ⟨44661408694229241827907677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29774272462819494551938451 44661408694229241827907677)
                ·
                  refine ⟨16748028260335965685465379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44661408694229241827907677 16748028260335965685465379)
                  ·
                    refine ⟨25122042390503948528198069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16748028260335965685465379 25122042390503948528198069)
                    ·
                      refine ⟨2355191474109745174518569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25122042390503948528198069 2355191474109745174518569)
                      ·
                        rfl

theorem cell23_4586719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_4586719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586719 prefixEnd_4586719 := by exact prefixLift 4586719
  have htrace : WordTrace (prefixWord ++ tailWord_4586719) baseStart_4586719 baseEnd_4586719 := by
    simpa [prefixWord, tailWord_4586719, baseEnd_4586719] using wordTrace_append hprefix tailTrace_4586719
  have hstable : (prefixWord ++ tailWord_4586719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586719).length < 2 ^ (prefixWord ++ tailWord_4586719).sum := by decide
  have hdescent : baseEnd_4586719 < baseStart_4586719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586733 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_4586733 : Nat := 118140960795 + 4586733 * 2 ^ 59
def prefixEnd_4586733 : Nat := 4983230072969 + 3 ^ 40 * 4586733 * 2
def baseEnd_4586733 : Nat := 2355198662838908119743505

theorem tailTrace_4586733 : CollatzResearch.WordTrace tailWord_4586733 prefixEnd_4586733 2355198662838908119743505 := by
  unfold tailWord_4586733
  simp only [CollatzResearch.WordTrace]
  refine ⟨167291896092057167475700853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111527930728038111650467235 167291896092057167475700853)
  ·
    refine ⟨15683615258630359450846955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167291896092057167475700853 15683615258630359450846955)
    ·
      refine ⟨23525422887945539176270433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15683615258630359450846955 23525422887945539176270433)
      ·
        refine ⟨17644067165959154382202825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23525422887945539176270433 17644067165959154382202825)
        ·
          refine ⟨13233050374469365786652119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17644067165959154382202825 13233050374469365786652119)
          ·
            refine ⟨19849575561704048679978179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13233050374469365786652119 19849575561704048679978179)
            ·
              refine ⟨29774363342556073019967269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19849575561704048679978179 29774363342556073019967269)
              ·
                refine ⟨5582693126729263691243863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29774363342556073019967269 5582693126729263691243863)
                ·
                  refine ⟨8374039690093895536865795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5582693126729263691243863 8374039690093895536865795)
                  ·
                    refine ⟨12561059535140843305298693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8374039690093895536865795 12561059535140843305298693)
                    ·
                      refine ⟨2355198662838908119743505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12561059535140843305298693 2355198662838908119743505)
                      ·
                        rfl

theorem cell23_4586733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_4586733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586733 prefixEnd_4586733 := by exact prefixLift 4586733
  have htrace : WordTrace (prefixWord ++ tailWord_4586733) baseStart_4586733 baseEnd_4586733 := by
    simpa [prefixWord, tailWord_4586733, baseEnd_4586733] using wordTrace_append hprefix tailTrace_4586733
  have hstable : (prefixWord ++ tailWord_4586733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586733).length < 2 ^ (prefixWord ++ tailWord_4586733).sum := by decide
  have hdescent : baseEnd_4586733 < baseStart_4586733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586739 : List Nat := [1, 1, 1, 2, 2, 6, 1, 9]
def baseStart_4586739 : Nat := 118140960795 + 4586739 * 2 ^ 59
def prefixEnd_4586739 : Nat := 4983230072969 + 3 ^ 40 * 4586739 * 2
def baseEnd_4586739 : Nat := 87229694211956855417351

theorem tailTrace_4586739 : CollatzResearch.WordTrace tailWord_4586739 prefixEnd_4586739 87229694211956855417351 := by
  unfold tailWord_4586739
  simp only [CollatzResearch.WordTrace]
  refine ⟨167292114930035430500419271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111528076620023620333612847 167292114930035430500419271)
  ·
    refine ⟨250938172395053145750628907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167292114930035430500419271 250938172395053145750628907)
    ·
      refine ⟨376407258592579718625943361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250938172395053145750628907 376407258592579718625943361)
      ·
        refine ⟨282305443944434788969457521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376407258592579718625943361 282305443944434788969457521)
        ·
          refine ⟨211729082958326091727093141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282305443944434788969457521 211729082958326091727093141)
          ·
            refine ⟨9924800763671535549707491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211729082958326091727093141 9924800763671535549707491)
            ·
              refine ⟨14887201145507303324561237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9924800763671535549707491 14887201145507303324561237)
              ·
                refine ⟨87229694211956855417351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14887201145507303324561237 87229694211956855417351)
                ·
                  rfl

theorem cell23_4586739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 9].length) (baseStart_4586739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586739 prefixEnd_4586739 := by exact prefixLift 4586739
  have htrace : WordTrace (prefixWord ++ tailWord_4586739) baseStart_4586739 baseEnd_4586739 := by
    simpa [prefixWord, tailWord_4586739, baseEnd_4586739] using wordTrace_append hprefix tailTrace_4586739
  have hstable : (prefixWord ++ tailWord_4586739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586739).length < 2 ^ (prefixWord ++ tailWord_4586739).sum := by decide
  have hdescent : baseEnd_4586739 < baseStart_4586739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586753 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_4586753 : Nat := 118140960795 + 4586753 * 2 ^ 59
def prefixEnd_4586753 : Nat := 4983230072969 + 3 ^ 40 * 4586753 * 2
def baseEnd_4586753 : Nat := 2355208932451998041493413

theorem tailTrace_4586753 : CollatzResearch.WordTrace tailWord_4586753 prefixEnd_4586753 2355208932451998041493413 := by
  unfold tailWord_4586753
  simp only [CollatzResearch.WordTrace]
  refine ⟨167292625551984710891428913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111528417034656473927619275 167292625551984710891428913)
  ·
    refine ⟨125469469163988533168571685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167292625551984710891428913 125469469163988533168571685)
    ·
      refine ⟨23525525468247849969107191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125469469163988533168571685 23525525468247849969107191)
      ·
        refine ⟨35288288202371774953660787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23525525468247849969107191 35288288202371774953660787)
        ·
          refine ⟨52932432303557662430491181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35288288202371774953660787 52932432303557662430491181)
          ·
            refine ⟨19849662113834123411434193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52932432303557662430491181 19849662113834123411434193)
            ·
              refine ⟨14887246585375592558575645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19849662113834123411434193 14887246585375592558575645)
              ·
                refine ⟨5582717469515847209465867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14887246585375592558575645 5582717469515847209465867)
                ·
                  refine ⟨8374076204273770814198801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5582717469515847209465867 8374076204273770814198801)
                  ·
                    refine ⟨6280557153205328110649101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8374076204273770814198801 6280557153205328110649101)
                    ·
                      refine ⟨2355208932451998041493413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6280557153205328110649101 2355208932451998041493413)
                      ·
                        rfl

theorem cell23_4586753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_4586753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586753 prefixEnd_4586753 := by exact prefixLift 4586753
  have htrace : WordTrace (prefixWord ++ tailWord_4586753) baseStart_4586753 baseEnd_4586753 := by
    simpa [prefixWord, tailWord_4586753, baseEnd_4586753] using wordTrace_append hprefix tailTrace_4586753
  have hstable : (prefixWord ++ tailWord_4586753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586753).length < 2 ^ (prefixWord ++ tailWord_4586753).sum := by decide
  have hdescent : baseEnd_4586753 < baseStart_4586753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586756 : List Nat := [2, 3, 2, 2, 2, 3, 9]
def baseStart_4586756 : Nat := 118140960795 + 4586756 * 2 ^ 59
def prefixEnd_4586756 : Nat := 4983230072969 + 3 ^ 40 * 4586756 * 2
def baseEnd_4586756 : Nat := 29076672504863722589579

theorem tailTrace_4586756 : CollatzResearch.WordTrace tailWord_4586756 prefixEnd_4586756 29076672504863722589579 := by
  unfold tailWord_4586756
  simp only [CollatzResearch.WordTrace]
  refine ⟨83646367485486921201894061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111528489980649228269192081 83646367485486921201894061)
  ·
    refine ⟨31367387807057595450710273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83646367485486921201894061 31367387807057595450710273)
    ·
      refine ⟨23525540855293196588032705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31367387807057595450710273 23525540855293196588032705)
      ·
        refine ⟨17644155641469897441024529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23525540855293196588032705 17644155641469897441024529)
        ·
          refine ⟨13233116731102423080768397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17644155641469897441024529 13233116731102423080768397)
          ·
            refine ⟨4962418774163408655288149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13233116731102423080768397 4962418774163408655288149)
            ·
              refine ⟨29076672504863722589579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4962418774163408655288149 29076672504863722589579)
              ·
                rfl

theorem cell23_4586756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 9].length) (baseStart_4586756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586756 prefixEnd_4586756 := by exact prefixLift 4586756
  have htrace : WordTrace (prefixWord ++ tailWord_4586756) baseStart_4586756 baseEnd_4586756 := by
    simpa [prefixWord, tailWord_4586756, baseEnd_4586756] using wordTrace_append hprefix tailTrace_4586756
  have hstable : (prefixWord ++ tailWord_4586756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586756).length < 2 ^ (prefixWord ++ tailWord_4586756).sum := by decide
  have hdescent : baseEnd_4586756 < baseStart_4586756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586769 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 2, 7]
def baseStart_4586769 : Nat := 118140960795 + 4586769 * 2 ^ 59
def prefixEnd_4586769 : Nat := 4983230072969 + 3 ^ 40 * 4586769 * 2
def baseEnd_4586769 : Nat := 785072382714156659631113

theorem tailTrace_4586769 : CollatzResearch.WordTrace tailWord_4586769 prefixEnd_4586769 785072382714156659631113 := by
  unfold tailWord_4586769
  simp only [CollatzResearch.WordTrace]
  refine ⟨167293209119926745624011361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111528806079951163749340907 167293209119926745624011361)
  ·
    refine ⟨125469906839945059218008521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167293209119926745624011361 125469906839945059218008521)
    ·
      refine ⟨94102430129958794413506391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125469906839945059218008521 94102430129958794413506391)
      ·
        refine ⟨141153645194938191620259587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94102430129958794413506391 141153645194938191620259587)
        ·
          refine ⟨211730467792407287430389381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141153645194938191620259587 211730467792407287430389381)
          ·
            refine ⟨39699462711076366393198009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211730467792407287430389381 39699462711076366393198009)
            ·
              refine ⟨29774597033307274794898507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39699462711076366393198009 29774597033307274794898507)
              ·
                refine ⟨44661895549960912192347761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29774597033307274794898507 44661895549960912192347761)
                ·
                  refine ⟨33496421662470684144260821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44661895549960912192347761 33496421662470684144260821)
                  ·
                    refine ⟨785072382714156659631113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33496421662470684144260821 785072382714156659631113)
                    ·
                      rfl

theorem cell23_4586769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_4586769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586769 prefixEnd_4586769 := by exact prefixLift 4586769
  have htrace : WordTrace (prefixWord ++ tailWord_4586769) baseStart_4586769 baseEnd_4586769 := by
    simpa [prefixWord, tailWord_4586769, baseEnd_4586769] using wordTrace_append hprefix tailTrace_4586769
  have hstable : (prefixWord ++ tailWord_4586769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586769).length < 2 ^ (prefixWord ++ tailWord_4586769).sum := by decide
  have hdescent : baseEnd_4586769 < baseStart_4586769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586799 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 4, 6]
def baseStart_4586799 : Nat := 118140960795 + 4586799 * 2 ^ 59
def prefixEnd_4586799 : Nat := 4983230072969 + 3 ^ 40 * 4586799 * 2
def baseEnd_4586799 : Nat := 785077517520701620506067

theorem tailTrace_4586799 : CollatzResearch.WordTrace tailWord_4586799 prefixEnd_4586799 785077517520701620506067 := by
  unfold tailWord_4586799
  simp only [CollatzResearch.WordTrace]
  refine ⟨167294303309818060747603451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111529535539878707165068967 167294303309818060747603451)
  ·
    refine ⟨250941454964727091121405177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167294303309818060747603451 250941454964727091121405177)
    ·
      refine ⟨188206091223545318341053883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250941454964727091121405177 188206091223545318341053883)
      ·
        refine ⟨282309136835317977511580825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188206091223545318341053883 282309136835317977511580825)
        ·
          refine ⟨211731852626488483133685619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282309136835317977511580825 211731852626488483133685619)
          ·
            refine ⟨317597778939732724700528429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211731852626488483133685619 317597778939732724700528429)
            ·
              refine ⟨119099167102399771762698161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317597778939732724700528429 119099167102399771762698161)
              ·
                refine ⟨89324375326799828822023621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119099167102399771762698161 89324375326799828822023621)
                ·
                  refine ⟨16748320373774967904129429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89324375326799828822023621 16748320373774967904129429)
                  ·
                    refine ⟨785077517520701620506067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16748320373774967904129429 785077517520701620506067)
                    ·
                      rfl

theorem cell23_4586799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_4586799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586799 prefixEnd_4586799 := by exact prefixLift 4586799
  have htrace : WordTrace (prefixWord ++ tailWord_4586799) baseStart_4586799 baseEnd_4586799 := by
    simpa [prefixWord, tailWord_4586799, baseEnd_4586799] using wordTrace_append hprefix tailTrace_4586799
  have hstable : (prefixWord ++ tailWord_4586799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586799).length < 2 ^ (prefixWord ++ tailWord_4586799).sum := by decide
  have hdescent : baseEnd_4586799 < baseStart_4586799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586817 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4586817 : Nat := 118140960795 + 4586817 * 2 ^ 59
def prefixEnd_4586817 : Nat := 4983230072969 + 3 ^ 40 * 4586817 * 2
def baseEnd_4586817 : Nat := 2355241795213885791093119

theorem tailTrace_4586817 : CollatzResearch.WordTrace tailWord_4586817 prefixEnd_4586817 2355241795213885791093119 := by
  unfold tailWord_4586817
  simp only [CollatzResearch.WordTrace]
  refine ⟨167294959823752849821758705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111529973215835233214505803 167294959823752849821758705)
  ·
    refine ⟨125471219867814637366319029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167294959823752849821758705 125471219867814637366319029)
    ·
      refine ⟨11762926862607622253092409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125471219867814637366319029 11762926862607622253092409)
      ·
        refine ⟨8822195146955716689819307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11762926862607622253092409 8822195146955716689819307)
        ·
          refine ⟨13233292720433575034728961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8822195146955716689819307 13233292720433575034728961)
          ·
            refine ⟨9924969540325181276046721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13233292720433575034728961 9924969540325181276046721)
            ·
              refine ⟨7443727155243885957035041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9924969540325181276046721 7443727155243885957035041)
              ·
                refine ⟨5582795366432914467776281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7443727155243885957035041 5582795366432914467776281)
                ·
                  refine ⟨4187096524824685850832211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5582795366432914467776281 4187096524824685850832211)
                  ·
                    refine ⟨6280644787237028776248317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4187096524824685850832211 6280644787237028776248317)
                    ·
                      refine ⟨2355241795213885791093119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6280644787237028776248317 2355241795213885791093119)
                      ·
                        rfl

theorem cell23_4586817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4586817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586817 prefixEnd_4586817 := by exact prefixLift 4586817
  have htrace : WordTrace (prefixWord ++ tailWord_4586817) baseStart_4586817 baseEnd_4586817 := by
    simpa [prefixWord, tailWord_4586817, baseEnd_4586817] using wordTrace_append hprefix tailTrace_4586817
  have hstable : (prefixWord ++ tailWord_4586817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586817).length < 2 ^ (prefixWord ++ tailWord_4586817).sum := by decide
  have hdescent : baseEnd_4586817 < baseStart_4586817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586819 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 6]
def baseStart_4586819 : Nat := 118140960795 + 4586819 * 2 ^ 59
def prefixEnd_4586819 : Nat := 4983230072969 + 3 ^ 40 * 4586819 * 2
def baseEnd_4586819 : Nat := 2355242822175194783268109

theorem tailTrace_4586819 : CollatzResearch.WordTrace tailWord_4586819 prefixEnd_4586819 2355242822175194783268109 := by
  unfold tailWord_4586819
  simp only [CollatzResearch.WordTrace]
  refine ⟨167295032769745604163331511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111530021846497069442221007 167295032769745604163331511)
  ·
    refine ⟨250942549154618406244997267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167295032769745604163331511 250942549154618406244997267)
    ·
      refine ⟨376413823731927609367495901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250942549154618406244997267 376413823731927609367495901)
      ·
        refine ⟨141155183899472853512810963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376413823731927609367495901 141155183899472853512810963)
        ·
          refine ⟨211732775849209280269216445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141155183899472853512810963 211732775849209280269216445)
          ·
            refine ⟨79399790943453480100956167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211732775849209280269216445 79399790943453480100956167)
            ·
              refine ⟨119099686415180220151434251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79399790943453480100956167 119099686415180220151434251)
              ·
                refine ⟨178649529622770330227151377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119099686415180220151434251 178649529622770330227151377)
                ·
                  refine ⟨133987147217077747670363533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178649529622770330227151377 133987147217077747670363533)
                  ·
                    refine ⟨50245180206404155376386325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133987147217077747670363533 50245180206404155376386325)
                    ·
                      refine ⟨2355242822175194783268109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50245180206404155376386325 2355242822175194783268109)
                      ·
                        rfl

theorem cell23_4586819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_4586819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586819 prefixEnd_4586819 := by exact prefixLift 4586819
  have htrace : WordTrace (prefixWord ++ tailWord_4586819) baseStart_4586819 baseEnd_4586819 := by
    simpa [prefixWord, tailWord_4586819, baseEnd_4586819] using wordTrace_append hprefix tailTrace_4586819
  have hstable : (prefixWord ++ tailWord_4586819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586819).length < 2 ^ (prefixWord ++ tailWord_4586819).sum := by decide
  have hdescent : baseEnd_4586819 < baseStart_4586819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586840 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 2, 2, 2]
def baseStart_4586840 : Nat := 118140960795 + 4586840 * 2 ^ 59
def prefixEnd_4586840 : Nat := 4983230072969 + 3 ^ 40 * 4586840 * 2
def baseEnd_4586840 : Nat := 2355253605268939201105513

theorem tailTrace_4586840 : CollatzResearch.WordTrace tailWord_4586840 prefixEnd_4586840 2355253605268939201105513 := by
  unfold tailWord_4586840
  simp only [CollatzResearch.WordTrace]
  refine ⟨83647899351334762374922987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111530532468446349833230649 83647899351334762374922987)
  ·
    refine ⟨125471849027002143562384481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83647899351334762374922987 125471849027002143562384481)
    ·
      refine ⟨94103886770251607671788361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125471849027002143562384481 94103886770251607671788361)
      ·
        refine ⟨70577915077688705753841271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94103886770251607671788361 70577915077688705753841271)
        ·
          refine ⟨105866872616533058630761907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70577915077688705753841271 105866872616533058630761907)
          ·
            refine ⟨158800308924799587946142861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105866872616533058630761907 158800308924799587946142861)
            ·
              refine ⟨59550115846799845479803573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158800308924799587946142861 59550115846799845479803573)
              ·
                refine ⟨5582823360637485513731585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59550115846799845479803573 5582823360637485513731585)
                ·
                  refine ⟨4187117520478114135298689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5582823360637485513731585 4187117520478114135298689)
                  ·
                    refine ⟨3140338140358585601474017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4187117520478114135298689 3140338140358585601474017)
                    ·
                      refine ⟨2355253605268939201105513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140338140358585601474017 2355253605268939201105513)
                      ·
                        rfl

theorem cell23_4586840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_4586840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586840 prefixEnd_4586840 := by exact prefixLift 4586840
  have htrace : WordTrace (prefixWord ++ tailWord_4586840) baseStart_4586840 baseEnd_4586840 := by
    simpa [prefixWord, tailWord_4586840, baseEnd_4586840] using wordTrace_append hprefix tailTrace_4586840
  have hstable : (prefixWord ++ tailWord_4586840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586840).length < 2 ^ (prefixWord ++ tailWord_4586840).sum := by decide
  have hdescent : baseEnd_4586840 < baseStart_4586840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586863 : List Nat := [1, 1, 2, 1, 3, 1, 6, 3, 5]
def baseStart_4586863 : Nat := 118140960795 + 4586863 * 2 ^ 59
def prefixEnd_4586863 : Nat := 4983230072969 + 3 ^ 40 * 4586863 * 2
def baseEnd_4586863 : Nat := 261696157258221401235323

theorem tailTrace_4586863 : CollatzResearch.WordTrace tailWord_4586863 prefixEnd_4586863 261696157258221401235323 := by
  unfold tailWord_4586863
  simp only [CollatzResearch.WordTrace]
  refine ⟨167296637581586199677933243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111531091721057466451955495 167296637581586199677933243)
  ·
    refine ⟨250944956372379299516899865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167296637581586199677933243 250944956372379299516899865)
    ·
      refine ⟨188208717279284474637674899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250944956372379299516899865 188208717279284474637674899)
      ·
        refine ⟨282313075918926711956512349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188208717279284474637674899 282313075918926711956512349)
        ·
          refine ⟨105867403469597516983692131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282313075918926711956512349 105867403469597516983692131)
          ·
            refine ⟨158801105204396275475538197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105867403469597516983692131 158801105204396275475538197)
            ·
              refine ⟨7443801806456075412915853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158801105204396275475538197 7443801806456075412915853)
              ·
                refine ⟨2791425677421028279843445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7443801806456075412915853 2791425677421028279843445)
                ·
                  refine ⟨261696157258221401235323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2791425677421028279843445 261696157258221401235323)
                  ·
                    rfl

theorem cell23_4586863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 5].length) (baseStart_4586863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586863 prefixEnd_4586863 := by exact prefixLift 4586863
  have htrace : WordTrace (prefixWord ++ tailWord_4586863) baseStart_4586863 baseEnd_4586863 := by
    simpa [prefixWord, tailWord_4586863, baseEnd_4586863] using wordTrace_append hprefix tailTrace_4586863
  have hstable : (prefixWord ++ tailWord_4586863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586863).length < 2 ^ (prefixWord ++ tailWord_4586863).sum := by decide
  have hdescent : baseEnd_4586863 < baseStart_4586863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586876 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_4586876 : Nat := 118140960795 + 4586876 * 2 ^ 59
def prefixEnd_4586876 : Nat := 4983230072969 + 3 ^ 40 * 4586876 * 2
def baseEnd_4586876 : Nat := 785090696857500353418449

theorem tailTrace_4586876 : CollatzResearch.WordTrace tailWord_4586876 prefixEnd_4586876 785090696857500353418449 := by
  unfold tailWord_4586876
  simp only [CollatzResearch.WordTrace]
  refine ⟨83648555865269551449078241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111531407820359401932104321 83648555865269551449078241)
  ·
    refine ⟨62736416898952163586808681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83648555865269551449078241 62736416898952163586808681)
    ·
      refine ⟨47052312674214122690106511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62736416898952163586808681 47052312674214122690106511)
      ·
        refine ⟨70578469011321184035159767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47052312674214122690106511 70578469011321184035159767)
        ·
          refine ⟨105867703516981776052739651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70578469011321184035159767 105867703516981776052739651)
          ·
            refine ⟨158801555275472664079109477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105867703516981776052739651 158801555275472664079109477)
            ·
              refine ⟨29775291614151124514833027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158801555275472664079109477 29775291614151124514833027)
              ·
                refine ⟨44662937421226686772249541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29775291614151124514833027 44662937421226686772249541)
                ·
                  refine ⟨8374300766480003769796789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44662937421226686772249541 8374300766480003769796789)
                  ·
                    refine ⟨785090696857500353418449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8374300766480003769796789 785090696857500353418449)
                    ·
                      rfl

theorem cell23_4586876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_4586876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586876 prefixEnd_4586876 := by exact prefixLift 4586876
  have htrace : WordTrace (prefixWord ++ tailWord_4586876) baseStart_4586876 baseEnd_4586876 := by
    simpa [prefixWord, tailWord_4586876, baseEnd_4586876] using wordTrace_append hprefix tailTrace_4586876
  have hstable : (prefixWord ++ tailWord_4586876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586876).length < 2 ^ (prefixWord ++ tailWord_4586876).sum := by decide
  have hdescent : baseEnd_4586876 < baseStart_4586876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586906 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_4586906 : Nat := 118140960795 + 4586906 * 2 ^ 59
def prefixEnd_4586906 : Nat := 4983230072969 + 3 ^ 40 * 4586906 * 2
def baseEnd_4586906 : Nat := 785095831664045314293403

theorem tailTrace_4586906 : CollatzResearch.WordTrace tailWord_4586906 prefixEnd_4586906 785095831664045314293403 := by
  unfold tailWord_4586906
  simp only [CollatzResearch.WordTrace]
  refine ⟨41824551480107604505437143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111532137280286945347832381 41824551480107604505437143)
  ·
    refine ⟨62736827220161406758155715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41824551480107604505437143 62736827220161406758155715)
    ·
      refine ⟨94105240830242110137233573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62736827220161406758155715 94105240830242110137233573)
      ·
        refine ⟨17644732655670395650731295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94105240830242110137233573 17644732655670395650731295)
        ·
          refine ⟨26467098983505593476096943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17644732655670395650731295 26467098983505593476096943)
          ·
            refine ⟨39700648475258390214145415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26467098983505593476096943 39700648475258390214145415)
            ·
              refine ⟨59550972712887585321218123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39700648475258390214145415 59550972712887585321218123)
              ·
                refine ⟨89326459069331377981827185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59550972712887585321218123 89326459069331377981827185)
                ·
                  refine ⟨66994844301998533486370389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89326459069331377981827185 66994844301998533486370389)
                  ·
                    refine ⟨785095831664045314293403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66994844301998533486370389 785095831664045314293403)
                    ·
                      rfl

theorem cell23_4586906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_4586906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586906 prefixEnd_4586906 := by exact prefixLift 4586906
  have htrace : WordTrace (prefixWord ++ tailWord_4586906) baseStart_4586906 baseEnd_4586906 := by
    simpa [prefixWord, tailWord_4586906, baseEnd_4586906] using wordTrace_append hprefix tailTrace_4586906
  have hstable : (prefixWord ++ tailWord_4586906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586906).length < 2 ^ (prefixWord ++ tailWord_4586906).sum := by decide
  have hdescent : baseEnd_4586906 < baseStart_4586906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586916 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_4586916 : Nat := 118140960795 + 4586916 * 2 ^ 59
def prefixEnd_4586916 : Nat := 4983230072969 + 3 ^ 40 * 4586916 * 2
def baseEnd_4586916 : Nat := 2355292629798680903755163

theorem tailTrace_4586916 : CollatzResearch.WordTrace tailWord_4586916 prefixEnd_4586916 2355292629798680903755163 := by
  unfold tailWord_4586916
  simp only [CollatzResearch.WordTrace]
  refine ⟨83649285325197094864806301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111532380433596126486408401 83649285325197094864806301)
  ·
    refine ⟨31368481996948910574302363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83649285325197094864806301 31368481996948910574302363)
    ·
      refine ⟨47052722995423365861453545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31368481996948910574302363 47052722995423365861453545)
      ·
        refine ⟨35289542246567524396090159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47052722995423365861453545 35289542246567524396090159)
        ·
          refine ⟨52934313369851286594135239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35289542246567524396090159 52934313369851286594135239)
          ·
            refine ⟨79401470054776929891202859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52934313369851286594135239 79401470054776929891202859)
            ·
              refine ⟨119102205082165394836804289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79401470054776929891202859 119102205082165394836804289)
              ·
                refine ⟨89326653811624046127603217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119102205082165394836804289 89326653811624046127603217)
                ·
                  refine ⟨66994990358718034595702413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89326653811624046127603217 66994990358718034595702413)
                  ·
                    refine ⟨25123121384519262973388405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66994990358718034595702413 25123121384519262973388405)
                    ·
                      refine ⟨2355292629798680903755163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25123121384519262973388405 2355292629798680903755163)
                      ·
                        rfl

theorem cell23_4586916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_4586916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586916 prefixEnd_4586916 := by exact prefixLift 4586916
  have htrace : WordTrace (prefixWord ++ tailWord_4586916) baseStart_4586916 baseEnd_4586916 := by
    simpa [prefixWord, tailWord_4586916, baseEnd_4586916] using wordTrace_append hprefix tailTrace_4586916
  have hstable : (prefixWord ++ tailWord_4586916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586916).length < 2 ^ (prefixWord ++ tailWord_4586916).sum := by decide
  have hdescent : baseEnd_4586916 < baseStart_4586916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586936 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 8]
def baseStart_4586936 : Nat := 118140960795 + 4586936 * 2 ^ 59
def prefixEnd_4586936 : Nat := 4983230072969 + 3 ^ 40 * 4586936 * 2
def baseEnd_4586936 : Nat := 261700322156863425056119

theorem tailTrace_4586936 : CollatzResearch.WordTrace tailWord_4586936 prefixEnd_4586936 261700322156863425056119 := by
  unfold tailWord_4586936
  simp only [CollatzResearch.WordTrace]
  refine ⟨83649650055160866572670331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111532866740214488763560441 83649650055160866572670331)
  ·
    refine ⟨125474475082741299859005497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83649650055160866572670331 125474475082741299859005497)
    ·
      refine ⟨94105856312055974894254123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125474475082741299859005497 94105856312055974894254123)
      ·
        refine ⟨141158784468083962341381185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94105856312055974894254123 141158784468083962341381185)
        ·
          refine ⟨105869088351062971756035889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141158784468083962341381185 105869088351062971756035889)
          ·
            refine ⟨79401816263297228817026917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105869088351062971756035889 79401816263297228817026917)
            ·
              refine ⟨14887840549368230403192547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79401816263297228817026917 14887840549368230403192547)
              ·
                refine ⟨22331760824052345604788821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14887840549368230403192547 22331760824052345604788821)
                ·
                  refine ⟨261700322156863425056119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22331760824052345604788821 261700322156863425056119)
                  ·
                    rfl

theorem cell23_4586936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 8].length) (baseStart_4586936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586936 prefixEnd_4586936 := by exact prefixLift 4586936
  have htrace : WordTrace (prefixWord ++ tailWord_4586936) baseStart_4586936 baseEnd_4586936 := by
    simpa [prefixWord, tailWord_4586936, baseEnd_4586936] using wordTrace_append hprefix tailTrace_4586936
  have hstable : (prefixWord ++ tailWord_4586936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586936).length < 2 ^ (prefixWord ++ tailWord_4586936).sum := by decide
  have hdescent : baseEnd_4586936 < baseStart_4586936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4586976 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_4586976 : Nat := 118140960795 + 4586976 * 2 ^ 59
def prefixEnd_4586976 : Nat := 4983230072969 + 3 ^ 40 * 4586976 * 2
def baseEnd_4586976 : Nat := 2355323438637950669004887

theorem tailTrace_4586976 : CollatzResearch.WordTrace tailWord_4586976 prefixEnd_4586976 2355323438637950669004887 := by
  unfold tailWord_4586976
  simp only [CollatzResearch.WordTrace]
  refine ⟨83650379515088409988398391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111533839353451213317864521 83650379515088409988398391)
  ·
    refine ⟨125475569272632614982597587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83650379515088409988398391 125475569272632614982597587)
    ·
      refine ⟨188213353908948922473896381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125475569272632614982597587 188213353908948922473896381)
      ·
        refine ⟨70580007715855845927711143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188213353908948922473896381 70580007715855845927711143)
        ·
          refine ⟨105870011573783768891566715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70580007715855845927711143 105870011573783768891566715)
          ·
            refine ⟨158805017360675653337350073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105870011573783768891566715 158805017360675653337350073)
            ·
              refine ⟨119103763020506740003012555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158805017360675653337350073 119103763020506740003012555)
              ·
                refine ⟨178655644530760110004518833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119103763020506740003012555 178655644530760110004518833)
                ·
                  refine ⟨133991733398070082503389125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178655644530760110004518833 133991733398070082503389125)
                  ·
                    refine ⟨25123450012138140469385461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133991733398070082503389125 25123450012138140469385461)
                    ·
                      refine ⟨2355323438637950669004887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25123450012138140469385461 2355323438637950669004887)
                      ·
                        rfl

theorem cell23_4586976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_4586976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4586976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4586976 prefixEnd_4586976 := by exact prefixLift 4586976
  have htrace : WordTrace (prefixWord ++ tailWord_4586976) baseStart_4586976 baseEnd_4586976 := by
    simpa [prefixWord, tailWord_4586976, baseEnd_4586976] using wordTrace_append hprefix tailTrace_4586976
  have hstable : (prefixWord ++ tailWord_4586976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4586976).length < 2 ^ (prefixWord ++ tailWord_4586976).sum := by decide
  have hdescent : baseEnd_4586976 < baseStart_4586976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4586976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587013 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_4587013 : Nat := 118140960795 + 4587013 * 2 ^ 59
def prefixEnd_4587013 : Nat := 4983230072969 + 3 ^ 40 * 4587013 * 2
def baseEnd_4587013 : Nat := 785114145807389008080739

theorem tailTrace_4587013 : CollatzResearch.WordTrace tailWord_4587013 prefixEnd_4587013 785114145807389008080739 := by
  unfold tailWord_4587013
  simp only [CollatzResearch.WordTrace]
  refine ⟨167302108531042775295893693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111534739020695183530595795 167302108531042775295893693)
  ·
    refine ⟨62738290699141040735960135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167302108531042775295893693 62738290699141040735960135)
    ·
      refine ⟨94107436048711561103940203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62738290699141040735960135 94107436048711561103940203)
      ·
        refine ⟨141161154073067341655910305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94107436048711561103940203 141161154073067341655910305)
        ·
          refine ⟨105870865554800506241932729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141161154073067341655910305 105870865554800506241932729)
          ·
            refine ⟨79403149166100379681449547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105870865554800506241932729 79403149166100379681449547)
            ·
              refine ⟨119104723749150569522174321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79403149166100379681449547 119104723749150569522174321)
              ·
                refine ⟨89328542811862927141630741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119104723749150569522174321 89328542811862927141630741)
                ·
                  refine ⟨4187275444306074709763941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89328542811862927141630741 4187275444306074709763941)
                  ·
                    refine ⟨785114145807389008080739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4187275444306074709763941 785114145807389008080739)
                    ·
                      rfl

theorem cell23_4587013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_4587013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587013 prefixEnd_4587013 := by exact prefixLift 4587013
  have htrace : WordTrace (prefixWord ++ tailWord_4587013) baseStart_4587013 baseEnd_4587013 := by
    simpa [prefixWord, tailWord_4587013, baseEnd_4587013] using wordTrace_append hprefix tailTrace_4587013
  have hstable : (prefixWord ++ tailWord_4587013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587013).length < 2 ^ (prefixWord ++ tailWord_4587013).sum := by decide
  have hdescent : baseEnd_4587013 < baseStart_4587013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587023 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 3]
def baseStart_4587023 : Nat := 118140960795 + 4587023 * 2 ^ 59
def prefixEnd_4587023 : Nat := 4983230072969 + 3 ^ 40 * 4587023 * 2
def baseEnd_4587023 : Nat := 2355347572228711985117171

theorem tailTrace_4587023 : CollatzResearch.WordTrace tailWord_4587023 prefixEnd_4587023 2355347572228711985117171 := by
  unfold tailWord_4587023
  simp only [CollatzResearch.WordTrace]
  refine ⟨167302473261006547003757723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111534982174004364669171815 167302473261006547003757723)
  ·
    refine ⟨250953709891509820505636585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167302473261006547003757723 250953709891509820505636585)
    ·
      refine ⟨188215282418632365379227439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250953709891509820505636585 188215282418632365379227439)
      ·
        refine ⟨282322923627948548068841159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188215282418632365379227439 282322923627948548068841159)
        ·
          refine ⟨423484385441922822103261739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282322923627948548068841159 423484385441922822103261739)
          ·
            refine ⟨635226578162884233154892609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423484385441922822103261739 635226578162884233154892609)
            ·
              refine ⟨476419933622163174866169457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635226578162884233154892609 476419933622163174866169457)
              ·
                refine ⟨357314950216622381149627093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476419933622163174866169457 357314950216622381149627093)
                ·
                  refine ⟨8374569145702087058194385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 357314950216622381149627093 8374569145702087058194385)
                  ·
                    refine ⟨6280926859276565293645789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8374569145702087058194385 6280926859276565293645789)
                    ·
                      refine ⟨2355347572228711985117171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6280926859276565293645789 2355347572228711985117171)
                      ·
                        rfl

theorem cell23_4587023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_4587023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587023 prefixEnd_4587023 := by exact prefixLift 4587023
  have htrace : WordTrace (prefixWord ++ tailWord_4587023) baseStart_4587023 baseEnd_4587023 := by
    simpa [prefixWord, tailWord_4587023, baseEnd_4587023] using wordTrace_append hprefix tailTrace_4587023
  have hstable : (prefixWord ++ tailWord_4587023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587023).length < 2 ^ (prefixWord ++ tailWord_4587023).sum := by decide
  have hdescent : baseEnd_4587023 < baseStart_4587023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587037 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_4587037 : Nat := 118140960795 + 4587037 * 2 ^ 59
def prefixEnd_4587037 : Nat := 4983230072969 + 3 ^ 40 * 4587037 * 2
def baseEnd_4587037 : Nat := 2355354760957874930342107

theorem tailTrace_4587037 : CollatzResearch.WordTrace tailWord_4587037 prefixEnd_4587037 2355354760957874930342107 := by
  unfold tailWord_4587037
  simp only [CollatzResearch.WordTrace]
  refine ⟨167302983882955827394767365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111535322588637218263178243 167302983882955827394767365)
  ·
    refine ⟨31369309478054217636518881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167302983882955827394767365 31369309478054217636518881)
    ·
      refine ⟨23526982108540663227389161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31369309478054217636518881 23526982108540663227389161)
      ·
        refine ⟨17645236581405497420541871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23526982108540663227389161 17645236581405497420541871)
        ·
          refine ⟨26467854872108246130812807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17645236581405497420541871 26467854872108246130812807)
          ·
            refine ⟨39701782308162369196219211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26467854872108246130812807 39701782308162369196219211)
            ·
              refine ⟨59552673462243553794328817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39701782308162369196219211 59552673462243553794328817)
              ·
                refine ⟨44664505096682665345746613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59552673462243553794328817 44664505096682665345746613)
                ·
                  refine ⟨4187297352813999876163745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44664505096682665345746613 4187297352813999876163745)
                  ·
                    refine ⟨3140473014610499907122809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4187297352813999876163745 3140473014610499907122809)
                    ·
                      refine ⟨2355354760957874930342107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140473014610499907122809 2355354760957874930342107)
                      ·
                        rfl

theorem cell23_4587037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_4587037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587037 prefixEnd_4587037 := by exact prefixLift 4587037
  have htrace : WordTrace (prefixWord ++ tailWord_4587037) baseStart_4587037 baseEnd_4587037 := by
    simpa [prefixWord, tailWord_4587037, baseEnd_4587037] using wordTrace_append hprefix tailTrace_4587037
  have hstable : (prefixWord ++ tailWord_4587037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587037).length < 2 ^ (prefixWord ++ tailWord_4587037).sum := by decide
  have hdescent : baseEnd_4587037 < baseStart_4587037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587038 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_4587038 : Nat := 118140960795 + 4587038 * 2 ^ 59
def prefixEnd_4587038 : Nat := 4983230072969 + 3 ^ 40 * 4587038 * 2
def baseEnd_4587038 : Nat := 261706141604281047381067

theorem tailTrace_4587038 : CollatzResearch.WordTrace tailWord_4587038 prefixEnd_4587038 261706141604281047381067 := by
  unfold tailWord_4587038
  simp only [CollatzResearch.WordTrace]
  refine ⟨20912877544494025570694221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111535346903968136377035845 20912877544494025570694221)
  ·
    refine ⟨7842329079185259589010333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20912877544494025570694221 7842329079185259589010333)
    ·
      refine ⟨2940873404694472345878875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7842329079185259589010333 2940873404694472345878875)
      ·
        refine ⟨4411310107041708518818313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940873404694472345878875 4411310107041708518818313)
        ·
          refine ⟨3308482580281281389113735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4411310107041708518818313 3308482580281281389113735)
          ·
            refine ⟨4962723870421922083670603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308482580281281389113735 4962723870421922083670603)
            ·
              refine ⟨7444085805632883125505905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962723870421922083670603 7444085805632883125505905)
              ·
                refine ⟨5583064354224662344129429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7444085805632883125505905 5583064354224662344129429)
                ·
                  refine ⟨261706141604281047381067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5583064354224662344129429 261706141604281047381067)
                  ·
                    rfl

theorem cell23_4587038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_4587038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587038 prefixEnd_4587038 := by exact prefixLift 4587038
  have htrace : WordTrace (prefixWord ++ tailWord_4587038) baseStart_4587038 baseEnd_4587038 := by
    simpa [prefixWord, tailWord_4587038, baseEnd_4587038] using wordTrace_append hprefix tailTrace_4587038
  have hstable : (prefixWord ++ tailWord_4587038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587038).length < 2 ^ (prefixWord ++ tailWord_4587038).sum := by decide
  have hdescent : baseEnd_4587038 < baseStart_4587038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587043 : List Nat := [1, 1, 1, 4, 5, 1, 10]
def baseStart_4587043 : Nat := 118140960795 + 4587043 * 2 ^ 59
def prefixEnd_4587043 : Nat := 4983230072969 + 3 ^ 40 * 4587043 * 2
def baseEnd_4587043 : Nat := 29078491874590146998359

theorem tailTrace_4587043 : CollatzResearch.WordTrace tailWord_4587043 prefixEnd_4587043 29078491874590146998359 := by
  unfold tailWord_4587043
  simp only [CollatzResearch.WordTrace]
  refine ⟨167303202720934090419485783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111535468480622726946323855 167303202720934090419485783)
  ·
    refine ⟨250954804081401135629228675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167303202720934090419485783 250954804081401135629228675)
    ·
      refine ⟨376432206122101703443843013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250954804081401135629228675 376432206122101703443843013)
      ·
        refine ⟨70581038647894069395720565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 376432206122101703443843013 70581038647894069395720565)
        ·
          refine ⟨6616972373240069005848803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70581038647894069395720565 6616972373240069005848803)
          ·
            refine ⟨9925458559860103508773205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6616972373240069005848803 9925458559860103508773205)
            ·
              refine ⟨29078491874590146998359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9925458559860103508773205 29078491874590146998359)
              ·
                rfl

theorem cell23_4587043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 10].length) (baseStart_4587043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587043 prefixEnd_4587043 := by exact prefixLift 4587043
  have htrace : WordTrace (prefixWord ++ tailWord_4587043) baseStart_4587043 baseEnd_4587043 := by
    simpa [prefixWord, tailWord_4587043, baseEnd_4587043] using wordTrace_append hprefix tailTrace_4587043
  have hstable : (prefixWord ++ tailWord_4587043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587043).length < 2 ^ (prefixWord ++ tailWord_4587043).sum := by decide
  have hdescent : baseEnd_4587043 < baseStart_4587043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587054 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_4587054 : Nat := 118140960795 + 4587054 * 2 ^ 59
def prefixEnd_4587054 : Nat := 4983230072969 + 3 ^ 40 * 4587054 * 2
def baseEnd_4587054 : Nat := 2355363490129001363829529

theorem tailTrace_4587054 : CollatzResearch.WordTrace tailWord_4587054 prefixEnd_4587054 2355363490129001363829529 := by
  unfold tailWord_4587054
  simp only [CollatzResearch.WordTrace]
  refine ⟨20912950490486779912267027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111535735949262826198757477 20912950490486779912267027)
  ·
    refine ⟨31369425735730169868400541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20912950490486779912267027 31369425735730169868400541)
    ·
      refine ⟨11763534650898813700650203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31369425735730169868400541 11763534650898813700650203)
      ·
        refine ⟨17645301976348220550975305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11763534650898813700650203 17645301976348220550975305)
        ·
          refine ⟨13233976482261165413231479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17645301976348220550975305 13233976482261165413231479)
          ·
            refine ⟨19850964723391748119847219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13233976482261165413231479 19850964723391748119847219)
            ·
              refine ⟨29776447085087622179770829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19850964723391748119847219 29776447085087622179770829)
              ·
                refine ⟨11166167656907858317414061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29776447085087622179770829 11166167656907858317414061)
                ·
                  refine ⟨4187312871340446869030273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11166167656907858317414061 4187312871340446869030273)
                  ·
                    refine ⟨3140484653505335151772705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4187312871340446869030273 3140484653505335151772705)
                    ·
                      refine ⟨2355363490129001363829529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140484653505335151772705 2355363490129001363829529)
                      ·
                        rfl

theorem cell23_4587054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_4587054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587054 prefixEnd_4587054 := by exact prefixLift 4587054
  have htrace : WordTrace (prefixWord ++ tailWord_4587054) baseStart_4587054 baseEnd_4587054 := by
    simpa [prefixWord, tailWord_4587054, baseEnd_4587054] using wordTrace_append hprefix tailTrace_4587054
  have hstable : (prefixWord ++ tailWord_4587054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587054).length < 2 ^ (prefixWord ++ tailWord_4587054).sum := by decide
  have hdescent : baseEnd_4587054 < baseStart_4587054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587093 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4587093 : Nat := 118140960795 + 4587093 * 2 ^ 59
def prefixEnd_4587093 : Nat := 4983230072969 + 3 ^ 40 * 4587093 * 2
def baseEnd_4587093 : Nat := 2355383515874526711241849

theorem tailTrace_4587093 : CollatzResearch.WordTrace tailWord_4587093 prefixEnd_4587093 2355383515874526711241849 := by
  unfold tailWord_4587093
  simp only [CollatzResearch.WordTrace]
  refine ⟨167305026370752948958805933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111536684247168632639203955 167305026370752948958805933)
  ·
    refine ⟨62739384889032355859552225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167305026370752948958805933 62739384889032355859552225)
    ·
      refine ⟨47054538666774266894664169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62739384889032355859552225 47054538666774266894664169)
      ·
        refine ⟨35290904000080700170998127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47054538666774266894664169 35290904000080700170998127)
        ·
          refine ⟨52936356000121050256497191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35290904000080700170998127 52936356000121050256497191)
          ·
            refine ⟨79404534000181575384745787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52936356000121050256497191 79404534000181575384745787)
            ·
              refine ⟨119106801000272363077118681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79404534000181575384745787 119106801000272363077118681)
              ·
                refine ⟨89330100750204272307839011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119106801000272363077118681 89330100750204272307839011)
                ·
                  refine ⟨133995151125306408461758517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89330100750204272307839011 133995151125306408461758517)
                  ·
                    refine ⟨12562045417997475793289861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133995151125306408461758517 12562045417997475793289861)
                    ·
                      refine ⟨2355383515874526711241849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12562045417997475793289861 2355383515874526711241849)
                      ·
                        rfl

theorem cell23_4587093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4587093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587093 prefixEnd_4587093 := by exact prefixLift 4587093
  have htrace : WordTrace (prefixWord ++ tailWord_4587093) baseStart_4587093 baseEnd_4587093 := by
    simpa [prefixWord, tailWord_4587093, baseEnd_4587093] using wordTrace_append hprefix tailTrace_4587093
  have hstable : (prefixWord ++ tailWord_4587093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587093).length < 2 ^ (prefixWord ++ tailWord_4587093).sum := by decide
  have hdescent : baseEnd_4587093 < baseStart_4587093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587094 : List Nat := [5, 2, 2, 2, 1, 2, 9]
def baseStart_4587094 : Nat := 118140960795 + 4587094 * 2 ^ 59
def prefixEnd_4587094 : Nat := 4983230072969 + 3 ^ 40 * 4587094 * 2
def baseEnd_4587094 : Nat := 29078815177224459349745

theorem tailTrace_4587094 : CollatzResearch.WordTrace tailWord_4587094 prefixEnd_4587094 29078815177224459349745 := by
  unfold tailWord_4587094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10456566427734332883099521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111536708562499550753061557 10456566427734332883099521)
  ·
    refine ⟨7842424820800749662324641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10456566427734332883099521 7842424820800749662324641)
    ·
      refine ⟨5881818615600562246743481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7842424820800749662324641 5881818615600562246743481)
      ·
        refine ⟨4411363961700421685057611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5881818615600562246743481 4411363961700421685057611)
        ·
          refine ⟨6617045942550632527586417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4411363961700421685057611 6617045942550632527586417)
          ·
            refine ⟨4962784456912974395689813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6617045942550632527586417 4962784456912974395689813)
            ·
              refine ⟨29078815177224459349745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4962784456912974395689813 29078815177224459349745)
              ·
                rfl

theorem cell23_4587094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 9].length) (baseStart_4587094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587094 prefixEnd_4587094 := by exact prefixLift 4587094
  have htrace : WordTrace (prefixWord ++ tailWord_4587094) baseStart_4587094 baseEnd_4587094 := by
    simpa [prefixWord, tailWord_4587094, baseEnd_4587094] using wordTrace_append hprefix tailTrace_4587094
  have hstable : (prefixWord ++ tailWord_4587094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587094).length < 2 ^ (prefixWord ++ tailWord_4587094).sum := by decide
  have hdescent : baseEnd_4587094 < baseStart_4587094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587123 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 4]
def baseStart_4587123 : Nat := 118140960795 + 4587123 * 2 ^ 59
def prefixEnd_4587123 : Nat := 4983230072969 + 3 ^ 40 * 4587123 * 2
def baseEnd_4587123 : Nat := 2355398920294161593866711

theorem tailTrace_4587123 : CollatzResearch.WordTrace tailWord_4587123 prefixEnd_4587123 2355398920294161593866711 := by
  unfold tailWord_4587123
  simp only [CollatzResearch.WordTrace]
  refine ⟨167306120560644264082398023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111537413707096176054932015 167306120560644264082398023)
  ·
    refine ⟨250959180840966396123597035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167306120560644264082398023 250959180840966396123597035)
    ·
      refine ⟨376438771261449594185395553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250959180840966396123597035 376438771261449594185395553)
      ·
        refine ⟨282329078446087195639046665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376438771261449594185395553 282329078446087195639046665)
        ·
          refine ⟨211746808834565396729284999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282329078446087195639046665 211746808834565396729284999)
          ·
            refine ⟨317620213251848095093927499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211746808834565396729284999 317620213251848095093927499)
            ·
              refine ⟨476430319877772142640891249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317620213251848095093927499 476430319877772142640891249)
              ·
                refine ⟨357322739908329106980668437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476430319877772142640891249 357322739908329106980668437)
                ·
                  refine ⟨16749503433202926889718833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 357322739908329106980668437 16749503433202926889718833)
                  ·
                    refine ⟨12562127574902195167289125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16749503433202926889718833 12562127574902195167289125)
                    ·
                      refine ⟨2355398920294161593866711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12562127574902195167289125 2355398920294161593866711)
                      ·
                        rfl

theorem cell23_4587123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_4587123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587123 prefixEnd_4587123 := by exact prefixLift 4587123
  have htrace : WordTrace (prefixWord ++ tailWord_4587123) baseStart_4587123 baseEnd_4587123 := by
    simpa [prefixWord, tailWord_4587123, baseEnd_4587123] using wordTrace_append hprefix tailTrace_4587123
  have hstable : (prefixWord ++ tailWord_4587123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587123).length < 2 ^ (prefixWord ++ tailWord_4587123).sum := by decide
  have hdescent : baseEnd_4587123 < baseStart_4587123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587200 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_4587200 : Nat := 118140960795 + 4587200 * 2 ^ 59
def prefixEnd_4587200 : Nat := 4983230072969 + 3 ^ 40 * 4587200 * 2
def baseEnd_4587200 : Nat := 2355438458304557792603857

theorem tailTrace_4587200 : CollatzResearch.WordTrace tailWord_4587200 prefixEnd_4587200 2355438458304557792603857 := by
  unfold tailWord_4587200
  simp only [CollatzResearch.WordTrace]
  refine ⟨83654464490682653116475527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111539285987576870821967369 83654464490682653116475527)
  ·
    refine ⟨125481696736023979674713291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83654464490682653116475527 125481696736023979674713291)
    ·
      refine ⟨188222545104035969512069937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125481696736023979674713291 188222545104035969512069937)
      ·
        refine ⟨141166908828026977134052453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188222545104035969512069937 141166908828026977134052453)
        ·
          refine ⟨26468795405255058212634835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141166908828026977134052453 26468795405255058212634835)
          ·
            refine ⟨39703193107882587318952253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26468795405255058212634835 39703193107882587318952253)
            ·
              refine ⟨14888697415455970244607095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39703193107882587318952253 14888697415455970244607095)
              ·
                refine ⟨22333046123183955366910643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14888697415455970244607095 22333046123183955366910643)
                ·
                  refine ⟨33499569184775933050365965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22333046123183955366910643 33499569184775933050365965)
                  ·
                    refine ⟨12562338444290974893887237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33499569184775933050365965 12562338444290974893887237)
                    ·
                      refine ⟨2355438458304557792603857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12562338444290974893887237 2355438458304557792603857)
                      ·
                        rfl

theorem cell23_4587200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_4587200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587200 prefixEnd_4587200 := by exact prefixLift 4587200
  have htrace : WordTrace (prefixWord ++ tailWord_4587200) baseStart_4587200 baseEnd_4587200 := by
    simpa [prefixWord, tailWord_4587200, baseEnd_4587200] using wordTrace_append hprefix tailTrace_4587200
  have hstable : (prefixWord ++ tailWord_4587200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587200).length < 2 ^ (prefixWord ++ tailWord_4587200).sum := by decide
  have hdescent : baseEnd_4587200 < baseStart_4587200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587217 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 2, 4, 2]
def baseStart_4587217 : Nat := 118140960795 + 4587217 * 2 ^ 59
def prefixEnd_4587217 : Nat := 4983230072969 + 3 ^ 40 * 4587217 * 2
def baseEnd_4587217 : Nat := 2355447187475684226091279

theorem tailTrace_4587217 : CollatzResearch.WordTrace tailWord_4587217 prefixEnd_4587217 2355447187475684226091279 := by
  unfold tailWord_4587217
  simp only [CollatzResearch.WordTrace]
  refine ⟨167309549022303718136319905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111539699348202478757546603 167309549022303718136319905)
  ·
    refine ⟨125482161766727788602239929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167309549022303718136319905 125482161766727788602239929)
    ·
      refine ⟨94111621325045841451679947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125482161766727788602239929 94111621325045841451679947)
      ·
        refine ⟨141167431987568762177519921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94111621325045841451679947 141167431987568762177519921)
        ·
          refine ⟨105875573990676571633139941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141167431987568762177519921 105875573990676571633139941)
          ·
            refine ⟨19851670123251857181213739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105875573990676571633139941 19851670123251857181213739)
            ·
              refine ⟨29777505184877785771820609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19851670123251857181213739 29777505184877785771820609)
              ·
                refine ⟨22333128888658339328865457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29777505184877785771820609 22333128888658339328865457)
                ·
                  refine ⟨16749846666493754496649093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22333128888658339328865457 16749846666493754496649093)
                  ·
                    refine ⟨3140596249967578968121705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16749846666493754496649093 3140596249967578968121705)
                    ·
                      refine ⟨2355447187475684226091279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140596249967578968121705 2355447187475684226091279)
                      ·
                        rfl

theorem cell23_4587217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_4587217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587217 prefixEnd_4587217 := by exact prefixLift 4587217
  have htrace : WordTrace (prefixWord ++ tailWord_4587217) baseStart_4587217 baseEnd_4587217 := by
    simpa [prefixWord, tailWord_4587217, baseEnd_4587217] using wordTrace_append hprefix tailTrace_4587217
  have hstable : (prefixWord ++ tailWord_4587217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587217).length < 2 ^ (prefixWord ++ tailWord_4587217).sum := by decide
  have hdescent : baseEnd_4587217 < baseStart_4587217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587267 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 3]
def baseStart_4587267 : Nat := 118140960795 + 4587267 * 2 ^ 59
def prefixEnd_4587267 : Nat := 4983230072969 + 3 ^ 40 * 4587267 * 2
def baseEnd_4587267 : Nat := 2355472861508409030466049

theorem tailTrace_4587267 : CollatzResearch.WordTrace tailWord_4587267 prefixEnd_4587267 2355472861508409030466049 := by
  unfold tailWord_4587267
  simp only [CollatzResearch.WordTrace]
  refine ⟨167311372672122576675640055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111540915114748384450426703 167311372672122576675640055)
  ·
    refine ⟨250967059008183865013460083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167311372672122576675640055 250967059008183865013460083)
    ·
      refine ⟨376450588512275797520190125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250967059008183865013460083 376450588512275797520190125)
      ·
        refine ⟨141168970692103424070071297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376450588512275797520190125 141168970692103424070071297)
        ·
          refine ⟨105876728019077568052553473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141168970692103424070071297 105876728019077568052553473)
          ·
            refine ⟨79407546014308176039415105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105876728019077568052553473 79407546014308176039415105)
            ·
              refine ⟨59555659510731132029561329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79407546014308176039415105 59555659510731132029561329)
              ·
                refine ⟨44666744633048349022170997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59555659510731132029561329 44666744633048349022170997)
                ·
                  refine ⟨4187507309348282720828531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44666744633048349022170997 4187507309348282720828531)
                  ·
                    refine ⟨6281260964022424081242797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4187507309348282720828531 6281260964022424081242797)
                    ·
                      refine ⟨2355472861508409030466049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6281260964022424081242797 2355472861508409030466049)
                      ·
                        rfl

theorem cell23_4587267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_4587267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587267 prefixEnd_4587267 := by exact prefixLift 4587267
  have htrace : WordTrace (prefixWord ++ tailWord_4587267) baseStart_4587267 baseEnd_4587267 := by
    simpa [prefixWord, tailWord_4587267, baseEnd_4587267] using wordTrace_append hprefix tailTrace_4587267
  have hstable : (prefixWord ++ tailWord_4587267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587267).length < 2 ^ (prefixWord ++ tailWord_4587267).sum := by decide
  have hdescent : baseEnd_4587267 < baseStart_4587267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587304 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 1, 5]
def baseStart_4587304 : Nat := 118140960795 + 4587304 * 2 ^ 59
def prefixEnd_4587304 : Nat := 4983230072969 + 3 ^ 40 * 4587304 * 2
def baseEnd_4587304 : Nat := 785163953430875128567793

theorem tailTrace_4587304 : CollatzResearch.WordTrace tailWord_4587304 prefixEnd_4587304 785163953430875128567793 := by
  unfold tailWord_4587304
  simp only [CollatzResearch.WordTrace]
  refine ⟨83656361086494265997368483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111541814781992354663157977 83656361086494265997368483)
  ·
    refine ⟨125484541629741398996052725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83656361086494265997368483 125484541629741398996052725)
    ·
      refine ⟨11764175777788256155879943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125484541629741398996052725 11764175777788256155879943)
      ·
        refine ⟨17646263666682384233819915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11764175777788256155879943 17646263666682384233819915)
        ·
          refine ⟨26469395500023576350729873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17646263666682384233819915 26469395500023576350729873)
          ·
            refine ⟨19852046625017682263047405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26469395500023576350729873 19852046625017682263047405)
            ·
              refine ⟨7444517484381630848642777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19852046625017682263047405 7444517484381630848642777)
              ·
                refine ⟨5583388113286223136482083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7444517484381630848642777 5583388113286223136482083)
                ·
                  refine ⟨8375082169929334704723125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5583388113286223136482083 8375082169929334704723125)
                  ·
                    refine ⟨785163953430875128567793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8375082169929334704723125 785163953430875128567793)
                    ·
                      rfl

theorem cell23_4587304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_4587304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587304 prefixEnd_4587304 := by exact prefixLift 4587304
  have htrace : WordTrace (prefixWord ++ tailWord_4587304) baseStart_4587304 baseEnd_4587304 := by
    simpa [prefixWord, tailWord_4587304, baseEnd_4587304] using wordTrace_append hprefix tailTrace_4587304
  have hstable : (prefixWord ++ tailWord_4587304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587304).length < 2 ^ (prefixWord ++ tailWord_4587304).sum := by decide
  have hdescent : baseEnd_4587304 < baseStart_4587304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587364 : List Nat := [2, 3, 1, 1, 5, 1, 3, 7]
def baseStart_4587364 : Nat := 118140960795 + 4587364 * 2 ^ 59
def prefixEnd_4587364 : Nat := 4983230072969 + 3 ^ 40 * 4587364 * 2
def baseEnd_4587364 : Nat := 87241580338218338924189

theorem tailTrace_4587364 : CollatzResearch.WordTrace tailWord_4587364 prefixEnd_4587364 87241580338218338924189 := by
  unfold tailWord_4587364
  simp only [CollatzResearch.WordTrace]
  refine ⟨83657455276385581120960573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111543273701847441494614097 83657455276385581120960573)
  ·
    refine ⟨31371545728644592920360215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83657455276385581120960573 31371545728644592920360215)
    ·
      refine ⟨47057318592966889380540323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31371545728644592920360215 47057318592966889380540323)
      ·
        refine ⟨70585977889450334070810485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47057318592966889380540323 70585977889450334070810485)
        ·
          refine ⟨6617435427135968819138483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70585977889450334070810485 6617435427135968819138483)
          ·
            refine ⟨9926153140703953228707725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6617435427135968819138483 9926153140703953228707725)
            ·
              refine ⟨3722307427763982460765397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9926153140703953228707725 3722307427763982460765397)
              ·
                refine ⟨87241580338218338924189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3722307427763982460765397 87241580338218338924189)
                ·
                  rfl

theorem cell23_4587364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 7].length) (baseStart_4587364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587364 prefixEnd_4587364 := by exact prefixLift 4587364
  have htrace : WordTrace (prefixWord ++ tailWord_4587364) baseStart_4587364 baseEnd_4587364 := by
    simpa [prefixWord, tailWord_4587364, baseEnd_4587364] using wordTrace_append hprefix tailTrace_4587364
  have hstable : (prefixWord ++ tailWord_4587364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587364).length < 2 ^ (prefixWord ++ tailWord_4587364).sum := by decide
  have hdescent : baseEnd_4587364 < baseStart_4587364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587417 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 3]
def baseStart_4587417 : Nat := 118140960795 + 4587417 * 2 ^ 59
def prefixEnd_4587417 : Nat := 4983230072969 + 3 ^ 40 * 4587417 * 2
def baseEnd_4587417 : Nat := 2355549883606583443590359

theorem tailTrace_4587417 : CollatzResearch.WordTrace tailWord_4587417 prefixEnd_4587417 2355549883606583443590359 := by
  unfold tailWord_4587417
  simp only [CollatzResearch.WordTrace]
  refine ⟨167316843621579152293600505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111544562414386101529067003 167316843621579152293600505)
  ·
    refine ⟨125487632716184364220200379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167316843621579152293600505 125487632716184364220200379)
    ·
      refine ⟨188231449074276546330300569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125487632716184364220200379 188231449074276546330300569)
      ·
        refine ⟨141173586805707409747725427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188231449074276546330300569 141173586805707409747725427)
        ·
          refine ⟨211760380208561114621588141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141173586805707409747725427 211760380208561114621588141)
          ·
            refine ⟨79410142578210417983095553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211760380208561114621588141 79410142578210417983095553)
            ·
              refine ⟨59557606933657813487321665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79410142578210417983095553 59557606933657813487321665)
              ·
                refine ⟨44668205200243360115491249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59557606933657813487321665 44668205200243360115491249)
                ·
                  refine ⟨33501153900182520086618437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44668205200243360115491249 33501153900182520086618437)
                  ·
                    refine ⟨6281466356284222516240957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33501153900182520086618437 6281466356284222516240957)
                    ·
                      refine ⟨2355549883606583443590359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6281466356284222516240957 2355549883606583443590359)
                      ·
                        rfl

theorem cell23_4587417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_4587417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587417 prefixEnd_4587417 := by exact prefixLift 4587417
  have htrace : WordTrace (prefixWord ++ tailWord_4587417) baseStart_4587417 baseEnd_4587417 := by
    simpa [prefixWord, tailWord_4587417, baseEnd_4587417] using wordTrace_append hprefix tailTrace_4587417
  have hstable : (prefixWord ++ tailWord_4587417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587417).length < 2 ^ (prefixWord ++ tailWord_4587417).sum := by decide
  have hdescent : baseEnd_4587417 < baseStart_4587417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587418 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2]
def baseStart_4587418 : Nat := 118140960795 + 4587418 * 2 ^ 59
def prefixEnd_4587418 : Nat := 4983230072969 + 3 ^ 40 * 4587418 * 2
def baseEnd_4587418 : Nat := 2355550397087237939677855

theorem tailTrace_4587418 : CollatzResearch.WordTrace tailWord_4587418 prefixEnd_4587418 2355550397087237939677855 := by
  unfold tailWord_4587418
  simp only [CollatzResearch.WordTrace]
  refine ⟨41829220023643882366096727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111544586729717019642924605 41829220023643882366096727)
  ·
    refine ⟨62743830035465823549145091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41829220023643882366096727 62743830035465823549145091)
    ·
      refine ⟨94115745053198735323717637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62743830035465823549145091 94115745053198735323717637)
      ·
        refine ⟨17646702197474762873197057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94115745053198735323717637 17646702197474762873197057)
        ·
          refine ⟨13235026648106072154897793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17646702197474762873197057 13235026648106072154897793)
          ·
            refine ⟨9926269986079554116173345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13235026648106072154897793 9926269986079554116173345)
            ·
              refine ⟨7444702489559665587130009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9926269986079554116173345 7444702489559665587130009)
              ·
                refine ⟨5583526867169749190347507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7444702489559665587130009 5583526867169749190347507)
                ·
                  refine ⟨8375290300754623785521261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5583526867169749190347507 8375290300754623785521261)
                  ·
                    refine ⟨3140733862782983919570473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8375290300754623785521261 3140733862782983919570473)
                    ·
                      refine ⟨2355550397087237939677855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140733862782983919570473 2355550397087237939677855)
                      ·
                        rfl

theorem cell23_4587418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_4587418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587418 prefixEnd_4587418 := by exact prefixLift 4587418
  have htrace : WordTrace (prefixWord ++ tailWord_4587418) baseStart_4587418 baseEnd_4587418 := by
    simpa [prefixWord, tailWord_4587418, baseEnd_4587418] using wordTrace_append hprefix tailTrace_4587418
  have hstable : (prefixWord ++ tailWord_4587418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587418).length < 2 ^ (prefixWord ++ tailWord_4587418).sum := by decide
  have hdescent : baseEnd_4587418 < baseStart_4587418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587454 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_4587454 : Nat := 118140960795 + 4587454 * 2 ^ 59
def prefixEnd_4587454 : Nat := 4983230072969 + 3 ^ 40 * 4587454 * 2
def baseEnd_4587454 : Nat := 261729875821199977647521

theorem tailTrace_4587454 : CollatzResearch.WordTrace tailWord_4587454 prefixEnd_4587454 261729875821199977647521 := by
  unfold tailWord_4587454
  simp only [CollatzResearch.WordTrace]
  refine ⟨20914774140305638451587177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111545462081630071741798277 20914774140305638451587177)
  ·
    refine ⟨15686080605229228838690383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20914774140305638451587177 15686080605229228838690383)
    ·
      refine ⟨23529120907843843258035575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15686080605229228838690383 23529120907843843258035575)
      ·
        refine ⟨35293681361765764887053363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23529120907843843258035575 35293681361765764887053363)
        ·
          refine ⟨52940522042648647330580045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35293681361765764887053363 52940522042648647330580045)
          ·
            refine ⟨19852695765993242748967517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52940522042648647330580045 19852695765993242748967517)
            ·
              refine ⟨7444760912247466030862819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19852695765993242748967517 7444760912247466030862819)
              ·
                refine ⟨11167141368371199046294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7444760912247466030862819 11167141368371199046294229)
                ·
                  refine ⟨261729875821199977647521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11167141368371199046294229 261729875821199977647521)
                  ·
                    rfl

theorem cell23_4587454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_4587454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587454 prefixEnd_4587454 := by exact prefixLift 4587454
  have htrace : WordTrace (prefixWord ++ tailWord_4587454) baseStart_4587454 baseEnd_4587454 := by
    simpa [prefixWord, tailWord_4587454, baseEnd_4587454] using wordTrace_append hprefix tailTrace_4587454
  have hstable : (prefixWord ++ tailWord_4587454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587454).length < 2 ^ (prefixWord ++ tailWord_4587454).sum := by decide
  have hdescent : baseEnd_4587454 < baseStart_4587454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587467 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 4, 5]
def baseStart_4587467 : Nat := 118140960795 + 4587467 * 2 ^ 59
def prefixEnd_4587467 : Nat := 4983230072969 + 3 ^ 40 * 4587467 * 2
def baseEnd_4587467 : Nat := 785191852546436082655043

theorem tailTrace_4587467 : CollatzResearch.WordTrace tailWord_4587467 prefixEnd_4587467 785191852546436082655043 := by
  unfold tailWord_4587467
  simp only [CollatzResearch.WordTrace]
  refine ⟨167318667271398010832920655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111545778180932007221947103 167318667271398010832920655)
  ·
    refine ⟨250978000907097016249380983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167318667271398010832920655 250978000907097016249380983)
    ·
      refine ⟨376467001360645524374071475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250978000907097016249380983 376467001360645524374071475)
      ·
        refine ⟨564700502040968286561107213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376467001360645524374071475 564700502040968286561107213)
        ·
          refine ⟨211762688265363107460415205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 564700502040968286561107213 211762688265363107460415205)
          ·
            refine ⟨39705504049755582648827851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211762688265363107460415205 39705504049755582648827851)
            ·
              refine ⟨59558256074633373973241777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39705504049755582648827851 59558256074633373973241777)
              ·
                refine ⟨44668692055975030479931333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59558256074633373973241777 44668692055975030479931333)
                ·
                  refine ⟨8375379760495318214987125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44668692055975030479931333 8375379760495318214987125)
                  ·
                    refine ⟨785191852546436082655043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8375379760495318214987125 785191852546436082655043)
                    ·
                      rfl

theorem cell23_4587467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 5].length) (baseStart_4587467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587467 prefixEnd_4587467 := by exact prefixLift 4587467
  have htrace : WordTrace (prefixWord ++ tailWord_4587467) baseStart_4587467 baseEnd_4587467 := by
    simpa [prefixWord, tailWord_4587467, baseEnd_4587467] using wordTrace_append hprefix tailTrace_4587467
  have hstable : (prefixWord ++ tailWord_4587467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587467).length < 2 ^ (prefixWord ++ tailWord_4587467).sum := by decide
  have hdescent : baseEnd_4587467 < baseStart_4587467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587504 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_4587504 : Nat := 118140960795 + 4587504 * 2 ^ 59
def prefixEnd_4587504 : Nat := 4983230072969 + 3 ^ 40 * 4587504 * 2
def baseEnd_4587504 : Nat := 2355594556423524603202459

theorem tailTrace_4587504 : CollatzResearch.WordTrace tailWord_4587504 prefixEnd_4587504 2355594556423524603202459 := by
  unfold tailWord_4587504
  simp only [CollatzResearch.WordTrace]
  refine ⟨83660008386131983076008783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111546677848175977434678377 83660008386131983076008783)
  ·
    refine ⟨125490012579197974614013175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83660008386131983076008783 125490012579197974614013175)
    ·
      refine ⟨188235018868796961921019763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125490012579197974614013175 188235018868796961921019763)
      ·
        refine ⟨282352528303195442881529645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188235018868796961921019763 282352528303195442881529645)
        ·
          refine ⟨105882198113698291080573617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282352528303195442881529645 105882198113698291080573617)
          ·
            refine ⟨79411648585273718310430213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105882198113698291080573617 79411648585273718310430213)
            ·
              refine ⟨14889684109738822183205665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79411648585273718310430213 14889684109738822183205665)
              ·
                refine ⟨11167263082304116637404249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14889684109738822183205665 11167263082304116637404249)
                ·
                  refine ⟨8375447311728087478053187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11167263082304116637404249 8375447311728087478053187)
                  ·
                    refine ⟨12563170967592131217079781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8375447311728087478053187 12563170967592131217079781)
                    ·
                      refine ⟨2355594556423524603202459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12563170967592131217079781 2355594556423524603202459)
                      ·
                        rfl

theorem cell23_4587504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_4587504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587504 prefixEnd_4587504 := by exact prefixLift 4587504
  have htrace : WordTrace (prefixWord ++ tailWord_4587504) baseStart_4587504 baseEnd_4587504 := by
    simpa [prefixWord, tailWord_4587504, baseEnd_4587504] using wordTrace_append hprefix tailTrace_4587504
  have hstable : (prefixWord ++ tailWord_4587504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587504).length < 2 ^ (prefixWord ++ tailWord_4587504).sum := by decide
  have hdescent : baseEnd_4587504 < baseStart_4587504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587505 : List Nat := [1, 2, 2, 2, 6, 1, 2, 2, 5]
def baseStart_4587505 : Nat := 118140960795 + 4587505 * 2 ^ 59
def prefixEnd_4587505 : Nat := 4983230072969 + 3 ^ 40 * 4587505 * 2
def baseEnd_4587505 : Nat := 261732785544908788809995

theorem tailTrace_4587505 : CollatzResearch.WordTrace tailWord_4587505 prefixEnd_4587505 261732785544908788809995 := by
  unfold tailWord_4587505
  simp only [CollatzResearch.WordTrace]
  refine ⟨167320053245260343322803969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111546702163506895548535979 167320053245260343322803969)
  ·
    refine ⟨125490039933945257492102977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167320053245260343322803969 125490039933945257492102977)
    ·
      refine ⟨94117529950458943119077233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125490039933945257492102977 94117529950458943119077233)
      ·
        refine ⟨70588147462844207339307925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94117529950458943119077233 70588147462844207339307925)
        ·
          refine ⟨3308819412320822219030059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70588147462844207339307925 3308819412320822219030059)
          ·
            refine ⟨4963229118481233328545089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308819412320822219030059 4963229118481233328545089)
            ·
              refine ⟨3722421838860924996408817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4963229118481233328545089 3722421838860924996408817)
              ·
                refine ⟨2791816379145693747306613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722421838860924996408817 2791816379145693747306613)
                ·
                  refine ⟨261732785544908788809995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2791816379145693747306613 261732785544908788809995)
                  ·
                    rfl

theorem cell23_4587505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 5].length) (baseStart_4587505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587505 prefixEnd_4587505 := by exact prefixLift 4587505
  have htrace : WordTrace (prefixWord ++ tailWord_4587505) baseStart_4587505 baseEnd_4587505 := by
    simpa [prefixWord, tailWord_4587505, baseEnd_4587505] using wordTrace_append hprefix tailTrace_4587505
  have hstable : (prefixWord ++ tailWord_4587505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587505).length < 2 ^ (prefixWord ++ tailWord_4587505).sum := by decide
  have hdescent : baseEnd_4587505 < baseStart_4587505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587521 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_4587521 : Nat := 118140960795 + 4587521 * 2 ^ 59
def prefixEnd_4587521 : Nat := 4983230072969 + 3 ^ 40 * 4587521 * 2
def baseEnd_4587521 : Nat := 2355603285594651036689881

theorem tailTrace_4587521 : CollatzResearch.WordTrace tailWord_4587521 prefixEnd_4587521 2355603285594651036689881 := by
  unfold tailWord_4587521
  simp only [CollatzResearch.WordTrace]
  refine ⟨167320636813202378055386417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111547091208801585370257611 167320636813202378055386417)
  ·
    refine ⟨125490477609901783541539813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167320636813202378055386417 125490477609901783541539813)
    ·
      refine ⟨23529464551856584414038715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125490477609901783541539813 23529464551856584414038715)
      ·
        refine ⟨35294196827784876621058073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23529464551856584414038715 35294196827784876621058073)
        ·
          refine ⟨26470647620838657465793555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35294196827784876621058073 26470647620838657465793555)
          ·
            refine ⟨39705971431257986198690333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26470647620838657465793555 39705971431257986198690333)
            ·
              refine ⟨14889739286721744824508875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39705971431257986198690333 14889739286721744824508875)
              ·
                refine ⟨22334608930082617236763313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14889739286721744824508875 22334608930082617236763313)
                ·
                  refine ⟨16750956697561962927572485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22334608930082617236763313 16750956697561962927572485)
                  ·
                    refine ⟨3140804380792868048919841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16750956697561962927572485 3140804380792868048919841)
                    ·
                      refine ⟨2355603285594651036689881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140804380792868048919841 2355603285594651036689881)
                      ·
                        rfl

theorem cell23_4587521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_4587521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587521 prefixEnd_4587521 := by exact prefixLift 4587521
  have htrace : WordTrace (prefixWord ++ tailWord_4587521) baseStart_4587521 baseEnd_4587521 := by
    simpa [prefixWord, tailWord_4587521, baseEnd_4587521] using wordTrace_append hprefix tailTrace_4587521
  have hstable : (prefixWord ++ tailWord_4587521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587521).length < 2 ^ (prefixWord ++ tailWord_4587521).sum := by decide
  have hdescent : baseEnd_4587521 < baseStart_4587521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587541 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_4587541 : Nat := 118140960795 + 4587541 * 2 ^ 59
def prefixEnd_4587541 : Nat := 4983230072969 + 3 ^ 40 * 4587541 * 2
def baseEnd_4587541 : Nat := 2355613555207740958439789

theorem tailTrace_4587541 : CollatzResearch.WordTrace tailWord_4587541 prefixEnd_4587541 2355613555207740958439789 := by
  unfold tailWord_4587541
  simp only [CollatzResearch.WordTrace]
  refine ⟨167321366273129921471114477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111547577515419947647409651 167321366273129921471114477)
  ·
    refine ⟨62745512352423720551667929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167321366273129921471114477 62745512352423720551667929)
    ·
      refine ⟨47059134264317790413750947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62745512352423720551667929 47059134264317790413750947)
      ·
        refine ⟨70588701396476685620626421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47059134264317790413750947 70588701396476685620626421)
        ·
          refine ⟨6617690755919689276933727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70588701396476685620626421 6617690755919689276933727)
          ·
            refine ⟨9926536133879533915400591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6617690755919689276933727 9926536133879533915400591)
            ·
              refine ⟨14889804200819300873100887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9926536133879533915400591 14889804200819300873100887)
              ·
                refine ⟨22334706301228951309651331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14889804200819300873100887 22334706301228951309651331)
                ·
                  refine ⟨33502059451843426964476997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22334706301228951309651331 33502059451843426964476997)
                  ·
                    refine ⟨6281636147220642555839437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33502059451843426964476997 6281636147220642555839437)
                    ·
                      refine ⟨2355613555207740958439789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6281636147220642555839437 2355613555207740958439789)
                      ·
                        rfl

theorem cell23_4587541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_4587541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587541 prefixEnd_4587541 := by exact prefixLift 4587541
  have htrace : WordTrace (prefixWord ++ tailWord_4587541) baseStart_4587541 baseEnd_4587541 := by
    simpa [prefixWord, tailWord_4587541, baseEnd_4587541] using wordTrace_append hprefix tailTrace_4587541
  have hstable : (prefixWord ++ tailWord_4587541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587541).length < 2 ^ (prefixWord ++ tailWord_4587541).sum := by decide
  have hdescent : baseEnd_4587541 < baseStart_4587541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587548 : List Nat := [2, 2, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_4587548 : Nat := 118140960795 + 4587548 * 2 ^ 59
def prefixEnd_4587548 : Nat := 4983230072969 + 3 ^ 40 * 4587548 * 2
def baseEnd_4587548 : Nat := 785205716524107477017419

theorem tailTrace_4587548 : CollatzResearch.WordTrace tailWord_4587548 prefixEnd_4587548 785205716524107477017419 := by
  unfold tailWord_4587548
  simp only [CollatzResearch.WordTrace]
  refine ⟨83660810792052280833309649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111547747722736374444412865 83660810792052280833309649)
  ·
    refine ⟨62745608094039210624982237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83660810792052280833309649 62745608094039210624982237)
    ·
      refine ⟨23529603035264703984368339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62745608094039210624982237 23529603035264703984368339)
      ·
        refine ⟨35294404552897055976552509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23529603035264703984368339 35294404552897055976552509)
        ·
          refine ⟨13235401707336395991207191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35294404552897055976552509 13235401707336395991207191)
          ·
            refine ⟨19853102561004593986810787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13235401707336395991207191 19853102561004593986810787)
            ·
              refine ⟨29779653841506890980216181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19853102561004593986810787 29779653841506890980216181)
              ·
                refine ⟨2791842547641271029395267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29779653841506890980216181 2791842547641271029395267)
                ·
                  refine ⟨4187763821461906544092901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791842547641271029395267 4187763821461906544092901)
                  ·
                    refine ⟨785205716524107477017419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4187763821461906544092901 785205716524107477017419)
                    ·
                      rfl

theorem cell23_4587548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_4587548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587548 prefixEnd_4587548 := by exact prefixLift 4587548
  have htrace : WordTrace (prefixWord ++ tailWord_4587548) baseStart_4587548 baseEnd_4587548 := by
    simpa [prefixWord, tailWord_4587548, baseEnd_4587548] using wordTrace_append hprefix tailTrace_4587548
  have hstable : (prefixWord ++ tailWord_4587548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587548).length < 2 ^ (prefixWord ++ tailWord_4587548).sum := by decide
  have hdescent : baseEnd_4587548 < baseStart_4587548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587567 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_4587567 : Nat := 118140960795 + 4587567 * 2 ^ 59
def prefixEnd_4587567 : Nat := 4983230072969 + 3 ^ 40 * 4587567 * 2
def baseEnd_4587567 : Nat := 2355626905704757856714669

theorem tailTrace_4587567 : CollatzResearch.WordTrace tailWord_4587567 prefixEnd_4587567 2355626905704757856714669 := by
  unfold tailWord_4587567
  simp only [CollatzResearch.WordTrace]
  refine ⟨167322314571035727911560955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111548209714023818607707303 167322314571035727911560955)
  ·
    refine ⟨250983471856553591867341433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167322314571035727911560955 250983471856553591867341433)
    ·
      refine ⟨188237603892415193900506075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250983471856553591867341433 188237603892415193900506075)
      ·
        refine ⟨282356405838622790850759113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188237603892415193900506075 282356405838622790850759113)
        ·
          refine ⟨211767304378967093138069335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282356405838622790850759113 211767304378967093138069335)
          ·
            refine ⟨317650956568450639707104003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211767304378967093138069335 317650956568450639707104003)
            ·
              refine ⟨476476434852675959560656005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317650956568450639707104003 476476434852675959560656005)
              ·
                refine ⟨89339331534876742417623001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 476476434852675959560656005 89339331534876742417623001)
                ·
                  refine ⟨67004498651157556813217251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89339331534876742417623001 67004498651157556813217251)
                  ·
                    refine ⟨100506747976736335219825877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67004498651157556813217251 100506747976736335219825877)
                    ·
                      refine ⟨2355626905704757856714669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100506747976736335219825877 2355626905704757856714669)
                      ·
                        rfl

theorem cell23_4587567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_4587567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587567 prefixEnd_4587567 := by exact prefixLift 4587567
  have htrace : WordTrace (prefixWord ++ tailWord_4587567) baseStart_4587567 baseEnd_4587567 := by
    simpa [prefixWord, tailWord_4587567, baseEnd_4587567] using wordTrace_append hprefix tailTrace_4587567
  have hstable : (prefixWord ++ tailWord_4587567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587567).length < 2 ^ (prefixWord ++ tailWord_4587567).sum := by decide
  have hdescent : baseEnd_4587567 < baseStart_4587567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587571 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 3]
def baseStart_4587571 : Nat := 118140960795 + 4587571 * 2 ^ 59
def prefixEnd_4587571 : Nat := 4983230072969 + 3 ^ 40 * 4587571 * 2
def baseEnd_4587571 : Nat := 2355628959627375841064651

theorem tailTrace_4587571 : CollatzResearch.WordTrace tailWord_4587571 prefixEnd_4587571 2355628959627375841064651 := by
  unfold tailWord_4587571
  simp only [CollatzResearch.WordTrace]
  refine ⟨167322460463021236594706567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111548306975347491063137711 167322460463021236594706567)
  ·
    refine ⟨250983690694531854892059851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167322460463021236594706567 250983690694531854892059851)
    ·
      refine ⟨376475536041797782338089777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250983690694531854892059851 376475536041797782338089777)
      ·
        refine ⟨282356652031348336753567333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376475536041797782338089777 282356652031348336753567333)
        ·
          refine ⟨52941872255877813141293875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282356652031348336753567333 52941872255877813141293875)
          ·
            refine ⟨79412808383816719711940813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52941872255877813141293875 79412808383816719711940813)
            ·
              refine ⟨29779803143931269891977805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79412808383816719711940813 29779803143931269891977805)
              ·
                refine ⟨11167426178974226209491677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29779803143931269891977805 11167426178974226209491677)
                ·
                  refine ⟨4187784817115334828559379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11167426178974226209491677 4187784817115334828559379)
                  ·
                    refine ⟨6281677225673002242839069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4187784817115334828559379 6281677225673002242839069)
                    ·
                      refine ⟨2355628959627375841064651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6281677225673002242839069 2355628959627375841064651)
                      ·
                        rfl

theorem cell23_4587571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 3].length) (baseStart_4587571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587571 prefixEnd_4587571 := by exact prefixLift 4587571
  have htrace : WordTrace (prefixWord ++ tailWord_4587571) baseStart_4587571 baseEnd_4587571 := by
    simpa [prefixWord, tailWord_4587571, baseEnd_4587571] using wordTrace_append hprefix tailTrace_4587571
  have hstable : (prefixWord ++ tailWord_4587571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587571).length < 2 ^ (prefixWord ++ tailWord_4587571).sum := by decide
  have hdescent : baseEnd_4587571 < baseStart_4587571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587581 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_4587581 : Nat := 118140960795 + 4587581 * 2 ^ 59
def prefixEnd_4587581 : Nat := 4983230072969 + 3 ^ 40 * 4587581 * 2
def baseEnd_4587581 : Nat := 2355634094433920801939605

theorem tailTrace_4587581 : CollatzResearch.WordTrace tailWord_4587581 prefixEnd_4587581 2355634094433920801939605 := by
  unfold tailWord_4587581
  simp only [CollatzResearch.WordTrace]
  refine ⟨167322825192985008302570597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111548550128656672201713731 167322825192985008302570597)
  ·
    refine ⟨31373029723684689056731987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167322825192985008302570597 31373029723684689056731987)
    ·
      refine ⟨47059544585527033585097981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31373029723684689056731987 47059544585527033585097981)
      ·
        refine ⟨17647329219572637594411743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47059544585527033585097981 17647329219572637594411743)
        ·
          refine ⟨26470993829358956391617615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17647329219572637594411743 26470993829358956391617615)
          ·
            refine ⟨39706490744038434587426423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26470993829358956391617615 39706490744038434587426423)
            ·
              refine ⟨59559736116057651881139635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39706490744038434587426423 59559736116057651881139635)
              ·
                refine ⟨89339604174086477821709453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59559736116057651881139635 89339604174086477821709453)
                ·
                  refine ⟨33502351565282429183141045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89339604174086477821709453 33502351565282429183141045)
                  ·
                    refine ⟨3140845459245227735919473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33502351565282429183141045 3140845459245227735919473)
                    ·
                      refine ⟨2355634094433920801939605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140845459245227735919473 2355634094433920801939605)
                      ·
                        rfl

theorem cell23_4587581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_4587581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587581 prefixEnd_4587581 := by exact prefixLift 4587581
  have htrace : WordTrace (prefixWord ++ tailWord_4587581) baseStart_4587581 baseEnd_4587581 := by
    simpa [prefixWord, tailWord_4587581, baseEnd_4587581] using wordTrace_append hprefix tailTrace_4587581
  have hstable : (prefixWord ++ tailWord_4587581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587581).length < 2 ^ (prefixWord ++ tailWord_4587581).sum := by decide
  have hdescent : baseEnd_4587581 < baseStart_4587581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587591 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 1, 5]
def baseStart_4587591 : Nat := 118140960795 + 4587591 * 2 ^ 59
def prefixEnd_4587591 : Nat := 4983230072969 + 3 ^ 40 * 4587591 * 2
def baseEnd_4587591 : Nat := 785213076413488587604853

theorem tailTrace_4587591 : CollatzResearch.WordTrace tailWord_4587591 prefixEnd_4587591 785213076413488587604853 := by
  unfold tailWord_4587591
  simp only [CollatzResearch.WordTrace]
  refine ⟨167323189922948780010434627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111548793281965853340289751 167323189922948780010434627)
  ·
    refine ⟨250984784884423170015651941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167323189922948780010434627 250984784884423170015651941)
    ·
      refine ⟨47059647165829344377934739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250984784884423170015651941 47059647165829344377934739)
      ·
        refine ⟨70589470748744016566902109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47059647165829344377934739 70589470748744016566902109)
        ·
          refine ⟨26471051530779006212588291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70589470748744016566902109 26471051530779006212588291)
          ·
            refine ⟨39706577296168509318882437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26471051530779006212588291 39706577296168509318882437)
            ·
              refine ⟨7444983243031595497290457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39706577296168509318882437 7444983243031595497290457)
              ·
                refine ⟨5583737432273696622967843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7444983243031595497290457 5583737432273696622967843)
                ·
                  refine ⟨8375606148410544934451765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5583737432273696622967843 8375606148410544934451765)
                  ·
                    refine ⟨785213076413488587604853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8375606148410544934451765 785213076413488587604853)
                    ·
                      rfl

theorem cell23_4587591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_4587591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587591 prefixEnd_4587591 := by exact prefixLift 4587591
  have htrace : WordTrace (prefixWord ++ tailWord_4587591) baseStart_4587591 baseEnd_4587591 := by
    simpa [prefixWord, tailWord_4587591, baseEnd_4587591] using wordTrace_append hprefix tailTrace_4587591
  have hstable : (prefixWord ++ tailWord_4587591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587591).length < 2 ^ (prefixWord ++ tailWord_4587591).sum := by decide
  have hdescent : baseEnd_4587591 < baseStart_4587591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587604 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_4587604 : Nat := 118140960795 + 4587604 * 2 ^ 59
def prefixEnd_4587604 : Nat := 4983230072969 + 3 ^ 40 * 4587604 * 2
def baseEnd_4587604 : Nat := 785215301496324737317333

theorem tailTrace_4587604 : CollatzResearch.WordTrace tailWord_4587604 prefixEnd_4587604 785215301496324737317333 := by
  unfold tailWord_4587604
  simp only [CollatzResearch.WordTrace]
  refine ⟨83661832035950841615328933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111549109381267788820438577 83661832035950841615328933)
  ·
    refine ⟨15686593506740782802874175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83661832035950841615328933 15686593506740782802874175)
    ·
      refine ⟨23529890260111174204311263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15686593506740782802874175 23529890260111174204311263)
      ·
        refine ⟨35294835390166761306466895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23529890260111174204311263 35294835390166761306466895)
        ·
          refine ⟨52942253085250141959700343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35294835390166761306466895 52942253085250141959700343)
          ·
            refine ⟨79413379627875212939550515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52942253085250141959700343 79413379627875212939550515)
            ·
              refine ⟨119120069441812819409325773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79413379627875212939550515 119120069441812819409325773)
              ·
                refine ⟨44670026040679807278497165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119120069441812819409325773 44670026040679807278497165)
                ·
                  refine ⟨16751259765254927729436437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44670026040679807278497165 16751259765254927729436437)
                  ·
                    refine ⟨785215301496324737317333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16751259765254927729436437 785215301496324737317333)
                    ·
                      rfl

theorem cell23_4587604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_4587604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587604 prefixEnd_4587604 := by exact prefixLift 4587604
  have htrace : WordTrace (prefixWord ++ tailWord_4587604) baseStart_4587604 baseEnd_4587604 := by
    simpa [prefixWord, tailWord_4587604, baseEnd_4587604] using wordTrace_append hprefix tailTrace_4587604
  have hstable : (prefixWord ++ tailWord_4587604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587604).length < 2 ^ (prefixWord ++ tailWord_4587604).sum := by decide
  have hdescent : baseEnd_4587604 < baseStart_4587604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587605 : List Nat := [1, 3, 2, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_4587605 : Nat := 118140960795 + 4587605 * 2 ^ 59
def prefixEnd_4587605 : Nat := 4983230072969 + 3 ^ 40 * 4587605 * 2
def baseEnd_4587605 : Nat := 2355646417969628708039495

theorem tailTrace_4587605 : CollatzResearch.WordTrace tailWord_4587605 prefixEnd_4587605 2355646417969628708039495 := by
  unfold tailWord_4587605
  simp only [CollatzResearch.WordTrace]
  refine ⟨167323700544898060401444269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111549133696598706934296179 167323700544898060401444269)
  ·
    refine ⟨62746387704336772650541601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167323700544898060401444269 62746387704336772650541601)
    ·
      refine ⟨47059790778252579487906201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62746387704336772650541601 47059790778252579487906201)
      ·
        refine ⟨35294843083689434615929651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47059790778252579487906201 35294843083689434615929651)
        ·
          refine ⟨52942264625534151923894477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35294843083689434615929651 52942264625534151923894477)
          ·
            refine ⟨19853349234575306971460429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52942264625534151923894477 19853349234575306971460429)
            ·
              refine ⟨7445005962965740114297661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19853349234575306971460429 7445005962965740114297661)
              ·
                refine ⟨2791877236112152542861623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7445005962965740114297661 2791877236112152542861623)
                ·
                  refine ⟨4187815854168228814292435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791877236112152542861623 4187815854168228814292435)
                  ·
                    refine ⟨6281723781252343221438653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4187815854168228814292435 6281723781252343221438653)
                    ·
                      refine ⟨2355646417969628708039495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6281723781252343221438653 2355646417969628708039495)
                      ·
                        rfl

theorem cell23_4587605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_4587605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587605 prefixEnd_4587605 := by exact prefixLift 4587605
  have htrace : WordTrace (prefixWord ++ tailWord_4587605) baseStart_4587605 baseEnd_4587605 := by
    simpa [prefixWord, tailWord_4587605, baseEnd_4587605] using wordTrace_append hprefix tailTrace_4587605
  have hstable : (prefixWord ++ tailWord_4587605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587605).length < 2 ^ (prefixWord ++ tailWord_4587605).sum := by decide
  have hdescent : baseEnd_4587605 < baseStart_4587605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587621 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_4587621 : Nat := 118140960795 + 4587621 * 2 ^ 59
def prefixEnd_4587621 : Nat := 4983230072969 + 3 ^ 40 * 4587621 * 2
def baseEnd_4587621 : Nat := 785218211220033548479807

theorem tailTrace_4587621 : CollatzResearch.WordTrace tailWord_4587621 prefixEnd_4587621 785218211220033548479807 := by
  unfold tailWord_4587621
  simp only [CollatzResearch.WordTrace]
  refine ⟨167324284112840095134026717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111549522741893396756017811 167324284112840095134026717)
  ·
    refine ⟨62746606542315035675260019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167324284112840095134026717 62746606542315035675260019)
    ·
      refine ⟨94119909813472553512890029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62746606542315035675260019 94119909813472553512890029)
      ·
        refine ⟨35294966180052207567333761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94119909813472553512890029 35294966180052207567333761)
        ·
          refine ⟨26471224635039155675500321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35294966180052207567333761 26471224635039155675500321)
          ·
            refine ⟨19853418476279366756625241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26471224635039155675500321 19853418476279366756625241)
            ·
              refine ⟨14890063857209525067468931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19853418476279366756625241 14890063857209525067468931)
              ·
                refine ⟨22335095785814287601203397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14890063857209525067468931 22335095785814287601203397)
                ·
                  refine ⟨4187830459840178925225637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22335095785814287601203397 4187830459840178925225637)
                  ·
                    refine ⟨785218211220033548479807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4187830459840178925225637 785218211220033548479807)
                    ·
                      rfl

theorem cell23_4587621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_4587621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587621 prefixEnd_4587621 := by exact prefixLift 4587621
  have htrace : WordTrace (prefixWord ++ tailWord_4587621) baseStart_4587621 baseEnd_4587621 := by
    simpa [prefixWord, tailWord_4587621, baseEnd_4587621] using wordTrace_append hprefix tailTrace_4587621
  have hstable : (prefixWord ++ tailWord_4587621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587621).length < 2 ^ (prefixWord ++ tailWord_4587621).sum := by decide
  have hdescent : baseEnd_4587621 < baseStart_4587621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587634 : List Nat := [3, 2, 1, 2, 2, 2, 1, 10]
def baseStart_4587634 : Nat := 118140960795 + 4587634 * 2 ^ 59
def prefixEnd_4587634 : Nat := 4983230072969 + 3 ^ 40 * 4587634 * 2
def baseEnd_4587634 : Nat := 87246715144763299799143

theorem tailTrace_4587634 : CollatzResearch.WordTrace tailWord_4587634 prefixEnd_4587634 87246715144763299799143 := by
  unfold tailWord_4587634
  simp only [CollatzResearch.WordTrace]
  refine ⟨41831189565448249588562489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111549838841195332236166637 41831189565448249588562489)
  ·
    refine ⟨31373392174086187191421867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41831189565448249588562489 31373392174086187191421867)
    ·
      refine ⟨47060088261129280787132801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31373392174086187191421867 47060088261129280787132801)
      ·
        refine ⟨35295066195846960590349601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47060088261129280787132801 35295066195846960590349601)
        ·
          refine ⟨26471299646885220442762201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35295066195846960590349601 26471299646885220442762201)
          ·
            refine ⟨19853474735163915332071651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26471299646885220442762201 19853474735163915332071651)
            ·
              refine ⟨29780212102745872998107477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19853474735163915332071651 29780212102745872998107477)
              ·
                refine ⟨87246715144763299799143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29780212102745872998107477 87246715144763299799143)
                ·
                  rfl

theorem cell23_4587634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 10].length) (baseStart_4587634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587634 prefixEnd_4587634 := by exact prefixLift 4587634
  have htrace : WordTrace (prefixWord ++ tailWord_4587634) baseStart_4587634 baseEnd_4587634 := by
    simpa [prefixWord, tailWord_4587634, baseEnd_4587634] using wordTrace_append hprefix tailTrace_4587634
  have hstable : (prefixWord ++ tailWord_4587634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587634).length < 2 ^ (prefixWord ++ tailWord_4587634).sum := by decide
  have hdescent : baseEnd_4587634 < baseStart_4587634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587668 : List Nat := [2, 4, 2, 3, 2, 10]
def baseStart_4587668 : Nat := 118140960795 + 4587668 * 2 ^ 59
def prefixEnd_4587668 : Nat := 4983230072969 + 3 ^ 40 * 4587668 * 2
def baseEnd_4587668 : Nat := 9694151305559102722435

theorem tailTrace_4587668 : CollatzResearch.WordTrace tailWord_4587668 prefixEnd_4587668 9694151305559102722435 := by
  unfold tailWord_4587668
  simp only [CollatzResearch.WordTrace]
  refine ⟨83662999171834911080493829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111550665562446548107325105 83662999171834911080493829)
  ·
    refine ⟨15686812344719045827592593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83662999171834911080493829 15686812344719045827592593)
    ·
      refine ⟨11765109258539284370694445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15686812344719045827592593 11765109258539284370694445)
      ·
        refine ⟨4411915971952231639010417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11765109258539284370694445 4411915971952231639010417)
        ·
          refine ⟨3308936978964173729257813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4411915971952231639010417 3308936978964173729257813)
          ·
            refine ⟨9694151305559102722435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3308936978964173729257813 9694151305559102722435)
            ·
              rfl

theorem cell23_4587668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 10].length) (baseStart_4587668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587668 prefixEnd_4587668 := by exact prefixLift 4587668
  have htrace : WordTrace (prefixWord ++ tailWord_4587668) baseStart_4587668 baseEnd_4587668 := by
    simpa [prefixWord, tailWord_4587668, baseEnd_4587668] using wordTrace_append hprefix tailTrace_4587668
  have hstable : (prefixWord ++ tailWord_4587668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587668).length < 2 ^ (prefixWord ++ tailWord_4587668).sum := by decide
  have hdescent : baseEnd_4587668 < baseStart_4587668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587679 : List Nat := [1, 1, 2, 6, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4587679 : Nat := 118140960795 + 4587679 * 2 ^ 59
def prefixEnd_4587679 : Nat := 4983230072969 + 3 ^ 40 * 4587679 * 2
def baseEnd_4587679 : Nat := 2355684415538061418514155

theorem tailTrace_4587679 : CollatzResearch.WordTrace tailWord_4587679 prefixEnd_4587679 2355684415538061418514155 := by
  unfold tailWord_4587679
  simp only [CollatzResearch.WordTrace]
  refine ⟨167326399546629971039638091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111550933031086647359758727 167326399546629971039638091)
  ·
    refine ⟨250989599319944956559457137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167326399546629971039638091 250989599319944956559457137)
    ·
      refine ⟨188242199489958717419592853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250989599319944956559457137 188242199489958717419592853)
      ·
        refine ⟨8823853101091814879043415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 188242199489958717419592853 8823853101091814879043415)
        ·
          refine ⟨13235779651637722318565123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8823853101091814879043415 13235779651637722318565123)
          ·
            refine ⟨19853669477456583477847685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13235779651637722318565123 19853669477456583477847685)
            ·
              refine ⟨3722563027023109402096441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19853669477456583477847685 3722563027023109402096441)
              ·
                refine ⟨2791922270267332051572331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722563027023109402096441 2791922270267332051572331)
                ·
                  refine ⟨4187883405400998077358497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791922270267332051572331 4187883405400998077358497)
                  ·
                    refine ⟨3140912554050748558018873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4187883405400998077358497 3140912554050748558018873)
                    ·
                      refine ⟨2355684415538061418514155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3140912554050748558018873 2355684415538061418514155)
                      ·
                        rfl

theorem cell23_4587679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4587679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587679 prefixEnd_4587679 := by exact prefixLift 4587679
  have htrace : WordTrace (prefixWord ++ tailWord_4587679) baseStart_4587679 baseEnd_4587679 := by
    simpa [prefixWord, tailWord_4587679, baseEnd_4587679] using wordTrace_append hprefix tailTrace_4587679
  have hstable : (prefixWord ++ tailWord_4587679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587679).length < 2 ^ (prefixWord ++ tailWord_4587679).sum := by decide
  have hdescent : baseEnd_4587679 < baseStart_4587679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587746 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4587746 : Nat := 118140960795 + 4587746 * 2 ^ 59
def prefixEnd_4587746 : Nat := 4983230072969 + 3 ^ 40 * 4587746 * 2
def baseEnd_4587746 : Nat := 2355718818741912656376347

theorem tailTrace_4587746 : CollatzResearch.WordTrace tailWord_4587746 prefixEnd_4587746 2355718818741912656376347 := by
  unfold tailWord_4587746
  simp only [CollatzResearch.WordTrace]
  refine ⟨41832210809346810370581773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111552562158258160988218061 41832210809346810370581773)
  ·
    refine ⟨15687079053505053888968165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41832210809346810370581773 15687079053505053888968165)
    ·
      refine ⟨2941327322532197604181531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15687079053505053888968165 2941327322532197604181531)
      ·
        refine ⟨4411990983798296406272297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2941327322532197604181531 4411990983798296406272297)
        ·
          refine ⟨3308993237848722304704223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4411990983798296406272297 3308993237848722304704223)
          ·
            refine ⟨4963489856773083457056335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308993237848722304704223 4963489856773083457056335)
            ·
              refine ⟨7445234785159625185584503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4963489856773083457056335 7445234785159625185584503)
              ·
                refine ⟨11167852177739437778376755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7445234785159625185584503 11167852177739437778376755)
                ·
                  refine ⟨16751778266609156667565133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11167852177739437778376755 16751778266609156667565133)
                  ·
                    refine ⟨6281916849978433750336925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16751778266609156667565133 6281916849978433750336925)
                    ·
                      refine ⟨2355718818741912656376347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6281916849978433750336925 2355718818741912656376347)
                      ·
                        rfl

theorem cell23_4587746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4587746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587746 prefixEnd_4587746 := by exact prefixLift 4587746
  have htrace : WordTrace (prefixWord ++ tailWord_4587746) baseStart_4587746 baseEnd_4587746 := by
    simpa [prefixWord, tailWord_4587746, baseEnd_4587746] using wordTrace_append hprefix tailTrace_4587746
  have hstable : (prefixWord ++ tailWord_4587746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587746).length < 2 ^ (prefixWord ++ tailWord_4587746).sum := by decide
  have hdescent : baseEnd_4587746 < baseStart_4587746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587822 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4587822 : Nat := 118140960795 + 4587822 * 2 ^ 59
def prefixEnd_4587822 : Nat := 4983230072969 + 3 ^ 40 * 4587822 * 2
def baseEnd_4587822 : Nat := 785252614423884786341999

theorem tailTrace_4587822 : CollatzResearch.WordTrace tailWord_4587822 prefixEnd_4587822 785252614423884786341999 := by
  unfold tailWord_4587822
  simp only [CollatzResearch.WordTrace]
  refine ⟨20916451898138988307761715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111554410123407937641395813 20916451898138988307761715)
  ·
    refine ⟨31374677847208482461642573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20916451898138988307761715 31374677847208482461642573)
    ·
      refine ⟨11765504192703180923115965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31374677847208482461642573 11765504192703180923115965)
      ·
        refine ⟨4412064072263692846168487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11765504192703180923115965 4412064072263692846168487)
        ·
          refine ⟨6618096108395539269252731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4412064072263692846168487 6618096108395539269252731)
          ·
            refine ⟨9927144162593308903879097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618096108395539269252731 9927144162593308903879097)
            ·
              refine ⟨7445358121944981677909323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9927144162593308903879097 7445358121944981677909323)
              ·
                refine ⟨11168037182917472516863985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7445358121944981677909323 11168037182917472516863985)
                ·
                  refine ⟨8376027887188104387647989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11168037182917472516863985 8376027887188104387647989)
                  ·
                    refine ⟨785252614423884786341999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8376027887188104387647989 785252614423884786341999)
                    ·
                      rfl

theorem cell23_4587822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4587822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587822 prefixEnd_4587822 := by exact prefixLift 4587822
  have htrace : WordTrace (prefixWord ++ tailWord_4587822) baseStart_4587822 baseEnd_4587822 := by
    simpa [prefixWord, tailWord_4587822, baseEnd_4587822] using wordTrace_append hprefix tailTrace_4587822
  have hstable : (prefixWord ++ tailWord_4587822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587822).length < 2 ^ (prefixWord ++ tailWord_4587822).sum := by decide
  have hdescent : baseEnd_4587822 < baseStart_4587822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587825 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_4587825 : Nat := 118140960795 + 4587825 * 2 ^ 59
def prefixEnd_4587825 : Nat := 4983230072969 + 3 ^ 40 * 4587825 * 2
def baseEnd_4587825 : Nat := 2355759383713617847288483

theorem tailTrace_4587825 : CollatzResearch.WordTrace tailWord_4587825 prefixEnd_4587825 2355759383713617847288483 := by
  unfold tailWord_4587825
  simp only [CollatzResearch.WordTrace]
  refine ⟨167331724604101037974452929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111554483069400691982968619 167331724604101037974452929)
  ·
    refine ⟨125498793453075778480839697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167331724604101037974452929 125498793453075778480839697)
    ·
      refine ⟨94124095089806833860629773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125498793453075778480839697 94124095089806833860629773)
      ·
        refine ⟨35296535658677562697736165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94124095089806833860629773 35296535658677562697736165)
        ·
          refine ⟨6618100436002043005825531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35296535658677562697736165 6618100436002043005825531)
          ·
            refine ⟨9927150654003064508738297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618100436002043005825531 9927150654003064508738297)
            ·
              refine ⟨7445362990502298381553723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9927150654003064508738297 7445362990502298381553723)
              ·
                refine ⟨11168044485753447572330585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7445362990502298381553723 11168044485753447572330585)
                ·
                  refine ⟨8376033364315085679247939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11168044485753447572330585 8376033364315085679247939)
                  ·
                    refine ⟨12564050046472628518871909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8376033364315085679247939 12564050046472628518871909)
                    ·
                      refine ⟨2355759383713617847288483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12564050046472628518871909 2355759383713617847288483)
                      ·
                        rfl

theorem cell23_4587825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_4587825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587825 prefixEnd_4587825 := by exact prefixLift 4587825
  have htrace : WordTrace (prefixWord ++ tailWord_4587825) baseStart_4587825 baseEnd_4587825 := by
    simpa [prefixWord, tailWord_4587825, baseEnd_4587825] using wordTrace_append hprefix tailTrace_4587825
  have hstable : (prefixWord ++ tailWord_4587825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587825).length < 2 ^ (prefixWord ++ tailWord_4587825).sum := by decide
  have hdescent : baseEnd_4587825 < baseStart_4587825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587875 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 3]
def baseStart_4587875 : Nat := 118140960795 + 4587875 * 2 ^ 59
def prefixEnd_4587875 : Nat := 4983230072969 + 3 ^ 40 * 4587875 * 2
def baseEnd_4587875 : Nat := 2355785057746342651663253

theorem tailTrace_4587875 : CollatzResearch.WordTrace tailWord_4587875 prefixEnd_4587875 2355785057746342651663253 := by
  unfold tailWord_4587875
  simp only [CollatzResearch.WordTrace]
  refine ⟨167333548253919896513773079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111555698835946597675848719 167333548253919896513773079)
  ·
    refine ⟨251000322380879844770659619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167333548253919896513773079 251000322380879844770659619)
    ·
      refine ⟨376500483571319767155989429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251000322380879844770659619 376500483571319767155989429)
      ·
        refine ⟨35296920334811228170874009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 376500483571319767155989429 35296920334811228170874009)
        ·
          refine ⟨26472690251108421128155507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35296920334811228170874009 26472690251108421128155507)
          ·
            refine ⟨39709035376662631692233261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26472690251108421128155507 39709035376662631692233261)
            ·
              refine ⟨14890888266248486884587473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39709035376662631692233261 14890888266248486884587473)
              ·
                refine ⟨11168166199686365163440605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14890888266248486884587473 11168166199686365163440605)
                ·
                  refine ⟨4188062324882386936290227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11168166199686365163440605 4188062324882386936290227)
                  ·
                    refine ⟨6282093487323580404435341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4188062324882386936290227 6282093487323580404435341)
                    ·
                      refine ⟨2355785057746342651663253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282093487323580404435341 2355785057746342651663253)
                      ·
                        rfl

theorem cell23_4587875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_4587875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587875 prefixEnd_4587875 := by exact prefixLift 4587875
  have htrace : WordTrace (prefixWord ++ tailWord_4587875) baseStart_4587875 baseEnd_4587875 := by
    simpa [prefixWord, tailWord_4587875, baseEnd_4587875] using wordTrace_append hprefix tailTrace_4587875
  have hstable : (prefixWord ++ tailWord_4587875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587875).length < 2 ^ (prefixWord ++ tailWord_4587875).sum := by decide
  have hdescent : baseEnd_4587875 < baseStart_4587875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587885 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_4587885 : Nat := 118140960795 + 4587885 * 2 ^ 59
def prefixEnd_4587885 : Nat := 4983230072969 + 3 ^ 40 * 4587885 * 2
def baseEnd_4587885 : Nat := 2355790192552887612538207

theorem tailTrace_4587885 : CollatzResearch.WordTrace tailWord_4587885 prefixEnd_4587885 2355790192552887612538207 := by
  unfold tailWord_4587885
  simp only [CollatzResearch.WordTrace]
  refine ⟨167333912983883668221637109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111555941989255778814424739 167333912983883668221637109)
  ·
    refine ⟨15687554342239093895778479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167333912983883668221637109 15687554342239093895778479)
    ·
      refine ⟨23531331513358640843667719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15687554342239093895778479 23531331513358640843667719)
      ·
        refine ⟨35296997270037961265501579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23531331513358640843667719 35296997270037961265501579)
        ·
          refine ⟨52945495905056941898252369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35296997270037961265501579 52945495905056941898252369)
          ·
            refine ⟨39709121928792706423689277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52945495905056941898252369 39709121928792706423689277)
            ·
              refine ⟨14890920723297264908883479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39709121928792706423689277 14890920723297264908883479)
              ·
                refine ⟨22336381084945897363325219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14890920723297264908883479 22336381084945897363325219)
                ·
                  refine ⟨33504571627418846044987829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22336381084945897363325219 33504571627418846044987829)
                  ·
                    refine ⟨3141053590070516816717609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33504571627418846044987829 3141053590070516816717609)
                    ·
                      refine ⟨2355790192552887612538207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141053590070516816717609 2355790192552887612538207)
                      ·
                        rfl

theorem cell23_4587885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_4587885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587885 prefixEnd_4587885 := by exact prefixLift 4587885
  have htrace : WordTrace (prefixWord ++ tailWord_4587885) baseStart_4587885 baseEnd_4587885 := by
    simpa [prefixWord, tailWord_4587885, baseEnd_4587885] using wordTrace_append hprefix tailTrace_4587885
  have hstable : (prefixWord ++ tailWord_4587885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587885).length < 2 ^ (prefixWord ++ tailWord_4587885).sum := by decide
  have hdescent : baseEnd_4587885 < baseStart_4587885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587938 : List Nat := [3, 3, 1, 2, 1, 1, 3, 9]
def baseStart_4587938 : Nat := 118140960795 + 4587938 * 2 ^ 59
def prefixEnd_4587938 : Nat := 4983230072969 + 3 ^ 40 * 4587938 * 2
def baseEnd_4587938 : Nat := 87252496556576885376869

theorem tailTrace_4587938 : CollatzResearch.WordTrace tailWord_4587938 prefixEnd_4587938 87252496556576885376869 := by
  unfold tailWord_4587938
  simp only [CollatzResearch.WordTrace]
  refine ⟨41833961513172914568329117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111557230701794438848877645 41833961513172914568329117)
  ·
    refine ⟨15687735567439842963123419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41833961513172914568329117 15687735567439842963123419)
    ·
      refine ⟨23531603351159764444685129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15687735567439842963123419 23531603351159764444685129)
      ·
        refine ⟨17648702513369823333513847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23531603351159764444685129 17648702513369823333513847)
        ·
          refine ⟨26473053770054735000270771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17648702513369823333513847 26473053770054735000270771)
          ·
            refine ⟨39709580655082102500406157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26473053770054735000270771 39709580655082102500406157)
            ·
              refine ⟨14891092745655788437652309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39709580655082102500406157 14891092745655788437652309)
              ·
                refine ⟨87252496556576885376869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14891092745655788437652309 87252496556576885376869)
                ·
                  rfl

theorem cell23_4587938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 9].length) (baseStart_4587938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587938 prefixEnd_4587938 := by exact prefixLift 4587938
  have htrace : WordTrace (prefixWord ++ tailWord_4587938) baseStart_4587938 baseEnd_4587938 := by
    simpa [prefixWord, tailWord_4587938, baseEnd_4587938] using wordTrace_append hprefix tailTrace_4587938
  have hstable : (prefixWord ++ tailWord_4587938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587938).length < 2 ^ (prefixWord ++ tailWord_4587938).sum := by decide
  have hdescent : baseEnd_4587938 < baseStart_4587938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587948 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_4587948 : Nat := 118140960795 + 4587948 * 2 ^ 59
def prefixEnd_4587948 : Nat := 4983230072969 + 3 ^ 40 * 4587948 * 2
def baseEnd_4587948 : Nat := 2355822541834120866050417

theorem tailTrace_4587948 : CollatzResearch.WordTrace tailWord_4587948 prefixEnd_4587948 2355822541834120866050417 := by
  unfold tailWord_4587948
  simp only [CollatzResearch.WordTrace]
  refine ⟨83668105391327714990590249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111557473855103619987453665 83668105391327714990590249)
  ·
    refine ⟨62751079043495786242942687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83668105391327714990590249 62751079043495786242942687)
    ·
      refine ⟨94126618565243679364414031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62751079043495786242942687 94126618565243679364414031)
      ·
        refine ⟨141189927847865519046621047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94126618565243679364414031 141189927847865519046621047)
        ·
          refine ⟨211784891771798278569931571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141189927847865519046621047 211784891771798278569931571)
          ·
            refine ⟨317677337657697417854897357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211784891771798278569931571 317677337657697417854897357)
            ·
              refine ⟨119129001621636531695586509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317677337657697417854897357 119129001621636531695586509)
              ·
                refine ⟨44673375608113699385844941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119129001621636531695586509 44673375608113699385844941)
                ·
                  refine ⟨16752515853042637269691853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44673375608113699385844941 16752515853042637269691853)
                  ·
                    refine ⟨6282193444890988976134445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16752515853042637269691853 6282193444890988976134445)
                    ·
                      refine ⟨2355822541834120866050417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282193444890988976134445 2355822541834120866050417)
                      ·
                        rfl

theorem cell23_4587948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_4587948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587948 prefixEnd_4587948 := by exact prefixLift 4587948
  have htrace : WordTrace (prefixWord ++ tailWord_4587948) baseStart_4587948 baseEnd_4587948 := by
    simpa [prefixWord, tailWord_4587948, baseEnd_4587948] using wordTrace_append hprefix tailTrace_4587948
  have hstable : (prefixWord ++ tailWord_4587948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587948).length < 2 ^ (prefixWord ++ tailWord_4587948).sum := by decide
  have hdescent : baseEnd_4587948 < baseStart_4587948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587951 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 3, 9]
def baseStart_4587951 : Nat := 118140960795 + 4587951 * 2 ^ 59
def prefixEnd_4587951 : Nat := 4983230072969 + 3 ^ 40 * 4587951 * 2
def baseEnd_4587951 : Nat := 785274694092028118104301

theorem tailTrace_4587951 : CollatzResearch.WordTrace tailWord_4587951 prefixEnd_4587951 785274694092028118104301 := by
  unfold tailWord_4587951
  simp only [CollatzResearch.WordTrace]
  refine ⟨167336320201644561493539707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111557546801096374329026471 167336320201644561493539707)
  ·
    refine ⟨251004480302466842240309561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167336320201644561493539707 251004480302466842240309561)
    ·
      refine ⟨188253360226850131680232171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251004480302466842240309561 188253360226850131680232171)
      ·
        refine ⟨282380040340275197520348257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188253360226850131680232171 282380040340275197520348257)
        ·
          refine ⟨211785030255206398140261193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282380040340275197520348257 211785030255206398140261193)
          ·
            refine ⟨158838772691404798605195895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211785030255206398140261193 158838772691404798605195895)
            ·
              refine ⟨238258159037107197907793843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158838772691404798605195895 238258159037107197907793843)
              ·
                refine ⟨357387238555660796861690765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238258159037107197907793843 357387238555660796861690765)
                ·
                  refine ⟨134020214458372798823134037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357387238555660796861690765 134020214458372798823134037)
                  ·
                    refine ⟨785274694092028118104301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 134020214458372798823134037 785274694092028118104301)
                    ·
                      rfl

theorem cell23_4587951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_4587951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587951 prefixEnd_4587951 := by exact prefixLift 4587951
  have htrace : WordTrace (prefixWord ++ tailWord_4587951) baseStart_4587951 baseEnd_4587951 := by
    simpa [prefixWord, tailWord_4587951, baseEnd_4587951] using wordTrace_append hprefix tailTrace_4587951
  have hstable : (prefixWord ++ tailWord_4587951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587951).length < 2 ^ (prefixWord ++ tailWord_4587951).sum := by decide
  have hdescent : baseEnd_4587951 < baseStart_4587951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4587986 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4587986 : Nat := 118140960795 + 4587986 * 2 ^ 59
def prefixEnd_4587986 : Nat := 4983230072969 + 3 ^ 40 * 4587986 * 2
def baseEnd_4587986 : Nat := 2355842054098991717375243

theorem tailTrace_4587986 : CollatzResearch.WordTrace tailWord_4587986 prefixEnd_4587986 2355842054098991717375243 := by
  unfold tailWord_4587986
  simp only [CollatzResearch.WordTrace]
  refine ⟨41834399189129440617765953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111558397837678508314042541 41834399189129440617765953)
  ·
    refine ⟨31375799391847080463324465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41834399189129440617765953 31375799391847080463324465)
    ·
      refine ⟨23531849543885310347493349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31375799391847080463324465 23531849543885310347493349)
      ·
        refine ⟨4412221789478495690155003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23531849543885310347493349 4412221789478495690155003)
        ·
          refine ⟨6618332684217743535232505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4412221789478495690155003 6618332684217743535232505)
          ·
            refine ⟨4963749513163307651424379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6618332684217743535232505 4963749513163307651424379)
            ·
              refine ⟨7445624269744961477136569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4963749513163307651424379 7445624269744961477136569)
              ·
                refine ⟨5584218202308721107852427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7445624269744961477136569 5584218202308721107852427)
                ·
                  refine ⟨8376327303463081661778641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5584218202308721107852427 8376327303463081661778641)
                  ·
                    refine ⟨6282245477597311246333981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8376327303463081661778641 6282245477597311246333981)
                    ·
                      refine ⟨2355842054098991717375243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282245477597311246333981 2355842054098991717375243)
                      ·
                        rfl

theorem cell23_4587986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4587986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4587986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4587986 prefixEnd_4587986 := by exact prefixLift 4587986
  have htrace : WordTrace (prefixWord ++ tailWord_4587986) baseStart_4587986 baseEnd_4587986 := by
    simpa [prefixWord, tailWord_4587986, baseEnd_4587986] using wordTrace_append hprefix tailTrace_4587986
  have hstable : (prefixWord ++ tailWord_4587986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4587986).length < 2 ^ (prefixWord ++ tailWord_4587986).sum := by decide
  have hdescent : baseEnd_4587986 < baseStart_4587986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4587986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588022 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_4588022 : Nat := 118140960795 + 4588022 * 2 ^ 59
def prefixEnd_4588022 : Nat := 4983230072969 + 3 ^ 40 * 4588022 * 2
def baseEnd_4588022 : Nat := 2355860539402553576525077

theorem tailTrace_4588022 : CollatzResearch.WordTrace tailWord_4588022 prefixEnd_4588022 2355860539402553576525077 := by
  unfold tailWord_4588022
  simp only [CollatzResearch.WordTrace]
  refine ⟨10458681861524208788710895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111559273189591560412916213 10458681861524208788710895)
  ·
    refine ⟨15688022792286313183066343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10458681861524208788710895 15688022792286313183066343)
    ·
      refine ⟨23532034188429469774599515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15688022792286313183066343 23532034188429469774599515)
      ·
        refine ⟨35298051282644204661899273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23532034188429469774599515 35298051282644204661899273)
        ·
          refine ⟨26473538461983153496424455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35298051282644204661899273 26473538461983153496424455)
          ·
            refine ⟨39710307692974730244636683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26473538461983153496424455 39710307692974730244636683)
            ·
              refine ⟨59565461539462095366955025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39710307692974730244636683 59565461539462095366955025)
              ·
                refine ⟨44674096154596571525216269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59565461539462095366955025 44674096154596571525216269)
                ·
                  refine ⟨16752786057973714321956101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44674096154596571525216269 16752786057973714321956101)
                  ·
                    refine ⟨3141147385870071435366769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16752786057973714321956101 3141147385870071435366769)
                    ·
                      refine ⟨2355860539402553576525077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141147385870071435366769 2355860539402553576525077)
                      ·
                        rfl

theorem cell23_4588022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_4588022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588022 prefixEnd_4588022 := by exact prefixLift 4588022
  have htrace : WordTrace (prefixWord ++ tailWord_4588022) baseStart_4588022 baseEnd_4588022 := by
    simpa [prefixWord, tailWord_4588022, baseEnd_4588022] using wordTrace_append hprefix tailTrace_4588022
  have hstable : (prefixWord ++ tailWord_4588022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588022).length < 2 ^ (prefixWord ++ tailWord_4588022).sum := by decide
  have hdescent : baseEnd_4588022 < baseStart_4588022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588028 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 7]
def baseStart_4588028 : Nat := 118140960795 + 4588028 * 2 ^ 59
def prefixEnd_4588028 : Nat := 4983230072969 + 3 ^ 40 * 4588028 * 2
def baseEnd_4588028 : Nat := 261762624476275617005561

theorem tailTrace_4588028 : CollatzResearch.WordTrace tailWord_4588028 prefixEnd_4588028 261762624476275617005561 := by
  unfold tailWord_4588028
  simp only [CollatzResearch.WordTrace]
  refine ⟨83669564311182801822046369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111559419081577069096061825 83669564311182801822046369)
  ·
    refine ⟨62752173233387101366534777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83669564311182801822046369 62752173233387101366534777)
    ·
      refine ⟨47064129925040326024901083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62752173233387101366534777 47064129925040326024901083)
      ·
        refine ⟨70596194887560489037351625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47064129925040326024901083 70596194887560489037351625)
        ·
          refine ⟨52947146165670366778013719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70596194887560489037351625 52947146165670366778013719)
          ·
            refine ⟨79420719248505550167020579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52947146165670366778013719 79420719248505550167020579)
            ·
              refine ⟨119131078872758325250530869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79420719248505550167020579 119131078872758325250530869)
              ·
                refine ⟨11168538644321092992237269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119131078872758325250530869 11168538644321092992237269)
                ·
                  refine ⟨261762624476275617005561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11168538644321092992237269 261762624476275617005561)
                  ·
                    rfl

theorem cell23_4588028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_4588028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588028 prefixEnd_4588028 := by exact prefixLift 4588028
  have htrace : WordTrace (prefixWord ++ tailWord_4588028) baseStart_4588028 baseEnd_4588028 := by
    simpa [prefixWord, tailWord_4588028, baseEnd_4588028] using wordTrace_append hprefix tailTrace_4588028
  have hstable : (prefixWord ++ tailWord_4588028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588028).length < 2 ^ (prefixWord ++ tailWord_4588028).sum := by decide
  have hdescent : baseEnd_4588028 < baseStart_4588028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588039 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_4588039 : Nat := 118140960795 + 4588039 * 2 ^ 59
def prefixEnd_4588039 : Nat := 4983230072969 + 3 ^ 40 * 4588039 * 2
def baseEnd_4588039 : Nat := 2355869268573680010012499

theorem tailTrace_4588039 : CollatzResearch.WordTrace tailWord_4588039 prefixEnd_4588039 2355869268573680010012499 := by
  unfold tailWord_4588039
  simp only [CollatzResearch.WordTrace]
  refine ⟨167339529825325752522743171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111559686550217168348495447 167339529825325752522743171)
  ·
    refine ⟨251009294737988628784114757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167339529825325752522743171 251009294737988628784114757)
    ·
      refine ⟨47064242763372867897021517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251009294737988628784114757 47064242763372867897021517)
      ·
        refine ⟨17649091036264825461383069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47064242763372867897021517 17649091036264825461383069)
        ·
          refine ⟨6618409138599309548018651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17649091036264825461383069 6618409138599309548018651)
          ·
            refine ⟨9927613707898964322027977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618409138599309548018651 9927613707898964322027977)
            ·
              refine ⟨7445710280924223241520983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9927613707898964322027977 7445710280924223241520983)
              ·
                refine ⟨11168565421386334862281475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7445710280924223241520983 11168565421386334862281475)
                ·
                  refine ⟨16752848132079502293422213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11168565421386334862281475 16752848132079502293422213)
                  ·
                    refine ⟨3141159024764906680016665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16752848132079502293422213 3141159024764906680016665)
                    ·
                      refine ⟨2355869268573680010012499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141159024764906680016665 2355869268573680010012499)
                      ·
                        rfl

theorem cell23_4588039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_4588039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588039 prefixEnd_4588039 := by exact prefixLift 4588039
  have htrace : WordTrace (prefixWord ++ tailWord_4588039) baseStart_4588039 baseEnd_4588039 := by
    simpa [prefixWord, tailWord_4588039, baseEnd_4588039] using wordTrace_append hprefix tailTrace_4588039
  have hstable : (prefixWord ++ tailWord_4588039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588039).length < 2 ^ (prefixWord ++ tailWord_4588039).sum := by decide
  have hdescent : baseEnd_4588039 < baseStart_4588039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588072 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4588072 : Nat := 118140960795 + 4588072 * 2 ^ 59
def prefixEnd_4588072 : Nat := 4983230072969 + 3 ^ 40 * 4588072 * 2
def baseEnd_4588072 : Nat := 2355886213435278380899847

theorem tailTrace_4588072 : CollatzResearch.WordTrace tailWord_4588072 prefixEnd_4588072 2355886213435278380899847 := by
  unfold tailWord_4588072
  simp only [CollatzResearch.WordTrace]
  refine ⟨83670366717103099579347235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111560488956137466105796313 83670366717103099579347235)
  ·
    refine ⟨125505550075654649369020853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83670366717103099579347235 125505550075654649369020853)
    ·
      refine ⟨11766145319592623378345705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125505550075654649369020853 11766145319592623378345705)
      ·
        refine ⟨8824608989694467533759279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11766145319592623378345705 8824608989694467533759279)
        ·
          refine ⟨13236913484541701300638919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8824608989694467533759279 13236913484541701300638919)
          ·
            refine ⟨19855370226812551950958379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13236913484541701300638919 19855370226812551950958379)
            ·
              refine ⟨29783055340218827926437569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19855370226812551950958379 29783055340218827926437569)
              ·
                refine ⟨22337291505164120944828177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29783055340218827926437569 22337291505164120944828177)
                ·
                  refine ⟨16752968628873090708621133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22337291505164120944828177 16752968628873090708621133)
                  ·
                    refine ⟨6282363235827409015732925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16752968628873090708621133 6282363235827409015732925)
                    ·
                      refine ⟨2355886213435278380899847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282363235827409015732925 2355886213435278380899847)
                      ·
                        rfl

theorem cell23_4588072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4588072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588072 prefixEnd_4588072 := by exact prefixLift 4588072
  have htrace : WordTrace (prefixWord ++ tailWord_4588072) baseStart_4588072 baseEnd_4588072 := by
    simpa [prefixWord, tailWord_4588072, baseEnd_4588072] using wordTrace_append hprefix tailTrace_4588072
  have hstable : (prefixWord ++ tailWord_4588072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588072).length < 2 ^ (prefixWord ++ tailWord_4588072).sum := by decide
  have hdescent : baseEnd_4588072 < baseStart_4588072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588132 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_4588132 : Nat := 118140960795 + 4588132 * 2 ^ 59
def prefixEnd_4588132 : Nat := 4983230072969 + 3 ^ 40 * 4588132 * 2
def baseEnd_4588132 : Nat := 2355917022274548146149571

theorem tailTrace_4588132 : CollatzResearch.WordTrace tailWord_4588132 prefixEnd_4588132 2355917022274548146149571 := by
  unfold tailWord_4588132
  simp only [CollatzResearch.WordTrace]
  refine ⟨83671460906994414702939325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111561947875992552937252433 83671460906994414702939325)
  ·
    refine ⟨31376797840122905513602247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83671460906994414702939325 31376797840122905513602247)
    ·
      refine ⟨47065196760184358270403371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31376797840122905513602247 47065196760184358270403371)
      ·
        refine ⟨70597795140276537405605057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47065196760184358270403371 70597795140276537405605057)
        ·
          refine ⟨52948346355207403054203793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70597795140276537405605057 52948346355207403054203793)
          ·
            refine ⟨39711259766405552290652845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52948346355207403054203793 39711259766405552290652845)
            ·
              refine ⟨14891722412402082108994817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39711259766405552290652845 14891722412402082108994817)
              ·
                refine ⟨11168791809301561581746113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14891722412402082108994817 11168791809301561581746113)
                ·
                  refine ⟨8376593856976171186309585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11168791809301561581746113 8376593856976171186309585)
                  ·
                    refine ⟨6282445392732128389732189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8376593856976171186309585 6282445392732128389732189)
                    ·
                      refine ⟨2355917022274548146149571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282445392732128389732189 2355917022274548146149571)
                      ·
                        rfl

theorem cell23_4588132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_4588132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588132 prefixEnd_4588132 := by exact prefixLift 4588132
  have htrace : WordTrace (prefixWord ++ tailWord_4588132) baseStart_4588132 baseEnd_4588132 := by
    simpa [prefixWord, tailWord_4588132, baseEnd_4588132] using wordTrace_append hprefix tailTrace_4588132
  have hstable : (prefixWord ++ tailWord_4588132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588132).length < 2 ^ (prefixWord ++ tailWord_4588132).sum := by decide
  have hdescent : baseEnd_4588132 < baseStart_4588132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588135 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 6]
def baseStart_4588135 : Nat := 118140960795 + 4588135 * 2 ^ 59
def prefixEnd_4588135 : Nat := 4983230072969 + 3 ^ 40 * 4588135 * 2
def baseEnd_4588135 : Nat := 261768729190723514934673

theorem tailTrace_4588135 : CollatzResearch.WordTrace tailWord_4588135 prefixEnd_4588135 261768729190723514934673 := by
  unfold tailWord_4588135
  simp only [CollatzResearch.WordTrace]
  refine ⟨167343031232977960918237859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111562020821985307278825239 167343031232977960918237859)
  ·
    refine ⟨251014546849466941377356789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167343031232977960918237859 251014546849466941377356789)
    ·
      refine ⟨23532613767137525754127199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 251014546849466941377356789 23532613767137525754127199)
      ·
        refine ⟨35298920650706288631190799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23532613767137525754127199 35298920650706288631190799)
        ·
          refine ⟨52948380976059432946786199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35298920650706288631190799 52948380976059432946786199)
          ·
            refine ⟨79422571464089149420179299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52948380976059432946786199 79422571464089149420179299)
            ·
              refine ⟨119133857196133724130268949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79422571464089149420179299 119133857196133724130268949)
              ·
                refine ⟨5584399556068768318606357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119133857196133724130268949 5584399556068768318606357)
                ·
                  refine ⟨261768729190723514934673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5584399556068768318606357 261768729190723514934673)
                  ·
                    rfl

theorem cell23_4588135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 6].length) (baseStart_4588135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588135 prefixEnd_4588135 := by exact prefixLift 4588135
  have htrace : WordTrace (prefixWord ++ tailWord_4588135) baseStart_4588135 baseEnd_4588135 := by
    simpa [prefixWord, tailWord_4588135, baseEnd_4588135] using wordTrace_append hprefix tailTrace_4588135
  have hstable : (prefixWord ++ tailWord_4588135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588135).length < 2 ^ (prefixWord ++ tailWord_4588135).sum := by decide
  have hdescent : baseEnd_4588135 < baseStart_4588135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588189 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_4588189 : Nat := 118140960795 + 4588189 * 2 ^ 59
def prefixEnd_4588189 : Nat := 4983230072969 + 3 ^ 40 * 4588189 * 2
def baseEnd_4588189 : Nat := 2355946290671854423136809

theorem tailTrace_4588189 : CollatzResearch.WordTrace tailWord_4588189 prefixEnd_4588189 2355946290671854423136809 := by
  unfold tailWord_4588189
  simp only [CollatzResearch.WordTrace]
  refine ⟨167345000774782328140703621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111563333849854885427135747 167345000774782328140703621)
  ·
    refine ⟨31377187645271686526381929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167345000774782328140703621 31377187645271686526381929)
    ·
      refine ⟨23532890733953764894786447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31377187645271686526381929 23532890733953764894786447)
      ·
        refine ⟨35299336100930647342179671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23532890733953764894786447 35299336100930647342179671)
        ·
          refine ⟨52949004151395971013269507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35299336100930647342179671 52949004151395971013269507)
          ·
            refine ⟨79423506227093956519904261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52949004151395971013269507 79423506227093956519904261)
            ·
              refine ⟨14891907417580116847482049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79423506227093956519904261 14891907417580116847482049)
              ·
                refine ⟨11168930563185087635611537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14891907417580116847482049 11168930563185087635611537)
                ·
                  refine ⟨8376697922388815726708653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11168930563185087635611537 8376697922388815726708653)
                  ·
                    refine ⟨3141261720895805897515745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8376697922388815726708653 3141261720895805897515745)
                    ·
                      refine ⟨2355946290671854423136809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141261720895805897515745 2355946290671854423136809)
                      ·
                        rfl

theorem cell23_4588189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_4588189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588189 prefixEnd_4588189 := by exact prefixLift 4588189
  have htrace : WordTrace (prefixWord ++ tailWord_4588189) baseStart_4588189 baseEnd_4588189 := by
    simpa [prefixWord, tailWord_4588189, baseEnd_4588189] using wordTrace_append hprefix tailTrace_4588189
  have hstable : (prefixWord ++ tailWord_4588189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588189).length < 2 ^ (prefixWord ++ tailWord_4588189).sum := by decide
  have hdescent : baseEnd_4588189 < baseStart_4588189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588196 : List Nat := [2, 3, 1, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_4588196 : Nat := 118140960795 + 4588196 * 2 ^ 59
def prefixEnd_4588196 : Nat := 4983230072969 + 3 ^ 40 * 4588196 * 2
def baseEnd_4588196 : Nat := 2355949885036435895749277

theorem tailTrace_4588196 : CollatzResearch.WordTrace tailWord_4588196 prefixEnd_4588196 2355949885036435895749277 := by
  unfold tailWord_4588196
  simp only [CollatzResearch.WordTrace]
  refine ⟨83672628042878484168104221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111563504057171312224138961 83672628042878484168104221)
  ·
    refine ⟨31377235516079431563039083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83672628042878484168104221 31377235516079431563039083)
    ·
      refine ⟨47065853274119147344558625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31377235516079431563039083 47065853274119147344558625)
      ·
        refine ⟨35299389955589360508418969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47065853274119147344558625 35299389955589360508418969)
        ·
          refine ⟨26474542466692020381314227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35299389955589360508418969 26474542466692020381314227)
          ·
            refine ⟨39711813700038030571971341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26474542466692020381314227 39711813700038030571971341)
            ·
              refine ⟨14891930137514261464489253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39711813700038030571971341 14891930137514261464489253)
              ·
                refine ⟨2792236900783924024591735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14891930137514261464489253 2792236900783924024591735)
                ·
                  refine ⟨4188355351175886036887603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792236900783924024591735 4188355351175886036887603)
                  ·
                    refine ⟨6282533026763829055331405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4188355351175886036887603 6282533026763829055331405)
                    ·
                      refine ⟨2355949885036435895749277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282533026763829055331405 2355949885036435895749277)
                      ·
                        rfl

theorem cell23_4588196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_4588196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588196 prefixEnd_4588196 := by exact prefixLift 4588196
  have htrace : WordTrace (prefixWord ++ tailWord_4588196) baseStart_4588196 baseEnd_4588196 := by
    simpa [prefixWord, tailWord_4588196, baseEnd_4588196] using wordTrace_append hprefix tailTrace_4588196
  have hstable : (prefixWord ++ tailWord_4588196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588196).length < 2 ^ (prefixWord ++ tailWord_4588196).sum := by decide
  have hdescent : baseEnd_4588196 < baseStart_4588196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588232 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_4588232 : Nat := 118140960795 + 4588232 * 2 ^ 59
def prefixEnd_4588232 : Nat := 4983230072969 + 3 ^ 40 * 4588232 * 2
def baseEnd_4588232 : Nat := 2355968370339997754899111

theorem tailTrace_4588232 : CollatzResearch.WordTrace tailWord_4588232 prefixEnd_4588232 2355968370339997754899111 := by
  unfold tailWord_4588232
  simp only [CollatzResearch.WordTrace]
  refine ⟨83673284556813273242259475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111564379409084364323012633 83673284556813273242259475)
  ·
    refine ⟨125509926835219909863389213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83673284556813273242259475 125509926835219909863389213)
    ·
      refine ⟨47066222563207466198770955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125509926835219909863389213 47066222563207466198770955)
      ·
        refine ⟨70599333844811199298156433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47066222563207466198770955 70599333844811199298156433)
        ·
          refine ⟨52949500383608399473617325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70599333844811199298156433 52949500383608399473617325)
          ·
            refine ⟨19856062643853149802606497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52949500383608399473617325 19856062643853149802606497)
            ·
              refine ⟨14892046982889862351954873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19856062643853149802606497 14892046982889862351954873)
              ·
                refine ⟨11169035237167396763966155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14892046982889862351954873 11169035237167396763966155)
                ·
                  refine ⟨16753552855751095145949233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11169035237167396763966155 16753552855751095145949233)
                  ·
                    refine ⟨12565164641813321359461925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16753552855751095145949233 12565164641813321359461925)
                    ·
                      refine ⟨2355968370339997754899111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12565164641813321359461925 2355968370339997754899111)
                      ·
                        rfl

theorem cell23_4588232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_4588232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588232 prefixEnd_4588232 := by exact prefixLift 4588232
  have htrace : WordTrace (prefixWord ++ tailWord_4588232) baseStart_4588232 baseEnd_4588232 := by
    simpa [prefixWord, tailWord_4588232, baseEnd_4588232] using wordTrace_append hprefix tailTrace_4588232
  have hstable : (prefixWord ++ tailWord_4588232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588232).length < 2 ^ (prefixWord ++ tailWord_4588232).sum := by decide
  have hdescent : baseEnd_4588232 < baseStart_4588232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588236 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4588236 : Nat := 118140960795 + 4588236 * 2 ^ 59
def prefixEnd_4588236 : Nat := 4983230072969 + 3 ^ 40 * 4588236 * 2
def baseEnd_4588236 : Nat := 2355970424262615739249093

theorem tailTrace_4588236 : CollatzResearch.WordTrace tailWord_4588236 prefixEnd_4588236 2355970424262615739249093 := by
  unfold tailWord_4588236
  simp only [CollatzResearch.WordTrace]
  refine ⟨83673357502806027583832281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111564476670408036778443041 83673357502806027583832281)
  ·
    refine ⟨62755018127104520687874211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83673357502806027583832281 62755018127104520687874211)
    ·
      refine ⟨94132527190656781031811317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62755018127104520687874211 94132527190656781031811317)
      ·
        refine ⟨8824924424124073221732311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94132527190656781031811317 8824924424124073221732311)
        ·
          refine ⟨13237386636186109832598467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8824924424124073221732311 13237386636186109832598467)
          ·
            refine ⟨19856079954279164748897701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13237386636186109832598467 19856079954279164748897701)
            ·
              refine ⟨3723014991427343390418319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19856079954279164748897701 3723014991427343390418319)
              ·
                refine ⟨5584522487141015085627479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723014991427343390418319 5584522487141015085627479)
                ·
                  refine ⟨8376783730711522628441219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5584522487141015085627479 8376783730711522628441219)
                  ·
                    refine ⟨12565175596067283942661829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8376783730711522628441219 12565175596067283942661829)
                    ·
                      refine ⟨2355970424262615739249093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12565175596067283942661829 2355970424262615739249093)
                      ·
                        rfl

theorem cell23_4588236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4588236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588236 prefixEnd_4588236 := by exact prefixLift 4588236
  have htrace : WordTrace (prefixWord ++ tailWord_4588236) baseStart_4588236 baseEnd_4588236 := by
    simpa [prefixWord, tailWord_4588236, baseEnd_4588236] using wordTrace_append hprefix tailTrace_4588236
  have hstable : (prefixWord ++ tailWord_4588236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588236).length < 2 ^ (prefixWord ++ tailWord_4588236).sum := by decide
  have hdescent : baseEnd_4588236 < baseStart_4588236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588242 : List Nat := [3, 2, 2, 2, 3, 1, 10]
def baseStart_4588242 : Nat := 118140960795 + 4588242 * 2 ^ 59
def prefixEnd_4588242 : Nat := 4983230072969 + 3 ^ 40 * 4588242 * 2
def baseEnd_4588242 : Nat := 29086092656130156984865

theorem tailTrace_4588242 : CollatzResearch.WordTrace tailWord_4588242 prefixEnd_4588242 29086092656130156984865 := by
  unfold tailWord_4588242
  simp only [CollatzResearch.WordTrace]
  refine ⟨41836733460897579548095745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111564622562393545461588653 41836733460897579548095745)
  ·
    refine ⟨31377550095673184661071809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41836733460897579548095745 31377550095673184661071809)
    ·
      refine ⟨23533162571754888495803857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31377550095673184661071809 23533162571754888495803857)
      ·
        refine ⟨17649871928816166371852893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23533162571754888495803857 17649871928816166371852893)
        ·
          refine ⟨6618701973306062389444835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17649871928816166371852893 6618701973306062389444835)
          ·
            refine ⟨9928052959959093584167253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618701973306062389444835 9928052959959093584167253)
            ·
              refine ⟨29086092656130156984865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9928052959959093584167253 29086092656130156984865)
              ·
                rfl

theorem cell23_4588242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 10].length) (baseStart_4588242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588242 prefixEnd_4588242 := by exact prefixLift 4588242
  have htrace : WordTrace (prefixWord ++ tailWord_4588242) baseStart_4588242 baseEnd_4588242 := by
    simpa [prefixWord, tailWord_4588242, baseEnd_4588242] using wordTrace_append hprefix tailTrace_4588242
  have hstable : (prefixWord ++ tailWord_4588242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588242).length < 2 ^ (prefixWord ++ tailWord_4588242).sum := by decide
  have hdescent : baseEnd_4588242 < baseStart_4588242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588276 : List Nat := [2, 6, 1, 1, 2, 1, 1, 9]
def baseStart_4588276 : Nat := 118140960795 + 4588276 * 2 ^ 59
def prefixEnd_4588276 : Nat := 4983230072969 + 3 ^ 40 * 4588276 * 2
def baseEnd_4588276 : Nat := 87258924573659095657367

theorem tailTrace_4588276 : CollatzResearch.WordTrace tailWord_4588276 prefixEnd_4588276 87258924573659095657367 := by
  unfold tailWord_4588276
  simp only [CollatzResearch.WordTrace]
  refine ⟨83674086962733570999560341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111565449283644761332747121 83674086962733570999560341)
  ·
    refine ⟨3922222826378136140604391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83674086962733570999560341 3922222826378136140604391)
    ·
      refine ⟨5883334239567204210906587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3922222826378136140604391 5883334239567204210906587)
      ·
        refine ⟨8825001359350806316359881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883334239567204210906587 8825001359350806316359881)
        ·
          refine ⟨6618751019513104737269911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8825001359350806316359881 6618751019513104737269911)
          ·
            refine ⟨9928126529269657105904867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618751019513104737269911 9928126529269657105904867)
            ·
              refine ⟨14892189793904485658857301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9928126529269657105904867 14892189793904485658857301)
              ·
                refine ⟨87258924573659095657367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14892189793904485658857301 87258924573659095657367)
                ·
                  rfl

theorem cell23_4588276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 9].length) (baseStart_4588276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588276 prefixEnd_4588276 := by exact prefixLift 4588276
  have htrace : WordTrace (prefixWord ++ tailWord_4588276) baseStart_4588276 baseEnd_4588276 := by
    simpa [prefixWord, tailWord_4588276, baseEnd_4588276] using wordTrace_append hprefix tailTrace_4588276
  have hstable : (prefixWord ++ tailWord_4588276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588276).length < 2 ^ (prefixWord ++ tailWord_4588276).sum := by decide
  have hdescent : baseEnd_4588276 < baseStart_4588276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588286 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_4588286 : Nat := 118140960795 + 4588286 * 2 ^ 59
def prefixEnd_4588286 : Nat := 4983230072969 + 3 ^ 40 * 4588286 * 2
def baseEnd_4588286 : Nat := 2355996098295340543623863

theorem tailTrace_4588286 : CollatzResearch.WordTrace tailWord_4588286 prefixEnd_4588286 2355996098295340543623863 := by
  unfold tailWord_4588286
  simp only [CollatzResearch.WordTrace]
  refine ⟨20918567331928864213373089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111565692436953942471323141 20918567331928864213373089)
  ·
    refine ⟨15688925498946648160029817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20918567331928864213373089 15688925498946648160029817)
    ·
      refine ⟨11766694124209986120022363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15688925498946648160029817 11766694124209986120022363)
      ·
        refine ⟨17650041186314979180033545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11766694124209986120022363 17650041186314979180033545)
        ·
          refine ⟨13237530889736234385025159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17650041186314979180033545 13237530889736234385025159)
          ·
            refine ⟨19856296334604351577537739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13237530889736234385025159 19856296334604351577537739)
            ·
              refine ⟨29784444501906527366306609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19856296334604351577537739 29784444501906527366306609)
              ·
                refine ⟨22338333376429895524729957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29784444501906527366306609 22338333376429895524729957)
                ·
                  refine ⟨4188437508080605410886867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22338333376429895524729957 4188437508080605410886867)
                  ·
                    refine ⟨6282656262120908116330301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4188437508080605410886867 6282656262120908116330301)
                    ·
                      refine ⟨2355996098295340543623863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282656262120908116330301 2355996098295340543623863)
                      ·
                        rfl

theorem cell23_4588286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_4588286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588286 prefixEnd_4588286 := by exact prefixLift 4588286
  have htrace : WordTrace (prefixWord ++ tailWord_4588286) baseStart_4588286 baseEnd_4588286 := by
    simpa [prefixWord, tailWord_4588286, baseEnd_4588286] using wordTrace_append hprefix tailTrace_4588286
  have hstable : (prefixWord ++ tailWord_4588286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588286).length < 2 ^ (prefixWord ++ tailWord_4588286).sum := by decide
  have hdescent : baseEnd_4588286 < baseStart_4588286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588296 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_4588296 : Nat := 118140960795 + 4588296 * 2 ^ 59
def prefixEnd_4588296 : Nat := 4983230072969 + 3 ^ 40 * 4588296 * 2
def baseEnd_4588296 : Nat := 2356001233101885504498817

theorem tailTrace_4588296 : CollatzResearch.WordTrace tailWord_4588296 prefixEnd_4588296 2356001233101885504498817 := by
  unfold tailWord_4588296
  simp only [CollatzResearch.WordTrace]
  refine ⟨83674451692697342707424371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111565935590263123609899161 83674451692697342707424371)
  ·
    refine ⟨125511677539046014061136557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83674451692697342707424371 125511677539046014061136557)
    ·
      refine ⟨47066879077142255272926209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125511677539046014061136557 47066879077142255272926209)
      ·
        refine ⟨35300159307856691454694657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47066879077142255272926209 35300159307856691454694657)
        ·
          refine ⟨26475119480892518591020993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35300159307856691454694657 26475119480892518591020993)
          ·
            refine ⟨19856339610669388943265745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26475119480892518591020993 19856339610669388943265745)
            ·
              refine ⟨14892254708002041707449309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19856339610669388943265745 14892254708002041707449309)
              ·
                refine ⟨5584595515500765640293491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14892254708002041707449309 5584595515500765640293491)
                ·
                  refine ⟨8376893273251148460440237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5584595515500765640293491 8376893273251148460440237)
                  ·
                    refine ⟨3141334977469180672665089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8376893273251148460440237 3141334977469180672665089)
                    ·
                      refine ⟨2356001233101885504498817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141334977469180672665089 2356001233101885504498817)
                      ·
                        rfl

theorem cell23_4588296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_4588296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588296 prefixEnd_4588296 := by exact prefixLift 4588296
  have htrace : WordTrace (prefixWord ++ tailWord_4588296) baseStart_4588296 baseEnd_4588296 := by
    simpa [prefixWord, tailWord_4588296, baseEnd_4588296] using wordTrace_append hprefix tailTrace_4588296
  have hstable : (prefixWord ++ tailWord_4588296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588296).length < 2 ^ (prefixWord ++ tailWord_4588296).sum := by decide
  have hdescent : baseEnd_4588296 < baseStart_4588296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588312 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_4588312 : Nat := 118140960795 + 4588312 * 2 ^ 59
def prefixEnd_4588312 : Nat := 4983230072969 + 3 ^ 40 * 4588312 * 2
def baseEnd_4588312 : Nat := 2356009448792357441898743

theorem tailTrace_4588312 : CollatzResearch.WordTrace tailWord_4588312 prefixEnd_4588312 2356009448792357441898743 := by
  unfold tailWord_4588312
  simp only [CollatzResearch.WordTrace]
  refine ⟨83674743476668360073715595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111566324635557813431620793 83674743476668360073715595)
  ·
    refine ⟨125512115215002540110573393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83674743476668360073715595 125512115215002540110573393)
    ·
      refine ⟨94134086411251905082930045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125512115215002540110573393 94134086411251905082930045)
      ·
        refine ⟨35300282404219464406098767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94134086411251905082930045 35300282404219464406098767)
        ·
          refine ⟨52950423606329196609148151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35300282404219464406098767 52950423606329196609148151)
          ·
            refine ⟨79425635409493794913722227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52950423606329196609148151 79425635409493794913722227)
            ·
              refine ⟨119138453114240692370583341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79425635409493794913722227 119138453114240692370583341)
              ·
                refine ⟨44676919917840259638968753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119138453114240692370583341 44676919917840259638968753)
                ·
                  refine ⟨33507689938380194729226565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44676919917840259638968753 33507689938380194729226565)
                  ·
                    refine ⟨6282691863446286511729981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33507689938380194729226565 6282691863446286511729981)
                    ·
                      refine ⟨2356009448792357441898743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282691863446286511729981 2356009448792357441898743)
                      ·
                        rfl

theorem cell23_4588312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_4588312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588312 prefixEnd_4588312 := by exact prefixLift 4588312
  have htrace : WordTrace (prefixWord ++ tailWord_4588312) baseStart_4588312 baseEnd_4588312 := by
    simpa [prefixWord, tailWord_4588312, baseEnd_4588312] using wordTrace_append hprefix tailTrace_4588312
  have hstable : (prefixWord ++ tailWord_4588312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588312).length < 2 ^ (prefixWord ++ tailWord_4588312).sum := by decide
  have hdescent : baseEnd_4588312 < baseStart_4588312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588362 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_4588362 : Nat := 118140960795 + 4588362 * 2 ^ 59
def prefixEnd_4588362 : Nat := 4983230072969 + 3 ^ 40 * 4588362 * 2
def baseEnd_4588362 : Nat := 785345040941694082091171

theorem tailTrace_4588362 : CollatzResearch.WordTrace tailWord_4588362 prefixEnd_4588362 785345040941694082091171 := by
  unfold tailWord_4588362
  simp only [CollatzResearch.WordTrace]
  refine ⟨41837827650788894671687835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111567540402103719124500893 41837827650788894671687835)
  ·
    refine ⟨62756741476183342007531753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41837827650788894671687835 62756741476183342007531753)
    ·
      refine ⟨47067556107137506505648815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62756741476183342007531753 47067556107137506505648815)
      ·
        refine ⟨70601334160706259758473223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47067556107137506505648815 70601334160706259758473223)
        ·
          refine ⟨105902001241059389637709835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70601334160706259758473223 105902001241059389637709835)
          ·
            refine ⟨158853001861589084456564753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105902001241059389637709835 158853001861589084456564753)
            ·
              refine ⟨119139751396191813342423565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158853001861589084456564753 119139751396191813342423565)
              ·
                refine ⟨44677406773571930003408837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119139751396191813342423565 44677406773571930003408837)
                ·
                  refine ⟨8377013770044736875639157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44677406773571930003408837 8377013770044736875639157)
                  ·
                    refine ⟨785345040941694082091171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8377013770044736875639157 785345040941694082091171)
                    ·
                      rfl

theorem cell23_4588362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_4588362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588362 prefixEnd_4588362 := by exact prefixLift 4588362
  have htrace : WordTrace (prefixWord ++ tailWord_4588362) baseStart_4588362 baseEnd_4588362 := by
    simpa [prefixWord, tailWord_4588362, baseEnd_4588362] using wordTrace_append hprefix tailTrace_4588362
  have hstable : (prefixWord ++ tailWord_4588362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588362).length < 2 ^ (prefixWord ++ tailWord_4588362).sum := by decide
  have hdescent : baseEnd_4588362 < baseStart_4588362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588412 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_4588412 : Nat := 118140960795 + 4588412 * 2 ^ 59
def prefixEnd_4588412 : Nat := 4983230072969 + 3 ^ 40 * 4588412 * 2
def baseEnd_4588412 : Nat := 2356060796857807050648283

theorem tailTrace_4588412 : CollatzResearch.WordTrace tailWord_4588412 prefixEnd_4588412 2356060796857807050648283 := by
  unfold tailWord_4588412
  simp only [CollatzResearch.WordTrace]
  refine ⟨83676567126487218613035745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111568756168649624817380993 83676567126487218613035745)
  ·
    refine ⟨62757425344865413959776809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83676567126487218613035745 62757425344865413959776809)
    ·
      refine ⟨47068069008649060469832607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62757425344865413959776809 47068069008649060469832607)
      ·
        refine ⟨70602103512973590704748911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47068069008649060469832607 70602103512973590704748911)
        ·
          refine ⟨105903155269460386057123367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70602103512973590704748911 105903155269460386057123367)
          ·
            refine ⟨158854732904190579085685051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105903155269460386057123367 158854732904190579085685051)
            ·
              refine ⟨238282099356285868628527577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158854732904190579085685051 238282099356285868628527577)
              ·
                refine ⟨178711574517214401471395683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238282099356285868628527577 178711574517214401471395683)
                ·
                  refine ⟨268067361775821602207093525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178711574517214401471395683 268067361775821602207093525)
                  ·
                    refine ⟨12565657583241637603457509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 268067361775821602207093525 12565657583241637603457509)
                    ·
                      refine ⟨2356060796857807050648283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12565657583241637603457509 2356060796857807050648283)
                      ·
                        rfl

theorem cell23_4588412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_4588412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588412 prefixEnd_4588412 := by exact prefixLift 4588412
  have htrace : WordTrace (prefixWord ++ tailWord_4588412) baseStart_4588412 baseEnd_4588412 := by
    simpa [prefixWord, tailWord_4588412, baseEnd_4588412] using wordTrace_append hprefix tailTrace_4588412
  have hstable : (prefixWord ++ tailWord_4588412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588412).length < 2 ^ (prefixWord ++ tailWord_4588412).sum := by decide
  have hdescent : baseEnd_4588412 < baseStart_4588412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588419 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 3]
def baseStart_4588419 : Nat := 118140960795 + 4588419 * 2 ^ 59
def prefixEnd_4588419 : Nat := 4983230072969 + 3 ^ 40 * 4588419 * 2
def baseEnd_4588419 : Nat := 2356064391222388523260751

theorem tailTrace_4588419 : CollatzResearch.WordTrace tailWord_4588419 prefixEnd_4588419 2356064391222388523260751 := by
  unfold tailWord_4588419
  simp only [CollatzResearch.WordTrace]
  refine ⟨167353389563949077421576311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111568926375966051614384207 167353389563949077421576311)
  ·
    refine ⟨251030084345923616132364467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167353389563949077421576311 251030084345923616132364467)
    ·
      refine ⟨376545126518885424198546701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251030084345923616132364467 376545126518885424198546701)
      ·
        refine ⟨141204422444582034074455013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376545126518885424198546701 141204422444582034074455013)
        ·
          refine ⟨26475829208359131388960315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141204422444582034074455013 26475829208359131388960315)
          ·
            refine ⟨39713743812538697083440473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26475829208359131388960315 39713743812538697083440473)
            ·
              refine ⟨29785307859404022812580355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39713743812538697083440473 29785307859404022812580355)
              ·
                refine ⟨44677961789106034218870533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29785307859404022812580355 44677961789106034218870533)
                ·
                  refine ⟨8377117835457381416038225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44677961789106034218870533 8377117835457381416038225)
                  ·
                    refine ⟨6282838376593036062028669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8377117835457381416038225 6282838376593036062028669)
                    ·
                      refine ⟨2356064391222388523260751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282838376593036062028669 2356064391222388523260751)
                      ·
                        rfl

theorem cell23_4588419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_4588419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588419 prefixEnd_4588419 := by exact prefixLift 4588419
  have htrace : WordTrace (prefixWord ++ tailWord_4588419) baseStart_4588419 baseEnd_4588419 := by
    simpa [prefixWord, tailWord_4588419, baseEnd_4588419] using wordTrace_append hprefix tailTrace_4588419
  have hstable : (prefixWord ++ tailWord_4588419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588419).length < 2 ^ (prefixWord ++ tailWord_4588419).sum := by decide
  have hdescent : baseEnd_4588419 < baseStart_4588419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588426 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_4588426 : Nat := 118140960795 + 4588426 * 2 ^ 59
def prefixEnd_4588426 : Nat := 4983230072969 + 3 ^ 40 * 4588426 * 2
def baseEnd_4588426 : Nat := 785355995195656665291073

theorem tailTrace_4588426 : CollatzResearch.WordTrace tailWord_4588426 prefixEnd_4588426 785355995195656665291073 := by
  unfold tailWord_4588426
  simp only [CollatzResearch.WordTrace]
  refine ⟨41838411218730929404270283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111569096583282478411387421 41838411218730929404270283)
  ·
    refine ⟨62757616828096394106405425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41838411218730929404270283 62757616828096394106405425)
    ·
      refine ⟨47068212621072295579804069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62757616828096394106405425 47068212621072295579804069)
      ·
        refine ⟨8825289866451055421213263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47068212621072295579804069 8825289866451055421213263)
        ·
          refine ⟨13237934799676583131819895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8825289866451055421213263 13237934799676583131819895)
          ·
            refine ⟨19856902199514874697729843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13237934799676583131819895 19856902199514874697729843)
            ·
              refine ⟨29785353299272312046594765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19856902199514874697729843 29785353299272312046594765)
              ·
                refine ⟨11169507487227117017473037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29785353299272312046594765 11169507487227117017473037)
                ·
                  refine ⟨4188565307710168881552389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11169507487227117017473037 4188565307710168881552389)
                  ·
                    refine ⟨785355995195656665291073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4188565307710168881552389 785355995195656665291073)
                    ·
                      rfl

theorem cell23_4588426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_4588426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588426 prefixEnd_4588426 := by exact prefixLift 4588426
  have htrace : WordTrace (prefixWord ++ tailWord_4588426) baseStart_4588426 baseEnd_4588426 := by
    simpa [prefixWord, tailWord_4588426, baseEnd_4588426] using wordTrace_append hprefix tailTrace_4588426
  have hstable : (prefixWord ++ tailWord_4588426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588426).length < 2 ^ (prefixWord ++ tailWord_4588426).sum := by decide
  have hdescent : baseEnd_4588426 < baseStart_4588426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588506 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_4588506 : Nat := 118140960795 + 4588506 * 2 ^ 59
def prefixEnd_4588506 : Nat := 4983230072969 + 3 ^ 40 * 4588506 * 2
def baseEnd_4588506 : Nat := 2356109064039329682872851

theorem tailTrace_4588506 : CollatzResearch.WordTrace tailWord_4588506 prefixEnd_4588506 2356109064039329682872851 := by
  unfold tailWord_4588506
  simp only [CollatzResearch.WordTrace]
  refine ⟨41839140678658472819998343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111571041809755927519995581 41839140678658472819998343)
  ·
    refine ⟨62758711017987709229997515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41839140678658472819998343 62758711017987709229997515)
    ·
      refine ⟨94138066526981563844996273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62758711017987709229997515 94138066526981563844996273)
      ·
        refine ⟨70603549895236172883747205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94138066526981563844996273 70603549895236172883747205)
        ·
          refine ⟨13238165605356782415702601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70603549895236172883747205 13238165605356782415702601)
          ·
            refine ⟨9928624204017586811776951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13238165605356782415702601 9928624204017586811776951)
            ·
              refine ⟨14892936306026380217665427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9928624204017586811776951 14892936306026380217665427)
              ·
                refine ⟨22339404459039570326498141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14892936306026380217665427 22339404459039570326498141)
                ·
                  refine ⟨8377276672139838872436803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22339404459039570326498141 8377276672139838872436803)
                  ·
                    refine ⟨12565915008209758308655205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8377276672139838872436803 12565915008209758308655205)
                    ·
                      refine ⟨2356109064039329682872851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12565915008209758308655205 2356109064039329682872851)
                      ·
                        rfl

theorem cell23_4588506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_4588506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588506 prefixEnd_4588506 := by exact prefixLift 4588506
  have htrace : WordTrace (prefixWord ++ tailWord_4588506) baseStart_4588506 baseEnd_4588506 := by
    simpa [prefixWord, tailWord_4588506, baseEnd_4588506] using wordTrace_append hprefix tailTrace_4588506
  have hstable : (prefixWord ++ tailWord_4588506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588506).length < 2 ^ (prefixWord ++ tailWord_4588506).sum := by decide
  have hdescent : baseEnd_4588506 < baseStart_4588506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588534 : List Nat := [5, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_4588534 : Nat := 118140960795 + 4588534 * 2 ^ 59
def prefixEnd_4588534 : Nat := 4983230072969 + 3 ^ 40 * 4588534 * 2
def baseEnd_4588534 : Nat := 2356123441497655573322723

theorem tailTrace_4588534 : CollatzResearch.WordTrace tailWord_4588534 prefixEnd_4588534 2356123441497655573322723 := by
  unfold tailWord_4588534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10459848997408278253875791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111571722639021634708008437 10459848997408278253875791)
  ·
    refine ⟨15689773496112417380813687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10459848997408278253875791 15689773496112417380813687)
    ·
      refine ⟨23534660244168626071220531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15689773496112417380813687 23534660244168626071220531)
      ·
        refine ⟨35301990366252939106830797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23534660244168626071220531 35301990366252939106830797)
        ·
          refine ⟨13238246387344852165061549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35301990366252939106830797 13238246387344852165061549)
          ·
            refine ⟨4964342395254319561898081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13238246387344852165061549 4964342395254319561898081)
            ·
              refine ⟨3723256796440739671423561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4964342395254319561898081 3723256796440739671423561)
              ·
                refine ⟨2792442597330554753567671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3723256796440739671423561 2792442597330554753567671)
                ·
                  refine ⟨4188663895995832130351507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792442597330554753567671 4188663895995832130351507)
                  ·
                    refine ⟨6282995843993748195527261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4188663895995832130351507 6282995843993748195527261)
                    ·
                      refine ⟨2356123441497655573322723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6282995843993748195527261 2356123441497655573322723)
                      ·
                        rfl

theorem cell23_4588534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_4588534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588534 prefixEnd_4588534 := by exact prefixLift 4588534
  have htrace : WordTrace (prefixWord ++ tailWord_4588534) baseStart_4588534 baseEnd_4588534 := by
    simpa [prefixWord, tailWord_4588534, baseEnd_4588534] using wordTrace_append hprefix tailTrace_4588534
  have hstable : (prefixWord ++ tailWord_4588534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588534).length < 2 ^ (prefixWord ++ tailWord_4588534).sum := by decide
  have hdescent : baseEnd_4588534 < baseStart_4588534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588539 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 3]
def baseStart_4588539 : Nat := 118140960795 + 4588539 * 2 ^ 59
def prefixEnd_4588539 : Nat := 4983230072969 + 3 ^ 40 * 4588539 * 2
def baseEnd_4588539 : Nat := 2356126008900928053760199

theorem tailTrace_4588539 : CollatzResearch.WordTrace tailWord_4588539 prefixEnd_4588539 2356126008900928053760199 := by
  unfold tailWord_4588539
  simp only [CollatzResearch.WordTrace]
  refine ⟨167357766323514337915944671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111571844215676225277296447 167357766323514337915944671)
  ·
    refine ⟨251036649485271506873917007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167357766323514337915944671 251036649485271506873917007)
    ·
      refine ⟨376554974227907260310875511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251036649485271506873917007 376554974227907260310875511)
      ·
        refine ⟨564832461341860890466313267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376554974227907260310875511 564832461341860890466313267)
        ·
          refine ⟨847248692012791335699469901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564832461341860890466313267 847248692012791335699469901)
          ·
            refine ⟨317718259504796750887301213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 847248692012791335699469901 317718259504796750887301213)
            ·
              refine ⟨119144347314298781582737955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317718259504796750887301213 119144347314298781582737955)
              ·
                refine ⟨178716520971448172374106933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119144347314298781582737955 178716520971448172374106933)
                ·
                  refine ⟨16754673841073266160072525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178716520971448172374106933 16754673841073266160072525)
                  ·
                    refine ⟨6283002690402474810027197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16754673841073266160072525 6283002690402474810027197)
                    ·
                      refine ⟨2356126008900928053760199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6283002690402474810027197 2356126008900928053760199)
                      ·
                        rfl

theorem cell23_4588539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 3].length) (baseStart_4588539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588539 prefixEnd_4588539 := by exact prefixLift 4588539
  have htrace : WordTrace (prefixWord ++ tailWord_4588539) baseStart_4588539 baseEnd_4588539 := by
    simpa [prefixWord, tailWord_4588539, baseEnd_4588539] using wordTrace_append hprefix tailTrace_4588539
  have hstable : (prefixWord ++ tailWord_4588539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588539).length < 2 ^ (prefixWord ++ tailWord_4588539).sum := by decide
  have hdescent : baseEnd_4588539 < baseStart_4588539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588556 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_4588556 : Nat := 118140960795 + 4588556 * 2 ^ 59
def prefixEnd_4588556 : Nat := 4983230072969 + 3 ^ 40 * 4588556 * 2
def baseEnd_4588556 : Nat := 2356134738072054487247621

theorem tailTrace_4588556 : CollatzResearch.WordTrace tailWord_4588556 prefixEnd_4588556 2356134738072054487247621 := by
  unfold tailWord_4588556
  simp only [CollatzResearch.WordTrace]
  refine ⟨83679193182226374909656761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111572257576301833212875681 83679193182226374909656761)
  ·
    refine ⟨62759394886669781182242571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83679193182226374909656761 62759394886669781182242571)
    ·
      refine ⟨94139092330004671773363857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62759394886669781182242571 94139092330004671773363857)
      ·
        refine ⟨70604319247503503830022893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94139092330004671773363857 70604319247503503830022893)
        ·
          refine ⟨26476619717813813936258585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70604319247503503830022893 26476619717813813936258585)
          ·
            refine ⟨19857464788360360452193939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26476619717813813936258585 19857464788360360452193939)
            ·
              refine ⟨29786197182540540678290909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19857464788360360452193939 29786197182540540678290909)
              ·
                refine ⟨11169823943452702754359091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29786197182540540678290909 11169823943452702754359091)
                ·
                  refine ⟨16754735915179054131538637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11169823943452702754359091 16754735915179054131538637)
                  ·
                    refine ⟨6283025968192145299326989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16754735915179054131538637 6283025968192145299326989)
                    ·
                      refine ⟨2356134738072054487247621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6283025968192145299326989 2356134738072054487247621)
                      ·
                        rfl

theorem cell23_4588556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_4588556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588556 prefixEnd_4588556 := by exact prefixLift 4588556
  have htrace : WordTrace (prefixWord ++ tailWord_4588556) baseStart_4588556 baseEnd_4588556 := by
    simpa [prefixWord, tailWord_4588556, baseEnd_4588556] using wordTrace_append hprefix tailTrace_4588556
  have hstable : (prefixWord ++ tailWord_4588556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588556).length < 2 ^ (prefixWord ++ tailWord_4588556).sum := by decide
  have hdescent : baseEnd_4588556 < baseStart_4588556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588599 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_4588599 : Nat := 118140960795 + 4588599 * 2 ^ 59
def prefixEnd_4588599 : Nat := 4983230072969 + 3 ^ 40 * 4588599 * 2
def baseEnd_4588599 : Nat := 2356156817740197819009923

theorem tailTrace_4588599 : CollatzResearch.WordTrace tailWord_4588599 prefixEnd_4588599 2356156817740197819009923 := by
  unfold tailWord_4588599
  simp only [CollatzResearch.WordTrace]
  refine ⟨167359954703296968163128851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111573303135531312108752567 167359954703296968163128851)
  ·
    refine ⟨251039932054945452244693277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167359954703296968163128851 251039932054945452244693277)
    ·
      refine ⟨94139974520604544591759979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251039932054945452244693277 94139974520604544591759979)
      ·
        refine ⟨141209961780906816887639969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94139974520604544591759979 141209961780906816887639969)
        ·
          refine ⟨105907471335680112665729977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141209961780906816887639969 105907471335680112665729977)
          ·
            refine ⟨79430603501760084499297483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105907471335680112665729977 79430603501760084499297483)
            ·
              refine ⟨119145905252640126748946225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79430603501760084499297483 119145905252640126748946225)
              ·
                refine ⟨89359428939480095061709669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119145905252640126748946225 89359428939480095061709669)
                ·
                  refine ⟨16754892926152517824070563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89359428939480095061709669 16754892926152517824070563)
                  ·
                    refine ⟨25132339389228776736105845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16754892926152517824070563 25132339389228776736105845)
                    ·
                      refine ⟨2356156817740197819009923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25132339389228776736105845 2356156817740197819009923)
                      ·
                        rfl

theorem cell23_4588599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_4588599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588599 prefixEnd_4588599 := by exact prefixLift 4588599
  have htrace : WordTrace (prefixWord ++ tailWord_4588599) baseStart_4588599 baseEnd_4588599 := by
    simpa [prefixWord, tailWord_4588599, baseEnd_4588599] using wordTrace_append hprefix tailTrace_4588599
  have hstable : (prefixWord ++ tailWord_4588599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588599).length < 2 ^ (prefixWord ++ tailWord_4588599).sum := by decide
  have hdescent : baseEnd_4588599 < baseStart_4588599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588613 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 1, 4, 2]
def baseStart_4588613 : Nat := 118140960795 + 4588613 * 2 ^ 59
def prefixEnd_4588613 : Nat := 4983230072969 + 3 ^ 40 * 4588613 * 2
def baseEnd_4588613 : Nat := 2356164006469360764234859

theorem tailTrace_4588613 : CollatzResearch.WordTrace tailWord_4588613 prefixEnd_4588613 2356164006469360764234859 := by
  unfold tailWord_4588613
  simp only [CollatzResearch.WordTrace]
  refine ⟨167360465325246248554138493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111573643550164165702758995 167360465325246248554138493)
  ·
    refine ⟨62760174496967343207801935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167360465325246248554138493 62760174496967343207801935)
    ·
      refine ⟨94140261745451014811702903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62760174496967343207801935 94140261745451014811702903)
      ·
        refine ⟨141210392618176522217554355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94140261745451014811702903 141210392618176522217554355)
        ·
          refine ⟨211815588927264783326331533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141210392618176522217554355 211815588927264783326331533)
          ·
            refine ⟨79430845847724293747374325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211815588927264783326331533 79430845847724293747374325)
            ·
              refine ⟨7446641798224152538816343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79430845847724293747374325 7446641798224152538816343)
              ·
                refine ⟨11169962697336228808224515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7446641798224152538816343 11169962697336228808224515)
                ·
                  refine ⟨16754944046004343212336773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11169962697336228808224515 16754944046004343212336773)
                  ·
                    refine ⟨3141552008625814352313145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16754944046004343212336773 3141552008625814352313145)
                    ·
                      refine ⟨2356164006469360764234859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141552008625814352313145 2356164006469360764234859)
                      ·
                        rfl

theorem cell23_4588613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_4588613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588613 prefixEnd_4588613 := by exact prefixLift 4588613
  have htrace : WordTrace (prefixWord ++ tailWord_4588613) baseStart_4588613 baseEnd_4588613 := by
    simpa [prefixWord, tailWord_4588613, baseEnd_4588613] using wordTrace_append hprefix tailTrace_4588613
  have hstable : (prefixWord ++ tailWord_4588613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588613).length < 2 ^ (prefixWord ++ tailWord_4588613).sum := by decide
  have hdescent : baseEnd_4588613 < baseStart_4588613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588653 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 7]
def baseStart_4588653 : Nat := 118140960795 + 4588653 * 2 ^ 59
def prefixEnd_4588653 : Nat := 4983230072969 + 3 ^ 40 * 4588653 * 2
def baseEnd_4588653 : Nat := 261798282855060067526075

theorem tailTrace_4588653 : CollatzResearch.WordTrace tailWord_4588653 prefixEnd_4588653 261798282855060067526075 := by
  unfold tailWord_4588653
  simp only [CollatzResearch.WordTrace]
  refine ⟨167361924245101335385594613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111574616163400890257063075 167361924245101335385594613)
  ·
    refine ⟨15690180397978250192399495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167361924245101335385594613 15690180397978250192399495)
    ·
      refine ⟨23535270596967375288599243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15690180397978250192399495 23535270596967375288599243)
      ·
        refine ⟨35302905895451062932898865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23535270596967375288599243 35302905895451062932898865)
        ·
          refine ⟨26477179421588297199674149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35302905895451062932898865 26477179421588297199674149)
          ·
            refine ⟨4964471141547805724938903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26477179421588297199674149 4964471141547805724938903)
            ·
              refine ⟨7446706712321708587408355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964471141547805724938903 7446706712321708587408355)
              ·
                refine ⟨11170060068482562881112533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7446706712321708587408355 11170060068482562881112533)
                ·
                  refine ⟨261798282855060067526075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11170060068482562881112533 261798282855060067526075)
                  ·
                    rfl

theorem cell23_4588653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_4588653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588653 prefixEnd_4588653 := by exact prefixLift 4588653
  have htrace : WordTrace (prefixWord ++ tailWord_4588653) baseStart_4588653 baseEnd_4588653 := by
    simpa [prefixWord, tailWord_4588653, baseEnd_4588653] using wordTrace_append hprefix tailTrace_4588653
  have hstable : (prefixWord ++ tailWord_4588653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588653).length < 2 ^ (prefixWord ++ tailWord_4588653).sum := by decide
  have hdescent : baseEnd_4588653 < baseStart_4588653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588689 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_4588689 : Nat := 118140960795 + 4588689 * 2 ^ 59
def prefixEnd_4588689 : Nat := 4983230072969 + 3 ^ 40 * 4588689 * 2
def baseEnd_4588689 : Nat := 2356203030999102466884509

theorem tailTrace_4588689 : CollatzResearch.WordTrace tailWord_4588689 prefixEnd_4588689 2356203030999102466884509 := by
  unfold tailWord_4588689
  simp only [CollatzResearch.WordTrace]
  refine ⟨167363237272970913533905121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111575491515313942355936747 167363237272970913533905121)
  ·
    refine ⟨125522427954728185150428841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167363237272970913533905121 125522427954728185150428841)
    ·
      refine ⟨94141820966046138862821631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125522427954728185150428841 94141820966046138862821631)
      ·
        refine ⟨141212731449069208294232447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94141820966046138862821631 141212731449069208294232447)
        ·
          refine ⟨211819097173603812441348671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141212731449069208294232447 211819097173603812441348671)
          ·
            refine ⟨317728645760405718662023007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211819097173603812441348671 317728645760405718662023007)
            ·
              refine ⟨476592968640608577993034511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317728645760405718662023007 476592968640608577993034511)
              ·
                refine ⟨714889452960912866989551767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476592968640608577993034511 714889452960912866989551767)
                ·
                  refine ⟨1072334179441369300484327651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 714889452960912866989551767 1072334179441369300484327651)
                  ·
                    refine ⟨1608501269162053950726491477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1072334179441369300484327651 1608501269162053950726491477)
                    ·
                      refine ⟨2356203030999102466884509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1608501269162053950726491477 2356203030999102466884509)
                      ·
                        rfl

theorem cell23_4588689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_4588689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588689 prefixEnd_4588689 := by exact prefixLift 4588689
  have htrace : WordTrace (prefixWord ++ tailWord_4588689) baseStart_4588689 baseEnd_4588689 := by
    simpa [prefixWord, tailWord_4588689, baseEnd_4588689] using wordTrace_append hprefix tailTrace_4588689
  have hstable : (prefixWord ++ tailWord_4588689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588689).length < 2 ^ (prefixWord ++ tailWord_4588689).sum := by decide
  have hdescent : baseEnd_4588689 < baseStart_4588689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588737 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4588737 : Nat := 118140960795 + 4588737 * 2 ^ 59
def prefixEnd_4588737 : Nat := 4983230072969 + 3 ^ 40 * 4588737 * 2
def baseEnd_4588737 : Nat := 2356227678070518279084289

theorem tailTrace_4588737 : CollatzResearch.WordTrace tailWord_4588737 prefixEnd_4588737 2356227678070518279084289 := by
  unfold tailWord_4588737
  simp only [CollatzResearch.WordTrace]
  refine ⟨167364987976797017731652465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111576658651198011821101643 167364987976797017731652465)
  ·
    refine ⟨125523740982597763298739349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167364987976797017731652465 125523740982597763298739349)
    ·
      refine ⟨5883925358559270154628407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 125523740982597763298739349 5883925358559270154628407)
      ·
        refine ⟨8825888037838905231942611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883925358559270154628407 8825888037838905231942611)
        ·
          refine ⟨13238832056758357847913917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8825888037838905231942611 13238832056758357847913917)
          ·
            refine ⟨4964562021284384192967719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13238832056758357847913917 4964562021284384192967719)
            ·
              refine ⟨7446843031926576289451579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964562021284384192967719 7446843031926576289451579)
              ·
                refine ⟨11170264547889864434177369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7446843031926576289451579 11170264547889864434177369)
                ·
                  refine ⟨8377698410917398325633027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11170264547889864434177369 8377698410917398325633027)
                  ·
                    refine ⟨12566547616376097488449541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8377698410917398325633027 12566547616376097488449541)
                    ·
                      refine ⟨2356227678070518279084289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12566547616376097488449541 2356227678070518279084289)
                      ·
                        rfl

theorem cell23_4588737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4588737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588737 prefixEnd_4588737 := by exact prefixLift 4588737
  have htrace : WordTrace (prefixWord ++ tailWord_4588737) baseStart_4588737 baseEnd_4588737 := by
    simpa [prefixWord, tailWord_4588737, baseEnd_4588737] using wordTrace_append hprefix tailTrace_4588737
  have hstable : (prefixWord ++ tailWord_4588737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588737).length < 2 ^ (prefixWord ++ tailWord_4588737).sum := by decide
  have hdescent : baseEnd_4588737 < baseStart_4588737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588740 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_4588740 : Nat := 118140960795 + 4588740 * 2 ^ 59
def prefixEnd_4588740 : Nat := 4983230072969 + 3 ^ 40 * 4588740 * 2
def baseEnd_4588740 : Nat := 2356229218512481767346775

theorem tailTrace_4588740 : CollatzResearch.WordTrace tailWord_4588740 prefixEnd_4588740 2356229218512481767346775 := by
  unfold tailWord_4588740
  simp only [CollatzResearch.WordTrace]
  refine ⟨83682548697893074622005837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111576731597190766162674449 83682548697893074622005837)
  ·
    refine ⟨31380955761709902983252189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83682548697893074622005837 31380955761709902983252189)
    ·
      refine ⟨11767858410641213618719571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31380955761709902983252189 11767858410641213618719571)
      ·
        refine ⟨17651787615961820428079357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11767858410641213618719571 17651787615961820428079357)
        ·
          refine ⟨6619420355985682660529759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17651787615961820428079357 6619420355985682660529759)
          ·
            refine ⟨9929130533978523990794639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6619420355985682660529759 9929130533978523990794639)
            ·
              refine ⟨14893695800967785986191959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9929130533978523990794639 14893695800967785986191959)
              ·
                refine ⟨22340543701451678979287939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14893695800967785986191959 22340543701451678979287939)
                ·
                  refine ⟨33510815552177518468931909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22340543701451678979287939 33510815552177518468931909)
                  ·
                    refine ⟨6283277916033284712924733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33510815552177518468931909 6283277916033284712924733)
                    ·
                      refine ⟨2356229218512481767346775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6283277916033284712924733 2356229218512481767346775)
                      ·
                        rfl

theorem cell23_4588740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_4588740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588740 prefixEnd_4588740 := by exact prefixLift 4588740
  have htrace : WordTrace (prefixWord ++ tailWord_4588740) baseStart_4588740 baseEnd_4588740 := by
    simpa [prefixWord, tailWord_4588740, baseEnd_4588740] using wordTrace_append hprefix tailTrace_4588740
  have hstable : (prefixWord ++ tailWord_4588740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588740).length < 2 ^ (prefixWord ++ tailWord_4588740).sum := by decide
  have hdescent : baseEnd_4588740 < baseStart_4588740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588753 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 3]
def baseStart_4588753 : Nat := 118140960795 + 4588753 * 2 ^ 59
def prefixEnd_4588753 : Nat := 4983230072969 + 3 ^ 40 * 4588753 * 2
def baseEnd_4588753 : Nat := 2356235893760990216484215

theorem tailTrace_4588753 : CollatzResearch.WordTrace tailWord_4588753 prefixEnd_4588753 2356235893760990216484215 := by
  unfold tailWord_4588753
  simp only [CollatzResearch.WordTrace]
  refine ⟨167365571544739052464234913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111577047696492701642823275 167365571544739052464234913)
  ·
    refine ⟨125524178658554289348176185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167365571544739052464234913 125524178658554289348176185)
    ·
      refine ⟨94143133993915717011132139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125524178658554289348176185 94143133993915717011132139)
      ·
        refine ⟨141214700990873575516698209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94143133993915717011132139 141214700990873575516698209)
        ·
          refine ⟨105911025743155181637523657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141214700990873575516698209 105911025743155181637523657)
          ·
            refine ⟨79433269307366386228142743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105911025743155181637523657 79433269307366386228142743)
            ·
              refine ⟨119149903961049579342214115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79433269307366386228142743 119149903961049579342214115)
              ·
                refine ⟨178724855941574369013321173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119149903961049579342214115 178724855941574369013321173)
                ·
                  refine ⟨4188863811130649273749715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 178724855941574369013321173 4188863811130649273749715)
                  ·
                    refine ⟨6283295716695973910624573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4188863811130649273749715 6283295716695973910624573)
                    ·
                      refine ⟨2356235893760990216484215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6283295716695973910624573 2356235893760990216484215)
                      ·
                        rfl

theorem cell23_4588753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_4588753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588753 prefixEnd_4588753 := by exact prefixLift 4588753
  have htrace : WordTrace (prefixWord ++ tailWord_4588753) baseStart_4588753 baseEnd_4588753 := by
    simpa [prefixWord, tailWord_4588753, baseEnd_4588753] using wordTrace_append hprefix tailTrace_4588753
  have hstable : (prefixWord ++ tailWord_4588753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588753).length < 2 ^ (prefixWord ++ tailWord_4588753).sum := by decide
  have hdescent : baseEnd_4588753 < baseStart_4588753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588760 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 6]
def baseStart_4588760 : Nat := 118140960795 + 4588760 * 2 ^ 59
def prefixEnd_4588760 : Nat := 4983230072969 + 3 ^ 40 * 4588760 * 2
def baseEnd_4588760 : Nat := 261804387569507965455187

theorem tailTrace_4588760 : CollatzResearch.WordTrace tailWord_4588760 prefixEnd_4588760 261804387569507965455187 := by
  unfold tailWord_4588760
  simp only [CollatzResearch.WordTrace]
  refine ⟨83682913427856846329869867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111577217903809128439826489 83682913427856846329869867)
  ·
    refine ⟨125524370141785269494804801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83682913427856846329869867 125524370141785269494804801)
    ·
      refine ⟨94143277606338952121103601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125524370141785269494804801 94143277606338952121103601)
      ·
        refine ⟨70607458204754214090827701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94143277606338952121103601 70607458204754214090827701)
        ·
          refine ⟨6619449206695707571015097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70607458204754214090827701 6619449206695707571015097)
          ·
            refine ⟨4964586905021780678261323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6619449206695707571015097 4964586905021780678261323)
            ·
              refine ⟨7446880357532671017391985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964586905021780678261323 7446880357532671017391985)
              ·
                refine ⟨5585160268149503263043989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7446880357532671017391985 5585160268149503263043989)
                ·
                  refine ⟨261804387569507965455187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5585160268149503263043989 261804387569507965455187)
                  ·
                    rfl

theorem cell23_4588760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 6].length) (baseStart_4588760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588760 prefixEnd_4588760 := by exact prefixLift 4588760
  have htrace : WordTrace (prefixWord ++ tailWord_4588760) baseStart_4588760 baseEnd_4588760 := by
    simpa [prefixWord, tailWord_4588760, baseEnd_4588760] using wordTrace_append hprefix tailTrace_4588760
  have hstable : (prefixWord ++ tailWord_4588760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588760).length < 2 ^ (prefixWord ++ tailWord_4588760).sum := by decide
  have hdescent : baseEnd_4588760 < baseStart_4588760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588793 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 2, 6, 2]
def baseStart_4588793 : Nat := 118140960795 + 4588793 * 2 ^ 59
def prefixEnd_4588793 : Nat := 4983230072969 + 3 ^ 40 * 4588793 * 2
def baseEnd_4588793 : Nat := 2356256432987170059984031

theorem tailTrace_4588793 : CollatzResearch.WordTrace tailWord_4588793 prefixEnd_4588793 2356256432987170059984031 := by
  unfold tailWord_4588793
  simp only [CollatzResearch.WordTrace]
  refine ⟨167367030464594139295691033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111578020309729426197127355 167367030464594139295691033)
  ·
    refine ⟨125525272848445604471768275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167367030464594139295691033 125525272848445604471768275)
    ·
      refine ⟨188287909272668406707652413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125525272848445604471768275 188287909272668406707652413)
      ·
        refine ⟨70607965977250652515369655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188287909272668406707652413 70607965977250652515369655)
        ·
          refine ⟨105911948965875978773054483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70607965977250652515369655 105911948965875978773054483)
          ·
            refine ⟨158867923448813968159581725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105911948965875978773054483 158867923448813968159581725)
            ·
              refine ⟨59575471293305238059843147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158867923448813968159581725 59575471293305238059843147)
              ·
                refine ⟨89363206939957857089764721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59575471293305238059843147 89363206939957857089764721)
                ·
                  refine ⟨67022405204968392817323541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89363206939957857089764721 67022405204968392817323541)
                  ·
                    refine ⟨3141675243982893413312041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67022405204968392817323541 3141675243982893413312041)
                    ·
                      refine ⟨2356256432987170059984031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141675243982893413312041 2356256432987170059984031)
                      ·
                        rfl

theorem cell23_4588793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_4588793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588793 prefixEnd_4588793 := by exact prefixLift 4588793
  have htrace : WordTrace (prefixWord ++ tailWord_4588793) baseStart_4588793 baseEnd_4588793 := by
    simpa [prefixWord, tailWord_4588793, baseEnd_4588793] using wordTrace_append hprefix tailTrace_4588793
  have hstable : (prefixWord ++ tailWord_4588793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588793).length < 2 ^ (prefixWord ++ tailWord_4588793).sum := by decide
  have hdescent : baseEnd_4588793 < baseStart_4588793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588803 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 4, 4]
def baseStart_4588803 : Nat := 118140960795 + 4588803 * 2 ^ 59
def prefixEnd_4588803 : Nat := 4983230072969 + 3 ^ 40 * 4588803 * 2
def baseEnd_4588803 : Nat := 785420522597905006952995

theorem tailTrace_4588803 : CollatzResearch.WordTrace tailWord_4588803 prefixEnd_4588803 785420522597905006952995 := by
  unfold tailWord_4588803
  simp only [CollatzResearch.WordTrace]
  refine ⟨167367395194557911003555063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111578263463038607335703375 167367395194557911003555063)
  ·
    refine ⟨251051092791836866505332595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167367395194557911003555063 251051092791836866505332595)
    ·
      refine ⟨376576639187755299757998893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251051092791836866505332595 376576639187755299757998893)
      ·
        refine ⟨141216239695408237409249585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376576639187755299757998893 141216239695408237409249585)
        ·
          refine ⟨105912179771556178056937189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141216239695408237409249585 105912179771556178056937189)
          ·
            refine ⟨19858533707166783385675723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105912179771556178056937189 19858533707166783385675723)
            ·
              refine ⟨29787800560750175078513585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19858533707166783385675723 29787800560750175078513585)
              ·
                refine ⟨22340850420562631308885189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29787800560750175078513585 22340850420562631308885189)
                ·
                  refine ⟨4188909453855493370415973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22340850420562631308885189 4188909453855493370415973)
                  ·
                    refine ⟨785420522597905006952995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4188909453855493370415973 785420522597905006952995)
                    ·
                      rfl

theorem cell23_4588803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 4].length) (baseStart_4588803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588803 prefixEnd_4588803 := by exact prefixLift 4588803
  have htrace : WordTrace (prefixWord ++ tailWord_4588803) baseStart_4588803 baseEnd_4588803 := by
    simpa [prefixWord, tailWord_4588803, baseEnd_4588803] using wordTrace_append hprefix tailTrace_4588803
  have hstable : (prefixWord ++ tailWord_4588803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588803).length < 2 ^ (prefixWord ++ tailWord_4588803).sum := by decide
  have hdescent : baseEnd_4588803 < baseStart_4588803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588804 : List Nat := [2, 3, 2, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_4588804 : Nat := 118140960795 + 4588804 * 2 ^ 59
def prefixEnd_4588804 : Nat := 4983230072969 + 3 ^ 40 * 4588804 * 2
def baseEnd_4588804 : Nat := 2356262081274369516946481

theorem tailTrace_4588804 : CollatzResearch.WordTrace tailWord_4588804 prefixEnd_4588804 2356262081274369516946481 := by
  unfold tailWord_4588804
  simp only [CollatzResearch.WordTrace]
  refine ⟨83683715833777144087170733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111578287778369525449560977 83683715833777144087170733)
  ·
    refine ⟨31381393437666429032689025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83683715833777144087170733 31381393437666429032689025)
    ·
      refine ⟨23536045078249821774516769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31381393437666429032689025 23536045078249821774516769)
      ·
        refine ⟨17652033808687366330887577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23536045078249821774516769 17652033808687366330887577)
        ·
          refine ⟨13239025356515524748165683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17652033808687366330887577 13239025356515524748165683)
          ·
            refine ⟨19858538034773287122248525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13239025356515524748165683 19858538034773287122248525)
            ·
              refine ⟨7446951763039982670843197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19858538034773287122248525 7446951763039982670843197)
              ·
                refine ⟨2792606911139993501566199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7446951763039982670843197 2792606911139993501566199)
                ·
                  refine ⟨4188910366709990252349299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792606911139993501566199 4188910366709990252349299)
                  ·
                    refine ⟨6283365550064985378523949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4188910366709990252349299 6283365550064985378523949)
                    ·
                      refine ⟨2356262081274369516946481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6283365550064985378523949 2356262081274369516946481)
                      ·
                        rfl

theorem cell23_4588804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_4588804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588804 prefixEnd_4588804 := by exact prefixLift 4588804
  have htrace : WordTrace (prefixWord ++ tailWord_4588804) baseStart_4588804 baseEnd_4588804 := by
    simpa [prefixWord, tailWord_4588804, baseEnd_4588804] using wordTrace_append hprefix tailTrace_4588804
  have hstable : (prefixWord ++ tailWord_4588804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588804).length < 2 ^ (prefixWord ++ tailWord_4588804).sum := by decide
  have hdescent : baseEnd_4588804 < baseStart_4588804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588837 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_4588837 : Nat := 118140960795 + 4588837 * 2 ^ 59
def prefixEnd_4588837 : Nat := 4983230072969 + 3 ^ 40 * 4588837 * 2
def baseEnd_4588837 : Nat := 785426342045322629277943

theorem tailTrace_4588837 : CollatzResearch.WordTrace tailWord_4588837 prefixEnd_4588837 785426342045322629277943 := by
  unfold tailWord_4588837
  simp only [CollatzResearch.WordTrace]
  refine ⟨167368635276434734810292765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111579090184289823206861843 167368635276434734810292765)
  ·
    refine ⟨62763238228663025553859787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167368635276434734810292765 62763238228663025553859787)
    ·
      refine ⟨94144857342994538330789681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62763238228663025553859787 94144857342994538330789681)
      ·
        refine ⟨70608643007245903748092261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94144857342994538330789681 70608643007245903748092261)
        ·
          refine ⟨13239120563858606952767299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70608643007245903748092261 13239120563858606952767299)
          ·
            refine ⟨19858680845787910429150949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13239120563858606952767299 19858680845787910429150949)
            ·
              refine ⟨3723502658585233205465803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19858680845787910429150949 3723502658585233205465803)
              ·
                refine ⟨5585253987877849808198705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723502658585233205465803 5585253987877849808198705)
                ·
                  refine ⟨4188940490908387356149029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585253987877849808198705 4188940490908387356149029)
                  ·
                    refine ⟨785426342045322629277943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4188940490908387356149029 785426342045322629277943)
                    ·
                      rfl

theorem cell23_4588837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_4588837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588837 prefixEnd_4588837 := by exact prefixLift 4588837
  have htrace : WordTrace (prefixWord ++ tailWord_4588837) baseStart_4588837 baseEnd_4588837 := by
    simpa [prefixWord, tailWord_4588837, baseEnd_4588837] using wordTrace_append hprefix tailTrace_4588837
  have hstable : (prefixWord ++ tailWord_4588837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588837).length < 2 ^ (prefixWord ++ tailWord_4588837).sum := by decide
  have hdescent : baseEnd_4588837 < baseStart_4588837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588860 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_4588860 : Nat := 118140960795 + 4588860 * 2 ^ 59
def prefixEnd_4588860 : Nat := 4983230072969 + 3 ^ 40 * 4588860 * 2
def baseEnd_4588860 : Nat := 2356290836191021297846223

theorem tailTrace_4588860 : CollatzResearch.WordTrace tailWord_4588860 prefixEnd_4588860 2356290836191021297846223 := by
  unfold tailWord_4588860
  simp only [CollatzResearch.WordTrace]
  refine ⟨83684737077675704869190017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111579649436900939825586689 83684737077675704869190017)
  ·
    refine ⟨62763552808256778651892513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83684737077675704869190017 62763552808256778651892513)
    ·
      refine ⟨47072664606192583988919385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62763552808256778651892513 47072664606192583988919385)
      ·
        refine ⟨35304498454644437991689539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47072664606192583988919385 35304498454644437991689539)
        ·
          refine ⟨52956747681966656987534309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35304498454644437991689539 52956747681966656987534309)
          ·
            refine ⟨9929390190368748185162683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52956747681966656987534309 9929390190368748185162683)
            ·
              refine ⟨14894085285553122277744025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9929390190368748185162683 14894085285553122277744025)
              ·
                refine ⟨11170563964164841708308019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14894085285553122277744025 11170563964164841708308019)
                ·
                  refine ⟨16755845946247262562462029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11170563964164841708308019 16755845946247262562462029)
                  ·
                    refine ⟨6283442229842723460923261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16755845946247262562462029 6283442229842723460923261)
                    ·
                      refine ⟨2356290836191021297846223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6283442229842723460923261 2356290836191021297846223)
                      ·
                        rfl

theorem cell23_4588860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_4588860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588860 prefixEnd_4588860 := by exact prefixLift 4588860
  have htrace : WordTrace (prefixWord ++ tailWord_4588860) baseStart_4588860 baseEnd_4588860 := by
    simpa [prefixWord, tailWord_4588860, baseEnd_4588860] using wordTrace_append hprefix tailTrace_4588860
  have hstable : (prefixWord ++ tailWord_4588860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588860).length < 2 ^ (prefixWord ++ tailWord_4588860).sum := by decide
  have hdescent : baseEnd_4588860 < baseStart_4588860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588940 : List Nat := [2, 2, 1, 2, 1, 3, 1, 6, 5]
def baseStart_4588940 : Nat := 118140960795 + 4588940 * 2 ^ 59
def prefixEnd_4588940 : Nat := 4983230072969 + 3 ^ 40 * 4588940 * 2
def baseEnd_4588940 : Nat := 261814657182597887205095

theorem tailTrace_4588940 : CollatzResearch.WordTrace tailWord_4588940 prefixEnd_4588940 261814657182597887205095 := by
  unfold tailWord_4588940
  simp only [CollatzResearch.WordTrace]
  refine ⟨83686195997530791700646137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111581594663374388934194849 83686195997530791700646137)
  ·
    refine ⟨62764646998148093775484603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83686195997530791700646137 62764646998148093775484603)
    ·
      refine ⟨94146970497222140663226905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62764646998148093775484603 94146970497222140663226905)
      ·
        refine ⟨70610227872916605497420179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94146970497222140663226905 70610227872916605497420179)
        ·
          refine ⟨105915341809374908246130269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70610227872916605497420179 105915341809374908246130269)
          ·
            refine ⟨39718253178515590592298851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105915341809374908246130269 39718253178515590592298851)
            ·
              refine ⟨59577379767773385888448277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39718253178515590592298851 59577379767773385888448277)
              ·
                refine ⟨2792689676614377463521013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59577379767773385888448277 2792689676614377463521013)
                ·
                  refine ⟨261814657182597887205095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2792689676614377463521013 261814657182597887205095)
                  ·
                    rfl

theorem cell23_4588940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_4588940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588940 prefixEnd_4588940 := by exact prefixLift 4588940
  have htrace : WordTrace (prefixWord ++ tailWord_4588940) baseStart_4588940 baseEnd_4588940 := by
    simpa [prefixWord, tailWord_4588940, baseEnd_4588940] using wordTrace_append hprefix tailTrace_4588940
  have hstable : (prefixWord ++ tailWord_4588940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588940).length < 2 ^ (prefixWord ++ tailWord_4588940).sum := by decide
  have hdescent : baseEnd_4588940 < baseStart_4588940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4588953 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 1, 7]
def baseStart_4588953 : Nat := 118140960795 + 4588953 * 2 ^ 59
def prefixEnd_4588953 : Nat := 4983230072969 + 3 ^ 40 * 4588953 * 2
def baseEnd_4588953 : Nat := 785446196630629811327765

theorem tailTrace_4588953 : CollatzResearch.WordTrace tailWord_4588953 prefixEnd_4588953 785446196630629811327765 := by
  unfold tailWord_4588953
  simp only [CollatzResearch.WordTrace]
  refine ⟨167372866144014486621515513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111581910762676324414343675 167372866144014486621515513)
  ·
    refine ⟨125529649608010864966136635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167372866144014486621515513 125529649608010864966136635)
    ·
      refine ⟨188294474412016297449204953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125529649608010864966136635 188294474412016297449204953)
      ·
        refine ⟨141220855809012223086903715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188294474412016297449204953 141220855809012223086903715)
        ·
          refine ⟨211831283713518334630355573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141220855809012223086903715 211831283713518334630355573)
          ·
            refine ⟨19859182848142343871595835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211831283713518334630355573 19859182848142343871595835)
            ·
              refine ⟨29788774272213515807393753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19859182848142343871595835 29788774272213515807393753)
              ·
                refine ⟨22341580704160136855545315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29788774272213515807393753 22341580704160136855545315)
                ·
                  refine ⟨33512371056240205283317973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22341580704160136855545315 33512371056240205283317973)
                  ·
                    refine ⟨785446196630629811327765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33512371056240205283317973 785446196630629811327765)
                    ·
                      rfl

theorem cell23_4588953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_4588953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4588953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4588953 prefixEnd_4588953 := by exact prefixLift 4588953
  have htrace : WordTrace (prefixWord ++ tailWord_4588953) baseStart_4588953 baseEnd_4588953 := by
    simpa [prefixWord, tailWord_4588953, baseEnd_4588953] using wordTrace_append hprefix tailTrace_4588953
  have hstable : (prefixWord ++ tailWord_4588953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4588953).length < 2 ^ (prefixWord ++ tailWord_4588953).sum := by decide
  have hdescent : baseEnd_4588953 < baseStart_4588953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4588953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589003 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 6]
def baseStart_4589003 : Nat := 118140960795 + 4589003 * 2 ^ 59
def prefixEnd_4589003 : Nat := 4983230072969 + 3 ^ 40 * 4589003 * 2
def baseEnd_4589003 : Nat := 2356364263924614238358065

theorem tailTrace_4589003 : CollatzResearch.WordTrace tailWord_4589003 prefixEnd_4589003 2356364263924614238358065 := by
  unfold tailWord_4589003
  simp only [CollatzResearch.WordTrace]
  refine ⟨167374689793833345160835663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111583126529222230107223775 167374689793833345160835663)
  ·
    refine ⟨251062034690750017741253495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167374689793833345160835663 251062034690750017741253495)
    ·
      refine ⟨376593052036125026611880243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251062034690750017741253495 376593052036125026611880243)
      ·
        refine ⟨564889578054187539917820365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376593052036125026611880243 564889578054187539917820365)
        ·
          refine ⟨211833591770320327469182637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 564889578054187539917820365 211833591770320327469182637)
          ·
            refine ⟨79437596913870122800943489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211833591770320327469182637 79437596913870122800943489)
            ·
              refine ⟨59578197685402592100707617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79437596913870122800943489 59578197685402592100707617)
              ·
                refine ⟨44683648264051944075530713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59578197685402592100707617 44683648264051944075530713)
                ·
                  refine ⟨33512736198038958056648035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44683648264051944075530713 33512736198038958056648035)
                  ·
                    refine ⟨50269104297058437084972053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33512736198038958056648035 50269104297058437084972053)
                    ·
                      refine ⟨2356364263924614238358065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50269104297058437084972053 2356364263924614238358065)
                      ·
                        rfl

theorem cell23_4589003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_4589003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589003 prefixEnd_4589003 := by exact prefixLift 4589003
  have htrace : WordTrace (prefixWord ++ tailWord_4589003) baseStart_4589003 baseEnd_4589003 := by
    simpa [prefixWord, tailWord_4589003, baseEnd_4589003] using wordTrace_append hprefix tailTrace_4589003
  have hstable : (prefixWord ++ tailWord_4589003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589003).length < 2 ^ (prefixWord ++ tailWord_4589003).sum := by decide
  have hdescent : baseEnd_4589003 < baseStart_4589003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589027 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 3]
def baseStart_4589027 : Nat := 118140960795 + 4589027 * 2 ^ 59
def prefixEnd_4589027 : Nat := 4983230072969 + 3 ^ 40 * 4589027 * 2
def baseEnd_4589027 : Nat := 2356376587460322144457955

theorem tailTrace_4589027 : CollatzResearch.WordTrace tailWord_4589027 prefixEnd_4589027 2356376587460322144457955 := by
  unfold tailWord_4589027
  simp only [CollatzResearch.WordTrace]
  refine ⟨167375565145746397259709335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111583710097164264839806223 167375565145746397259709335)
  ·
    refine ⟨251063347718619595889564003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167375565145746397259709335 251063347718619595889564003)
    ·
      refine ⟨376595021577929393834346005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251063347718619595889564003 376595021577929393834346005)
      ·
        refine ⟨17652891636465440335984969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 376595021577929393834346005 17652891636465440335984969)
        ·
          refine ⟨13239668727349080251988727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17652891636465440335984969 13239668727349080251988727)
          ·
            refine ⟨19859503091023620377983091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13239668727349080251988727 19859503091023620377983091)
            ·
              refine ⟨29789254636535430566974637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19859503091023620377983091 29789254636535430566974637)
              ·
                refine ⟨11170970488700786462615489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29789254636535430566974637 11170970488700786462615489)
                ·
                  refine ⟨8378227866525589846961617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11170970488700786462615489 8378227866525589846961617)
                  ·
                    refine ⟨6283670899894192385221213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8378227866525589846961617 6283670899894192385221213)
                    ·
                      refine ⟨2356376587460322144457955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6283670899894192385221213 2356376587460322144457955)
                      ·
                        rfl

theorem cell23_4589027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_4589027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589027 prefixEnd_4589027 := by exact prefixLift 4589027
  have htrace : WordTrace (prefixWord ++ tailWord_4589027) baseStart_4589027 baseEnd_4589027 := by
    simpa [prefixWord, tailWord_4589027, baseEnd_4589027] using wordTrace_append hprefix tailTrace_4589027
  have hstable : (prefixWord ++ tailWord_4589027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589027).length < 2 ^ (prefixWord ++ tailWord_4589027).sum := by decide
  have hdescent : baseEnd_4589027 < baseStart_4589027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589107 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 4, 4]
def baseStart_4589107 : Nat := 118140960795 + 4589107 * 2 ^ 59
def prefixEnd_4589107 : Nat := 4983230072969 + 3 ^ 40 * 4589107 * 2
def baseEnd_4589107 : Nat := 785472555304227277152529

theorem tailTrace_4589107 : CollatzResearch.WordTrace tailWord_4589107 prefixEnd_4589107 785472555304227277152529 := by
  unfold tailWord_4589107
  simp only [CollatzResearch.WordTrace]
  refine ⟨167378482985456570922621575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111585655323637713948414383 167378482985456570922621575)
  ·
    refine ⟨251067724478184856383932363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167378482985456570922621575 251067724478184856383932363)
    ·
      refine ⟨376601586717277284575898545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251067724478184856383932363 376601586717277284575898545)
      ·
        refine ⟨282451190037957963431923909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376601586717277284575898545 282451190037957963431923909)
        ·
          refine ⟨52959598132117118143485733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282451190037957963431923909 52959598132117118143485733)
          ·
            refine ⟨9929924649771959651903575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52959598132117118143485733 9929924649771959651903575)
            ·
              refine ⟨14894886974657939477855363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9929924649771959651903575 14894886974657939477855363)
              ·
                refine ⟨22342330461986909216783045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14894886974657939477855363 22342330461986909216783045)
                ·
                  refine ⟨4189186961622545478146821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22342330461986909216783045 4189186961622545478146821)
                  ·
                    refine ⟨785472555304227277152529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4189186961622545478146821 785472555304227277152529)
                    ·
                      rfl

theorem cell23_4589107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 4].length) (baseStart_4589107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589107 prefixEnd_4589107 := by exact prefixLift 4589107
  have htrace : WordTrace (prefixWord ++ tailWord_4589107) baseStart_4589107 baseEnd_4589107 := by
    simpa [prefixWord, tailWord_4589107, baseEnd_4589107] using wordTrace_append hprefix tailTrace_4589107
  have hstable : (prefixWord ++ tailWord_4589107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589107).length < 2 ^ (prefixWord ++ tailWord_4589107).sum := by decide
  have hdescent : baseEnd_4589107 < baseStart_4589107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589127 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_4589127 : Nat := 118140960795 + 4589127 * 2 ^ 59
def prefixEnd_4589127 : Nat := 4983230072969 + 3 ^ 40 * 4589127 * 2
def baseEnd_4589127 : Nat := 2356427935525771753207495

theorem tailTrace_4589127 : CollatzResearch.WordTrace tailWord_4589127 prefixEnd_4589127 2356427935525771753207495 := by
  unfold tailWord_4589127
  simp only [CollatzResearch.WordTrace]
  refine ⟨167379212445384114338349635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111586141630256076225566423 167379212445384114338349635)
  ·
    refine ⟨251068818668076171507524453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167379212445384114338349635 251068818668076171507524453)
    ·
      refine ⟨47075403500264282157660835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251068818668076171507524453 47075403500264282157660835)
      ·
        refine ⟨70613105250396423236491253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47075403500264282157660835 70613105250396423236491253)
        ·
          refine ⟨6619978617224664678421055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70613105250396423236491253 6619978617224664678421055)
          ·
            refine ⟨9929967925836997017631583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6619978617224664678421055 9929967925836997017631583)
            ·
              refine ⟨14894951888755495526447375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9929967925836997017631583 14894951888755495526447375)
              ·
                refine ⟨22342427833133243289671063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14894951888755495526447375 22342427833133243289671063)
                ·
                  refine ⟨33513641749699864934506595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22342427833133243289671063 33513641749699864934506595)
                  ·
                    refine ⟨50270462624549797401759893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33513641749699864934506595 50270462624549797401759893)
                    ·
                      refine ⟨2356427935525771753207495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50270462624549797401759893 2356427935525771753207495)
                      ·
                        rfl

theorem cell23_4589127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_4589127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589127 prefixEnd_4589127 := by exact prefixLift 4589127
  have htrace : WordTrace (prefixWord ++ tailWord_4589127) baseStart_4589127 baseEnd_4589127 := by
    simpa [prefixWord, tailWord_4589127, baseEnd_4589127] using wordTrace_append hprefix tailTrace_4589127
  have hstable : (prefixWord ++ tailWord_4589127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589127).length < 2 ^ (prefixWord ++ tailWord_4589127).sum := by decide
  have hdescent : baseEnd_4589127 < baseStart_4589127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589164 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_4589164 : Nat := 118140960795 + 4589164 * 2 ^ 59
def prefixEnd_4589164 : Nat := 4983230072969 + 3 ^ 40 * 4589164 * 2
def baseEnd_4589164 : Nat := 2356446934309988108444825

theorem tailTrace_4589164 : CollatzResearch.WordTrace tailWord_4589164 prefixEnd_4589164 2356446934309988108444825 := by
  unfold tailWord_4589164
  simp only [CollatzResearch.WordTrace]
  refine ⟨83690280973125034828723273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111587041297500046438297697 83690280973125034828723273)
  ·
    refine ⟨62767710729843776121542455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83690280973125034828723273 62767710729843776121542455)
    ·
      refine ⟨94151566094765664182313683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62767710729843776121542455 94151566094765664182313683)
      ·
        refine ⟨141227349142148496273470525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94151566094765664182313683 141227349142148496273470525)
        ·
          refine ⟨52960255928305686102551447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141227349142148496273470525 52960255928305686102551447)
          ·
            refine ⟨79440383892458529153827171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52960255928305686102551447 79440383892458529153827171)
            ·
              refine ⟨119160575838687793730740757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79440383892458529153827171 119160575838687793730740757)
              ·
                refine ⟨5585651992438490331128473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119160575838687793730740757 5585651992438490331128473)
                ·
                  refine ⟨4189238994328867748346355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585651992438490331128473 4189238994328867748346355)
                  ·
                    refine ⟨6283858491493301622519533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4189238994328867748346355 6283858491493301622519533)
                    ·
                      refine ⟨2356446934309988108444825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6283858491493301622519533 2356446934309988108444825)
                      ·
                        rfl

theorem cell23_4589164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_4589164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589164 prefixEnd_4589164 := by exact prefixLift 4589164
  have htrace : WordTrace (prefixWord ++ tailWord_4589164) baseStart_4589164 baseEnd_4589164 := by
    simpa [prefixWord, tailWord_4589164, baseEnd_4589164] using wordTrace_append hprefix tailTrace_4589164
  have hstable : (prefixWord ++ tailWord_4589164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589164).length < 2 ^ (prefixWord ++ tailWord_4589164).sum := by decide
  have hdescent : baseEnd_4589164 < baseStart_4589164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589165 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_4589165 : Nat := 118140960795 + 4589165 * 2 ^ 59
def prefixEnd_4589165 : Nat := 4983230072969 + 3 ^ 40 * 4589165 * 2
def baseEnd_4589165 : Nat := 2356447447790642604532321

theorem tailTrace_4589165 : CollatzResearch.WordTrace tailWord_4589165 prefixEnd_4589165 2356447447790642604532321 := by
  unfold tailWord_4589165
  simp only [CollatzResearch.WordTrace]
  refine ⟨167380598419246446828232949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111587065612830964552155299 167380598419246446828232949)
  ·
    refine ⟨15691931101804354390146839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167380598419246446828232949 15691931101804354390146839)
    ·
      refine ⟨23537896652706531585220259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15691931101804354390146839 23537896652706531585220259)
      ·
        refine ⟨35306844979059797377830389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23537896652706531585220259 35306844979059797377830389)
        ·
          refine ⟨3310016716786856004171599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35306844979059797377830389 3310016716786856004171599)
          ·
            refine ⟨4965025075180284006257399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310016716786856004171599 4965025075180284006257399)
            ·
              refine ⟨7447537612770426009386099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4965025075180284006257399 7447537612770426009386099)
              ·
                refine ⟨11171306419155639014079149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7447537612770426009386099 11171306419155639014079149)
                ·
                  refine ⟨4189239907183364630279681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11171306419155639014079149 4189239907183364630279681)
                  ·
                    refine ⟨3141929930387523472709761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4189239907183364630279681 3141929930387523472709761)
                    ·
                      refine ⟨2356447447790642604532321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141929930387523472709761 2356447447790642604532321)
                      ·
                        rfl

theorem cell23_4589165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_4589165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589165 prefixEnd_4589165 := by exact prefixLift 4589165
  have htrace : WordTrace (prefixWord ++ tailWord_4589165) baseStart_4589165 baseEnd_4589165 := by
    simpa [prefixWord, tailWord_4589165, baseEnd_4589165] using wordTrace_append hprefix tailTrace_4589165
  have hstable : (prefixWord ++ tailWord_4589165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589165).length < 2 ^ (prefixWord ++ tailWord_4589165).sum := by decide
  have hdescent : baseEnd_4589165 < baseStart_4589165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589180 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_4589180 : Nat := 118140960795 + 4589180 * 2 ^ 59
def prefixEnd_4589180 : Nat := 4983230072969 + 3 ^ 40 * 4589180 * 2
def baseEnd_4589180 : Nat := 785485050000153348614917

theorem tailTrace_4589180 : CollatzResearch.WordTrace tailWord_4589180 prefixEnd_4589180 785485050000153348614917 := by
  unfold tailWord_4589180
  simp only [CollatzResearch.WordTrace]
  refine ⟨83690572757096052195014497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111587430342794736260019329 83690572757096052195014497)
  ·
    refine ⟨62767929567822039146260873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83690572757096052195014497 62767929567822039146260873)
    ·
      refine ⟨47075947175866529359695655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62767929567822039146260873 47075947175866529359695655)
      ·
        refine ⟨70613920763799794039543483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47075947175866529359695655 70613920763799794039543483)
        ·
          refine ⟨105920881145699691059315225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70613920763799794039543483 105920881145699691059315225)
          ·
            refine ⟨79440660859274768294486419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105920881145699691059315225 79440660859274768294486419)
            ·
              refine ⟨119160991288912152441729629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79440660859274768294486419 119160991288912152441729629)
              ·
                refine ⟨44685371733342057165648611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119160991288912152441729629 44685371733342057165648611)
                ·
                  refine ⟨67028057600013085748472917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44685371733342057165648611 67028057600013085748472917)
                  ·
                    refine ⟨785485050000153348614917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67028057600013085748472917 785485050000153348614917)
                    ·
                      rfl

theorem cell23_4589180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_4589180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589180 prefixEnd_4589180 := by exact prefixLift 4589180
  have htrace : WordTrace (prefixWord ++ tailWord_4589180) baseStart_4589180 baseEnd_4589180 := by
    simpa [prefixWord, tailWord_4589180, baseEnd_4589180] using wordTrace_append hprefix tailTrace_4589180
  have hstable : (prefixWord ++ tailWord_4589180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589180).length < 2 ^ (prefixWord ++ tailWord_4589180).sum := by decide
  have hdescent : baseEnd_4589180 < baseStart_4589180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589181 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_4589181 : Nat := 118140960795 + 4589181 * 2 ^ 59
def prefixEnd_4589181 : Nat := 4983230072969 + 3 ^ 40 * 4589181 * 2
def baseEnd_4589181 : Nat := 2356455663481114541932247

theorem tailTrace_4589181 : CollatzResearch.WordTrace tailWord_4589181 prefixEnd_4589181 2356455663481114541932247 := by
  unfold tailWord_4589181
  simp only [CollatzResearch.WordTrace]
  refine ⟨167381181987188481560815397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111587454658125654373876931 167381181987188481560815397)
  ·
    refine ⟨31383971622597840292652887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167381181987188481560815397 31383971622597840292652887)
    ·
      refine ⟨47075957433896760438979331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31383971622597840292652887 47075957433896760438979331)
      ·
        refine ⟨70613936150845140658468997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47075957433896760438979331 70613936150845140658468997)
        ·
          refine ⟨13240113028283463873462937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70613936150845140658468997 13240113028283463873462937)
          ·
            refine ⟨9930084771212597905097203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13240113028283463873462937 9930084771212597905097203)
            ·
              refine ⟨14895127156818896857645805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9930084771212597905097203 14895127156818896857645805)
              ·
                refine ⟨5585672683807086321617177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14895127156818896857645805 5585672683807086321617177)
                ·
                  refine ⟨4189254512855314741212883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585672683807086321617177 4189254512855314741212883)
                  ·
                    refine ⟨6283881769282972111819325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4189254512855314741212883 6283881769282972111819325)
                    ·
                      refine ⟨2356455663481114541932247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6283881769282972111819325 2356455663481114541932247)
                      ·
                        rfl

theorem cell23_4589181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_4589181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589181 prefixEnd_4589181 := by exact prefixLift 4589181
  have htrace : WordTrace (prefixWord ++ tailWord_4589181) baseStart_4589181 baseEnd_4589181 := by
    simpa [prefixWord, tailWord_4589181, baseEnd_4589181] using wordTrace_append hprefix tailTrace_4589181
  have hstable : (prefixWord ++ tailWord_4589181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589181).length < 2 ^ (prefixWord ++ tailWord_4589181).sum := by decide
  have hdescent : baseEnd_4589181 < baseStart_4589181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589191 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_4589191 : Nat := 118140960795 + 4589191 * 2 ^ 59
def prefixEnd_4589191 : Nat := 4983230072969 + 3 ^ 40 * 4589191 * 2
def baseEnd_4589191 : Nat := 2356460798287659502807201

theorem tailTrace_4589191 : CollatzResearch.WordTrace tailWord_4589191 prefixEnd_4589191 2356460798287659502807201 := by
  unfold tailWord_4589191
  simp only [CollatzResearch.WordTrace]
  refine ⟨167381546717152253268679427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111587697811434835512452951 167381546717152253268679427)
  ·
    refine ⟨251072320075728379903019141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167381546717152253268679427 251072320075728379903019141)
    ·
      refine ⟨47076060014199071231816089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251072320075728379903019141 47076060014199071231816089)
      ·
        refine ⟨35307045010649303423862067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47076060014199071231816089 35307045010649303423862067)
        ·
          refine ⟨52960567515973955135793101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35307045010649303423862067 52960567515973955135793101)
          ·
            refine ⟨19860212818490233175922413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52960567515973955135793101 19860212818490233175922413)
            ·
              refine ⟨7447579806933837440970905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19860212818490233175922413 7447579806933837440970905)
              ·
                refine ⟨5585684855200378080728179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7447579806933837440970905 5585684855200378080728179)
                ·
                  refine ⟨8378527282800567121092269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5585684855200378080728179 8378527282800567121092269)
                  ·
                    refine ⟨3141947731050212670409601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8378527282800567121092269 3141947731050212670409601)
                    ·
                      refine ⟨2356460798287659502807201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141947731050212670409601 2356460798287659502807201)
                      ·
                        rfl

theorem cell23_4589191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_4589191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589191 prefixEnd_4589191 := by exact prefixLift 4589191
  have htrace : WordTrace (prefixWord ++ tailWord_4589191) baseStart_4589191 baseEnd_4589191 := by
    simpa [prefixWord, tailWord_4589191, baseEnd_4589191] using wordTrace_append hprefix tailTrace_4589191
  have hstable : (prefixWord ++ tailWord_4589191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589191).length < 2 ^ (prefixWord ++ tailWord_4589191).sum := by decide
  have hdescent : baseEnd_4589191 < baseStart_4589191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589207 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_4589207 : Nat := 118140960795 + 4589207 * 2 ^ 59
def prefixEnd_4589207 : Nat := 4983230072969 + 3 ^ 40 * 4589207 * 2
def baseEnd_4589207 : Nat := 2356469013978131440207127

theorem tailTrace_4589207 : CollatzResearch.WordTrace tailWord_4589207 prefixEnd_4589207 2356469013978131440207127 := by
  unfold tailWord_4589207
  simp only [CollatzResearch.WordTrace]
  refine ⟨167382130285094288001261875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111588086856729525334174583 167382130285094288001261875)
  ·
    refine ⟨251073195427641432001892813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167382130285094288001261875 251073195427641432001892813)
    ·
      refine ⟨94152448285365537000709805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251073195427641432001892813 94152448285365537000709805)
      ·
        refine ⟨35307168107012076375266177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94152448285365537000709805 35307168107012076375266177)
        ·
          refine ⟨26480376080259057281449633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35307168107012076375266177 26480376080259057281449633)
          ·
            refine ⟨19860282060194292961087225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26480376080259057281449633 19860282060194292961087225)
            ·
              refine ⟨14895211545145719720815419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19860282060194292961087225 14895211545145719720815419)
              ·
                refine ⟨22342817317718579581223129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14895211545145719720815419 22342817317718579581223129)
                ·
                  refine ⟨16757112988288934685917347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22342817317718579581223129 16757112988288934685917347)
                  ·
                    refine ⟨25135669482433402028876021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16757112988288934685917347 25135669482433402028876021)
                    ·
                      refine ⟨2356469013978131440207127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25135669482433402028876021 2356469013978131440207127)
                      ·
                        rfl

theorem cell23_4589207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_4589207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589207 prefixEnd_4589207 := by exact prefixLift 4589207
  have htrace : WordTrace (prefixWord ++ tailWord_4589207) baseStart_4589207 baseEnd_4589207 := by
    simpa [prefixWord, tailWord_4589207, baseEnd_4589207] using wordTrace_append hprefix tailTrace_4589207
  have hstable : (prefixWord ++ tailWord_4589207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589207).length < 2 ^ (prefixWord ++ tailWord_4589207).sum := by decide
  have hdescent : baseEnd_4589207 < baseStart_4589207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589208 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 1, 3, 2]
def baseStart_4589208 : Nat := 118140960795 + 4589208 * 2 ^ 59
def prefixEnd_4589208 : Nat := 4983230072969 + 3 ^ 40 * 4589208 * 2
def baseEnd_4589208 : Nat := 2356469527458785936294623

theorem tailTrace_4589208 : CollatzResearch.WordTrace tailWord_4589208 prefixEnd_4589208 2356469527458785936294623 := by
  unfold tailWord_4589208
  simp only [CollatzResearch.WordTrace]
  refine ⟨83691083379045332586024139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111588111172060443448032185 83691083379045332586024139)
  ·
    refine ⟨125536625068567998879036209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83691083379045332586024139 125536625068567998879036209)
    ·
      refine ⟨94152468801425999159277157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125536625068567998879036209 94152468801425999159277157)
      ·
        refine ⟨17653587900267374842364467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94152468801425999159277157 17653587900267374842364467)
        ·
          refine ⟨26480381850401062263546701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17653587900267374842364467 26480381850401062263546701)
          ·
            refine ⟨9930143193900398348830013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26480381850401062263546701 9930143193900398348830013)
            ·
              refine ⟨3723803697712649380811255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9930143193900398348830013 3723803697712649380811255)
              ·
                refine ⟨5585705546568974071216883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723803697712649380811255 5585705546568974071216883)
                ·
                  refine ⟨8378558319853461106825325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5585705546568974071216883 8378558319853461106825325)
                  ·
                    refine ⟨3141959369945047915059497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8378558319853461106825325 3141959369945047915059497)
                    ·
                      refine ⟨2356469527458785936294623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141959369945047915059497 2356469527458785936294623)
                      ·
                        rfl

theorem cell23_4589208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_4589208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589208 prefixEnd_4589208 := by exact prefixLift 4589208
  have htrace : WordTrace (prefixWord ++ tailWord_4589208) baseStart_4589208 baseEnd_4589208 := by
    simpa [prefixWord, tailWord_4589208, baseEnd_4589208] using wordTrace_append hprefix tailTrace_4589208
  have hstable : (prefixWord ++ tailWord_4589208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589208).length < 2 ^ (prefixWord ++ tailWord_4589208).sum := by decide
  have hdescent : baseEnd_4589208 < baseStart_4589208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589221 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 2, 2, 2]
def baseStart_4589221 : Nat := 118140960795 + 4589221 * 2 ^ 59
def prefixEnd_4589221 : Nat := 4983230072969 + 3 ^ 40 * 4589221 * 2
def baseEnd_4589221 : Nat := 2356476202707294385432063

theorem tailTrace_4589221 : CollatzResearch.WordTrace tailWord_4589221 prefixEnd_4589221 2356476202707294385432063 := by
  unfold tailWord_4589221
  simp only [CollatzResearch.WordTrace]
  refine ⟨167382640907043568392271517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111588427271362378928181011 167382640907043568392271517)
  ·
    refine ⟨62768490340141338147101819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167382640907043568392271517 62768490340141338147101819)
    ·
      refine ⟨94152735510212007220652729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62768490340141338147101819 94152735510212007220652729)
      ·
        refine ⟨70614551632659005415489547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94152735510212007220652729 70614551632659005415489547)
        ·
          refine ⟨105921827448988508123234321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70614551632659005415489547 105921827448988508123234321)
          ·
            refine ⟨79441370586741381092425741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105921827448988508123234321 79441370586741381092425741)
            ·
              refine ⟨29790513970028017909659653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79441370586741381092425741 29790513970028017909659653)
              ·
                refine ⟨5585721369380253358061185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29790513970028017909659653 5585721369380253358061185)
                ·
                  refine ⟨4189291027035190018545889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585721369380253358061185 4189291027035190018545889)
                  ·
                    refine ⟨3141968270276392513909417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4189291027035190018545889 3141968270276392513909417)
                    ·
                      refine ⟨2356476202707294385432063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141968270276392513909417 2356476202707294385432063)
                      ·
                        rfl

theorem cell23_4589221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_4589221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589221 prefixEnd_4589221 := by exact prefixLift 4589221
  have htrace : WordTrace (prefixWord ++ tailWord_4589221) baseStart_4589221 baseEnd_4589221 := by
    simpa [prefixWord, tailWord_4589221, baseEnd_4589221] using wordTrace_append hprefix tailTrace_4589221
  have hstable : (prefixWord ++ tailWord_4589221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589221).length < 2 ^ (prefixWord ++ tailWord_4589221).sum := by decide
  have hdescent : baseEnd_4589221 < baseStart_4589221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589238 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_4589238 : Nat := 118140960795 + 4589238 * 2 ^ 59
def prefixEnd_4589238 : Nat := 4983230072969 + 3 ^ 40 * 4589238 * 2
def baseEnd_4589238 : Nat := 2356484931878420818919485

theorem tailTrace_4589238 : CollatzResearch.WordTrace tailWord_4589238 prefixEnd_4589238 2356484931878420818919485 := by
  unfold tailWord_4589238
  simp only [CollatzResearch.WordTrace]
  refine ⟨10461453809248873768477523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111588840631987986863760245 10461453809248873768477523)
  ·
    refine ⟨15692180713873310652716285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10461453809248873768477523 15692180713873310652716285)
    ·
      refine ⟨5884567767702491494768607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15692180713873310652716285 5884567767702491494768607)
      ·
        refine ⟨8826851651553737242152911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5884567767702491494768607 8826851651553737242152911)
        ·
          refine ⟨13240277477330605863229367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8826851651553737242152911 13240277477330605863229367)
          ·
            refine ⟨19860416215995908794844051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13240277477330605863229367 19860416215995908794844051)
            ·
              refine ⟨29790624323993863192266077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19860416215995908794844051 29790624323993863192266077)
              ·
                refine ⟨11171484121497698697099779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29790624323993863192266077 11171484121497698697099779)
                ·
                  refine ⟨16757226182246548045649669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11171484121497698697099779 16757226182246548045649669)
                  ·
                    refine ⟨3141979909171227758559313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16757226182246548045649669 3141979909171227758559313)
                    ·
                      refine ⟨2356484931878420818919485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3141979909171227758559313 2356484931878420818919485)
                      ·
                        rfl

theorem cell23_4589238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_4589238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589238 prefixEnd_4589238 := by exact prefixLift 4589238
  have htrace : WordTrace (prefixWord ++ tailWord_4589238) baseStart_4589238 baseEnd_4589238 := by
    simpa [prefixWord, tailWord_4589238, baseEnd_4589238] using wordTrace_append hprefix tailTrace_4589238
  have hstable : (prefixWord ++ tailWord_4589238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589238).length < 2 ^ (prefixWord ++ tailWord_4589238).sum := by decide
  have hdescent : baseEnd_4589238 < baseStart_4589238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589381 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_4589381 : Nat := 118140960795 + 4589381 * 2 ^ 59
def prefixEnd_4589381 : Nat := 4983230072969 + 3 ^ 40 * 4589381 * 2
def baseEnd_4589381 : Nat := 785519453204004586477109

theorem tailTrace_4589381 : CollatzResearch.WordTrace tailWord_4589381 prefixEnd_4589381 785519453204004586477109 := by
  unfold tailWord_4589381
  simp only [CollatzResearch.WordTrace]
  refine ⟨167388476586463915718095997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111592317724309277145397331 167388476586463915718095997)
  ·
    refine ⟨62770678719923968394285999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167388476586463915718095997 62770678719923968394285999)
    ·
      refine ⟨94156018079885952591428999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62770678719923968394285999 94156018079885952591428999)
      ·
        refine ⟨141234027119828928887143499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94156018079885952591428999 141234027119828928887143499)
        ·
          refine ⟨211851040679743393330715249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141234027119828928887143499 211851040679743393330715249)
          ·
            refine ⟨158888280509807544998036437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211851040679743393330715249 158888280509807544998036437)
            ·
              refine ⟨3723944074448614335891479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 158888280509807544998036437 3723944074448614335891479)
              ·
                refine ⟨5585916111672921503837219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723944074448614335891479 5585916111672921503837219)
                ·
                  refine ⟨8378874167509382255755829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5585916111672921503837219 8378874167509382255755829)
                  ·
                    refine ⟨785519453204004586477109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8378874167509382255755829 785519453204004586477109)
                    ·
                      rfl

theorem cell23_4589381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_4589381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589381 prefixEnd_4589381 := by exact prefixLift 4589381
  have htrace : WordTrace (prefixWord ++ tailWord_4589381) baseStart_4589381 baseEnd_4589381 := by
    simpa [prefixWord, tailWord_4589381, baseEnd_4589381] using wordTrace_append hprefix tailTrace_4589381
  have hstable : (prefixWord ++ tailWord_4589381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589381).length < 2 ^ (prefixWord ++ tailWord_4589381).sum := by decide
  have hdescent : baseEnd_4589381 < baseStart_4589381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589411 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 1, 6]
def baseStart_4589411 : Nat := 118140960795 + 4589411 * 2 ^ 59
def prefixEnd_4589411 : Nat := 4983230072969 + 3 ^ 40 * 4589411 * 2
def baseEnd_4589411 : Nat := 785524588010549547352063

theorem tailTrace_4589411 : CollatzResearch.WordTrace tailWord_4589411 prefixEnd_4589411 785524588010549547352063 := by
  unfold tailWord_4589411
  simp only [CollatzResearch.WordTrace]
  refine ⟨167389570776355230841688087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111593047184236820561125391 167389570776355230841688087)
  ·
    refine ⟨251084356164532846262532131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167389570776355230841688087 251084356164532846262532131)
    ·
      refine ⟨376626534246799269393798197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251084356164532846262532131 376626534246799269393798197)
      ·
        refine ⟨35308737585637431505668581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 376626534246799269393798197 35308737585637431505668581)
        ·
          refine ⟨6620388297307018407312859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35308737585637431505668581 6620388297307018407312859)
          ·
            refine ⟨9930582445960527610969289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6620388297307018407312859 9930582445960527610969289)
            ·
              refine ⟨7447936834470395708226967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9930582445960527610969289 7447936834470395708226967)
              ·
                refine ⟨11171905251705593562340451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7447936834470395708226967 11171905251705593562340451)
                ·
                  refine ⟨16757857877558390343510677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11171905251705593562340451 16757857877558390343510677)
                  ·
                    refine ⟨785524588010549547352063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16757857877558390343510677 785524588010549547352063)
                    ·
                      rfl

theorem cell23_4589411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 6].length) (baseStart_4589411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589411 prefixEnd_4589411 := by exact prefixLift 4589411
  have htrace : WordTrace (prefixWord ++ tailWord_4589411) baseStart_4589411 baseEnd_4589411 := by
    simpa [prefixWord, tailWord_4589411, baseEnd_4589411] using wordTrace_append hprefix tailTrace_4589411
  have hstable : (prefixWord ++ tailWord_4589411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589411).length < 2 ^ (prefixWord ++ tailWord_4589411).sum := by decide
  have hdescent : baseEnd_4589411 < baseStart_4589411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589417 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_4589417 : Nat := 118140960795 + 4589417 * 2 ^ 59
def prefixEnd_4589417 : Nat := 4983230072969 + 3 ^ 40 * 4589417 * 2
def baseEnd_4589417 : Nat := 2356576844915575618581161

theorem tailTrace_4589417 : CollatzResearch.WordTrace tailWord_4589417 prefixEnd_4589417 2356576844915575618581161 := by
  unfold tailWord_4589417
  simp only [CollatzResearch.WordTrace]
  refine ⟨167389789614333493866406505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111593193076222329244271003 167389789614333493866406505)
  ·
    refine ⟨125542342210750120399804879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167389789614333493866406505 125542342210750120399804879)
    ·
      refine ⟨188313513316125180599707319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125542342210750120399804879 188313513316125180599707319)
      ·
        refine ⟨282470269974187770899560979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188313513316125180599707319 282470269974187770899560979)
        ·
          refine ⟨423705404961281656349341469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282470269974187770899560979 423705404961281656349341469)
          ·
            refine ⟨158889526860480621131003051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 423705404961281656349341469 158889526860480621131003051)
            ·
              refine ⟨238334290290720931696504577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158889526860480621131003051 238334290290720931696504577)
              ·
                refine ⟨178750717718040698772378433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238334290290720931696504577 178750717718040698772378433)
                ·
                  refine ⟨134063038288530524079283825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178750717718040698772378433 134063038288530524079283825)
                  ·
                    refine ⟨100547278716397893059462869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134063038288530524079283825 100547278716397893059462869)
                    ·
                      refine ⟨2356576844915575618581161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100547278716397893059462869 2356576844915575618581161)
                      ·
                        rfl

theorem cell23_4589417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_4589417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589417 prefixEnd_4589417 := by exact prefixLift 4589417
  have htrace : WordTrace (prefixWord ++ tailWord_4589417) baseStart_4589417 baseEnd_4589417 := by
    simpa [prefixWord, tailWord_4589417, baseEnd_4589417] using wordTrace_append hprefix tailTrace_4589417
  have hstable : (prefixWord ++ tailWord_4589417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589417).length < 2 ^ (prefixWord ++ tailWord_4589417).sum := by decide
  have hdescent : baseEnd_4589417 < baseStart_4589417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589421 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_4589421 : Nat := 118140960795 + 4589421 * 2 ^ 59
def prefixEnd_4589421 : Nat := 4983230072969 + 3 ^ 40 * 4589421 * 2
def baseEnd_4589421 : Nat := 2356578898838193602931143

theorem tailTrace_4589421 : CollatzResearch.WordTrace tailWord_4589421 prefixEnd_4589421 2356578898838193602931143 := by
  unfold tailWord_4589421
  simp only [CollatzResearch.WordTrace]
  refine ⟨167389935506319002549552117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111593290337546001699701411 167389935506319002549552117)
  ·
    refine ⟨15692806453717406489020511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167389935506319002549552117 15692806453717406489020511)
    ·
      refine ⟨23539209680576109733530767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15692806453717406489020511 23539209680576109733530767)
      ·
        refine ⟨35308814520864164600296151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23539209680576109733530767 35308814520864164600296151)
        ·
          refine ⟨52963221781296246900444227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35308814520864164600296151 52963221781296246900444227)
          ·
            refine ⟨79444832671944370350666341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52963221781296246900444227 79444832671944370350666341)
            ·
              refine ⟨14895906125989569440749939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79444832671944370350666341 14895906125989569440749939)
              ·
                refine ⟨22343859188984354161124909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14895906125989569440749939 22343859188984354161124909)
                ·
                  refine ⟨8378947195869132810421841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22343859188984354161124909 8378947195869132810421841)
                  ·
                    refine ⟨6284210396901849607816381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8378947195869132810421841 6284210396901849607816381)
                    ·
                      refine ⟨2356578898838193602931143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6284210396901849607816381 2356578898838193602931143)
                      ·
                        rfl

theorem cell23_4589421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_4589421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589421 prefixEnd_4589421 := by exact prefixLift 4589421
  have htrace : WordTrace (prefixWord ++ tailWord_4589421) baseStart_4589421 baseEnd_4589421 := by
    simpa [prefixWord, tailWord_4589421, baseEnd_4589421] using wordTrace_append hprefix tailTrace_4589421
  have hstable : (prefixWord ++ tailWord_4589421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589421).length < 2 ^ (prefixWord ++ tailWord_4589421).sum := by decide
  have hdescent : baseEnd_4589421 < baseStart_4589421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589441 : List Nat := [1, 2, 4, 4, 1, 1, 10]
def baseStart_4589441 : Nat := 118140960795 + 4589441 * 2 ^ 59
def prefixEnd_4589441 : Nat := 4983230072969 + 3 ^ 40 * 4589441 * 2
def baseEnd_4589441 : Nat := 29093693437670166971371

theorem tailTrace_4589441 : CollatzResearch.WordTrace tailWord_4589441 prefixEnd_4589441 29093693437670166971371 := by
  unfold tailWord_4589441
  simp only [CollatzResearch.WordTrace]
  refine ⟨167390664966246545965280177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111593776644164363976853451 167390664966246545965280177)
  ·
    refine ⟨125542998724684909473960133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167390664966246545965280177 125542998724684909473960133)
    ·
      refine ⟨23539312260878420526367525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125542998724684909473960133 23539312260878420526367525)
      ·
        refine ⟨4413621048914703848693911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23539312260878420526367525 4413621048914703848693911)
        ·
          refine ⟨6620431573372055773040867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4413621048914703848693911 6620431573372055773040867)
          ·
            refine ⟨9930647360058083659561301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6620431573372055773040867 9930647360058083659561301)
            ·
              refine ⟨29093693437670166971371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9930647360058083659561301 29093693437670166971371)
              ·
                rfl

theorem cell23_4589441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 10].length) (baseStart_4589441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589441 prefixEnd_4589441 := by exact prefixLift 4589441
  have htrace : WordTrace (prefixWord ++ tailWord_4589441) baseStart_4589441 baseEnd_4589441 := by
    simpa [prefixWord, tailWord_4589441, baseEnd_4589441] using wordTrace_append hprefix tailTrace_4589441
  have hstable : (prefixWord ++ tailWord_4589441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589441).length < 2 ^ (prefixWord ++ tailWord_4589441).sum := by decide
  have hdescent : baseEnd_4589441 < baseStart_4589441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589462 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4589462 : Nat := 118140960795 + 4589462 * 2 ^ 59
def prefixEnd_4589462 : Nat := 4983230072969 + 3 ^ 40 * 4589462 * 2
def baseEnd_4589462 : Nat := 785533317181675980839485

theorem tailTrace_4589462 : CollatzResearch.WordTrace tailWord_4589462 prefixEnd_4589462 785533317181675980839485 := by
  unfold tailWord_4589462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10461964431198154159487165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111594287266113644367863093 10461964431198154159487165)
  ·
    refine ⟨3923236661699307809807687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10461964431198154159487165 3923236661699307809807687)
    ·
      refine ⟨5884854992548961714711531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3923236661699307809807687 5884854992548961714711531)
      ·
        refine ⟨8827282488823442572067297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5884854992548961714711531 8827282488823442572067297)
        ·
          refine ⟨6620461866617581929050473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8827282488823442572067297 6620461866617581929050473)
          ·
            refine ⟨4965346399963186446787855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6620461866617581929050473 4965346399963186446787855)
            ·
              refine ⟨7448019599944779670181783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4965346399963186446787855 7448019599944779670181783)
              ·
                refine ⟨11172029399917169505272675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7448019599944779670181783 11172029399917169505272675)
                ·
                  refine ⟨16758044099875754257909013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11172029399917169505272675 16758044099875754257909013)
                  ·
                    refine ⟨785533317181675980839485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16758044099875754257909013 785533317181675980839485)
                    ·
                      rfl

theorem cell23_4589462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4589462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589462 prefixEnd_4589462 := by exact prefixLift 4589462
  have htrace : WordTrace (prefixWord ++ tailWord_4589462) baseStart_4589462 baseEnd_4589462 := by
    simpa [prefixWord, tailWord_4589462, baseEnd_4589462] using wordTrace_append hprefix tailTrace_4589462
  have hstable : (prefixWord ++ tailWord_4589462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589462).length < 2 ^ (prefixWord ++ tailWord_4589462).sum := by decide
  have hdescent : baseEnd_4589462 < baseStart_4589462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589468 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4589468 : Nat := 118140960795 + 4589468 * 2 ^ 59
def prefixEnd_4589468 : Nat := 4983230072969 + 3 ^ 40 * 4589468 * 2
def baseEnd_4589468 : Nat := 2356603032428954919043427

theorem tailTrace_4589468 : CollatzResearch.WordTrace tailWord_4589468 prefixEnd_4589468 2356603032428954919043427 := by
  unfold tailWord_4589468
  simp only [CollatzResearch.WordTrace]
  refine ⟨83695824868574364788256529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111594433158099153051008705 83695824868574364788256529)
  ·
    refine ⟨62771868651430773591192397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83695824868574364788256529 62771868651430773591192397)
    ·
      refine ⟨23539450744286540096697149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62771868651430773591192397 23539450744286540096697149)
      ·
        refine ⟨8827294029107452536261431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23539450744286540096697149 8827294029107452536261431)
        ·
          refine ⟨13240941043661178804392147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8827294029107452536261431 13240941043661178804392147)
          ·
            refine ⟨19861411565491768206588221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13240941043661178804392147 19861411565491768206588221)
            ·
              refine ⟨7448029337059413077470583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19861411565491768206588221 7448029337059413077470583)
              ·
                refine ⟨11172044005589119616205875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7448029337059413077470583 11172044005589119616205875)
                ·
                  refine ⟨16758066008383679424308813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11172044005589119616205875 16758066008383679424308813)
                  ·
                    refine ⟨6284274753143879784115805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16758066008383679424308813 6284274753143879784115805)
                    ·
                      refine ⟨2356603032428954919043427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6284274753143879784115805 2356603032428954919043427)
                      ·
                        rfl

theorem cell23_4589468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4589468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589468 prefixEnd_4589468 := by exact prefixLift 4589468
  have htrace : WordTrace (prefixWord ++ tailWord_4589468) baseStart_4589468 baseEnd_4589468 := by
    simpa [prefixWord, tailWord_4589468, baseEnd_4589468] using wordTrace_append hprefix tailTrace_4589468
  have hstable : (prefixWord ++ tailWord_4589468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589468).length < 2 ^ (prefixWord ++ tailWord_4589468).sum := by decide
  have hdescent : baseEnd_4589468 < baseStart_4589468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589491 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 3, 4, 2]
def baseStart_4589491 : Nat := 118140960795 + 4589491 * 2 ^ 59
def prefixEnd_4589491 : Nat := 4983230072969 + 3 ^ 40 * 4589491 * 2
def baseEnd_4589491 : Nat := 2356614842484008329055821

theorem tailTrace_4589491 : CollatzResearch.WordTrace tailWord_4589491 prefixEnd_4589491 2356614842484008329055821 := by
  unfold tailWord_4589491
  simp only [CollatzResearch.WordTrace]
  refine ⟨167392488616065404504600327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111594992410710269669733551 167392488616065404504600327)
  ·
    refine ⟨251088732924098106756900491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167392488616065404504600327 251088732924098106756900491)
    ·
      refine ⟨376633099386147160135350737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251088732924098106756900491 376633099386147160135350737)
      ·
        refine ⟨282474824539610370101513053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376633099386147160135350737 282474824539610370101513053)
        ·
          refine ⟨105928059202353888788067395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282474824539610370101513053 105928059202353888788067395)
          ·
            refine ⟨158892088803530833182101093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105928059202353888788067395 158892088803530833182101093)
            ·
              refine ⟨29792266650662031221643955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158892088803530833182101093 29792266650662031221643955)
              ·
                refine ⟨44688399975993046832465933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29792266650662031221643955 44688399975993046832465933)
                ·
                  refine ⟨16758149990997392562174725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44688399975993046832465933 16758149990997392562174725)
                  ·
                    refine ⟨3142153123312011105407761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16758149990997392562174725 3142153123312011105407761)
                    ·
                      refine ⟨2356614842484008329055821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142153123312011105407761 2356614842484008329055821)
                      ·
                        rfl

theorem cell23_4589491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 4, 2].length) (baseStart_4589491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589491 prefixEnd_4589491 := by exact prefixLift 4589491
  have htrace : WordTrace (prefixWord ++ tailWord_4589491) baseStart_4589491 baseEnd_4589491 := by
    simpa [prefixWord, tailWord_4589491, baseEnd_4589491] using wordTrace_append hprefix tailTrace_4589491
  have hstable : (prefixWord ++ tailWord_4589491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589491).length < 2 ^ (prefixWord ++ tailWord_4589491).sum := by decide
  have hdescent : baseEnd_4589491 < baseStart_4589491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589561 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 2, 5]
def baseStart_4589561 : Nat := 118140960795 + 4589561 * 2 ^ 59
def prefixEnd_4589561 : Nat := 4983230072969 + 3 ^ 40 * 4589561 * 2
def baseEnd_4589561 : Nat := 785550262043274351726833

theorem tailTrace_4589561 : CollatzResearch.WordTrace tailWord_4589561 prefixEnd_4589561 785550262043274351726833 := by
  unfold tailWord_4589561
  simp only [CollatzResearch.WordTrace]
  refine ⟨167395041725811806459648537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111596694483874537639765691 167395041725811806459648537)
  ·
    refine ⟨125546281294358854844736403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167395041725811806459648537 125546281294358854844736403)
    ·
      refine ⟨188319421941538282267104605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125546281294358854844736403 188319421941538282267104605)
      ·
        refine ⟨70619783228076855850164227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188319421941538282267104605 70619783228076855850164227)
        ·
          refine ⟨105929674842115283775246341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70619783228076855850164227 105929674842115283775246341)
          ·
            refine ⟨19861814032896615707858689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105929674842115283775246341 19861814032896615707858689)
            ·
              refine ⟨14896360524672461780894017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19861814032896615707858689 14896360524672461780894017)
              ·
                refine ⟨11172270393504346335670513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14896360524672461780894017 11172270393504346335670513)
                ·
                  refine ⟨8379202795128259751752885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11172270393504346335670513 8379202795128259751752885)
                  ·
                    refine ⟨785550262043274351726833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8379202795128259751752885 785550262043274351726833)
                    ·
                      rfl

theorem cell23_4589561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_4589561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589561 prefixEnd_4589561 := by exact prefixLift 4589561
  have htrace : WordTrace (prefixWord ++ tailWord_4589561) baseStart_4589561 baseEnd_4589561 := by
    simpa [prefixWord, tailWord_4589561, baseEnd_4589561] using wordTrace_append hprefix tailTrace_4589561
  have hstable : (prefixWord ++ tailWord_4589561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589561).length < 2 ^ (prefixWord ++ tailWord_4589561).sum := by decide
  have hdescent : baseEnd_4589561 < baseStart_4589561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589584 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_4589584 : Nat := 118140960795 + 4589584 * 2 ^ 59
def prefixEnd_4589584 : Nat := 4983230072969 + 3 ^ 40 * 4589584 * 2
def baseEnd_4589584 : Nat := 2356662596184876465192893

theorem tailTrace_4589584 : CollatzResearch.WordTrace tailWord_4589584 prefixEnd_4589584 2356662596184876465192893 := by
  unfold tailWord_4589584
  simp only [CollatzResearch.WordTrace]
  refine ⟨83697940302364240693867903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111597253736485654258490537 83697940302364240693867903)
  ·
    refine ⟨125546910453546361040801855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83697940302364240693867903 125546910453546361040801855)
    ·
      refine ⟨188320365680319541561202783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125546910453546361040801855 188320365680319541561202783)
      ·
        refine ⟨282480548520479312341804175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188320365680319541561202783 282480548520479312341804175)
        ·
          refine ⟨423720822780718968512706263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282480548520479312341804175 423720822780718968512706263)
          ·
            refine ⟨635581234171078452769059395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423720822780718968512706263 635581234171078452769059395)
            ·
              refine ⟨953371851256617679153589093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635581234171078452769059395 953371851256617679153589093)
              ·
                refine ⟨178757222110615814841297955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 953371851256617679153589093 178757222110615814841297955)
                ·
                  refine ⟨268135833165923722261946933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178757222110615814841297955 268135833165923722261946933)
                  ·
                    refine ⟨25137734359305348962057525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 268135833165923722261946933 25137734359305348962057525)
                    ·
                      refine ⟨2356662596184876465192893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25137734359305348962057525 2356662596184876465192893)
                      ·
                        rfl

theorem cell23_4589584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_4589584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589584 prefixEnd_4589584 := by exact prefixLift 4589584
  have htrace : WordTrace (prefixWord ++ tailWord_4589584) baseStart_4589584 baseEnd_4589584 := by
    simpa [prefixWord, tailWord_4589584, baseEnd_4589584] using wordTrace_append hprefix tailTrace_4589584
  have hstable : (prefixWord ++ tailWord_4589584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589584).length < 2 ^ (prefixWord ++ tailWord_4589584).sum := by decide
  have hdescent : baseEnd_4589584 < baseStart_4589584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589625 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 3, 4]
def baseStart_4589625 : Nat := 118140960795 + 4589625 * 2 ^ 59
def prefixEnd_4589625 : Nat := 4983230072969 + 3 ^ 40 * 4589625 * 2
def baseEnd_4589625 : Nat := 785561216297236934926735

theorem tailTrace_4589625 : CollatzResearch.WordTrace tailWord_4589625 prefixEnd_4589625 785561216297236934926735 := by
  unfold tailWord_4589625
  simp only [CollatzResearch.WordTrace]
  refine ⟨167397375997579945389978329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111598250665053296926652219 167397375997579945389978329)
  ·
    refine ⟨125548031998184959042483747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167397375997579945389978329 125548031998184959042483747)
    ·
      refine ⟨188322047997277438563725621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125548031998184959042483747 188322047997277438563725621)
      ·
        refine ⟨17655191999744759865349277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188322047997277438563725621 17655191999744759865349277)
        ·
          refine ⟨6620696999904284949505979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17655191999744759865349277 6620696999904284949505979)
          ·
            refine ⟨9931045499856427424258969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6620696999904284949505979 9931045499856427424258969)
            ·
              refine ⟨7448284124892320568194227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9931045499856427424258969 7448284124892320568194227)
              ·
                refine ⟨11172426187338480852291341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7448284124892320568194227 11172426187338480852291341)
                ·
                  refine ⟨4189659820251930319609253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11172426187338480852291341 4189659820251930319609253)
                  ·
                    refine ⟨785561216297236934926735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4189659820251930319609253 785561216297236934926735)
                    ·
                      rfl

theorem cell23_4589625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 4].length) (baseStart_4589625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589625 prefixEnd_4589625 := by exact prefixLift 4589625
  have htrace : WordTrace (prefixWord ++ tailWord_4589625) baseStart_4589625 baseEnd_4589625 := by
    simpa [prefixWord, tailWord_4589625, baseEnd_4589625] using wordTrace_append hprefix tailTrace_4589625
  have hstable : (prefixWord ++ tailWord_4589625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589625).length < 2 ^ (prefixWord ++ tailWord_4589625).sum := by decide
  have hdescent : baseEnd_4589625 < baseStart_4589625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589658 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2]
def baseStart_4589658 : Nat := 118140960795 + 4589658 * 2 ^ 59
def prefixEnd_4589658 : Nat := 4983230072969 + 3 ^ 40 * 4589658 * 2
def baseEnd_4589658 : Nat := 2356700593753309175667553

theorem tailTrace_4589658 : CollatzResearch.WordTrace tailWord_4589658 prefixEnd_4589658 2356700593753309175667553 := by
  unfold tailWord_4589658
  simp only [CollatzResearch.WordTrace]
  refine ⟨41849644901615098006482407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111599053070973594683953085 41849644901615098006482407)
  ·
    refine ⟨62774467352422647009723611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41849644901615098006482407 62774467352422647009723611)
    ·
      refine ⟨94161701028633970514585417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62774467352422647009723611 94161701028633970514585417)
      ·
        refine ⟨70621275771475477885939063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94161701028633970514585417 70621275771475477885939063)
        ·
          refine ⟨105931913657213216828908595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70621275771475477885939063 105931913657213216828908595)
          ·
            refine ⟨158897870485819825243362893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105931913657213216828908595 158897870485819825243362893)
            ·
              refine ⟨59586701432182434466261085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158897870485819825243362893 59586701432182434466261085)
              ·
                refine ⟨22345013037068412924847907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59586701432182434466261085 22345013037068412924847907)
                ·
                  refine ⟨33517519555602619387271861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22345013037068412924847907 33517519555602619387271861)
                  ·
                    refine ⟨3142267458337745567556737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33517519555602619387271861 3142267458337745567556737)
                    ·
                      refine ⟨2356700593753309175667553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142267458337745567556737 2356700593753309175667553)
                      ·
                        rfl

theorem cell23_4589658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_4589658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589658 prefixEnd_4589658 := by exact prefixLift 4589658
  have htrace : WordTrace (prefixWord ++ tailWord_4589658) baseStart_4589658 baseEnd_4589658 := by
    simpa [prefixWord, tailWord_4589658, baseEnd_4589658] using wordTrace_append hprefix tailTrace_4589658
  have hstable : (prefixWord ++ tailWord_4589658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589658).length < 2 ^ (prefixWord ++ tailWord_4589658).sum := by decide
  have hdescent : baseEnd_4589658 < baseStart_4589658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589668 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_4589668 : Nat := 118140960795 + 4589668 * 2 ^ 59
def prefixEnd_4589668 : Nat := 4983230072969 + 3 ^ 40 * 4589668 * 2
def baseEnd_4589668 : Nat := 785568576186618045514169

theorem tailTrace_4589668 : CollatzResearch.WordTrace tailWord_4589668 prefixEnd_4589668 785568576186618045514169 := by
  unfold tailWord_4589668
  simp only [CollatzResearch.WordTrace]
  refine ⟨83699472168212081866896829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111599296224282775822529105 83699472168212081866896829)
  ·
    refine ⟨31387302063079530700086311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83699472168212081866896829 31387302063079530700086311)
    ·
      refine ⟨47080953094619296050129467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31387302063079530700086311 47080953094619296050129467)
      ·
        refine ⟨70621429641928944075194201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47080953094619296050129467 70621429641928944075194201)
        ·
          refine ⟨52966072231446708056395651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70621429641928944075194201 52966072231446708056395651)
          ·
            refine ⟨79449108347170062084593477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52966072231446708056395651 79449108347170062084593477)
            ·
              refine ⟨14896707815094386640861277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79449108347170062084593477 14896707815094386640861277)
              ·
                refine ⟨5586265430660394990322979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14896707815094386640861277 5586265430660394990322979)
                ·
                  refine ⟨8379398145990592485484469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5586265430660394990322979 8379398145990592485484469)
                  ·
                    refine ⟨785568576186618045514169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8379398145990592485484469 785568576186618045514169)
                    ·
                      rfl

theorem cell23_4589668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_4589668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589668 prefixEnd_4589668 := by exact prefixLift 4589668
  have htrace : WordTrace (prefixWord ++ tailWord_4589668) baseStart_4589668 baseEnd_4589668 := by
    simpa [prefixWord, tailWord_4589668, baseEnd_4589668] using wordTrace_append hprefix tailTrace_4589668
  have hstable : (prefixWord ++ tailWord_4589668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589668).length < 2 ^ (prefixWord ++ tailWord_4589668).sum := by decide
  have hdescent : baseEnd_4589668 < baseStart_4589668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589682 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_4589682 : Nat := 118140960795 + 4589682 * 2 ^ 59
def prefixEnd_4589682 : Nat := 4983230072969 + 3 ^ 40 * 4589682 * 2
def baseEnd_4589682 : Nat := 2356712917289017081767443

theorem tailTrace_4589682 : CollatzResearch.WordTrace tailWord_4589682 prefixEnd_4589682 2356712917289017081767443 := by
  unfold tailWord_4589682
  simp only [CollatzResearch.WordTrace]
  refine ⟨41849863739593361031200825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111599636638915629416535533 41849863739593361031200825)
  ·
    refine ⟨31387397804695020773400619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41849863739593361031200825 31387397804695020773400619)
    ·
      refine ⟨47081096707042531160100929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31387397804695020773400619 47081096707042531160100929)
      ·
        refine ⟨35310822530281898370075697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47081096707042531160100929 35310822530281898370075697)
        ·
          refine ⟨26483116897711423777556773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35310822530281898370075697 26483116897711423777556773)
          ·
            refine ⟨4965584418320891958291895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26483116897711423777556773 4965584418320891958291895)
            ·
              refine ⟨7448376627481337937437843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4965584418320891958291895 7448376627481337937437843)
              ·
                refine ⟨11172564941222006906156765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7448376627481337937437843 11172564941222006906156765)
                ·
                  refine ⟨4189711852958252589808787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11172564941222006906156765 4189711852958252589808787)
                  ·
                    refine ⟨6284567779437378884713181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4189711852958252589808787 6284567779437378884713181)
                    ·
                      refine ⟨2356712917289017081767443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6284567779437378884713181 2356712917289017081767443)
                      ·
                        rfl

theorem cell23_4589682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_4589682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589682 prefixEnd_4589682 := by exact prefixLift 4589682
  have htrace : WordTrace (prefixWord ++ tailWord_4589682) baseStart_4589682 baseEnd_4589682 := by
    simpa [prefixWord, tailWord_4589682, baseEnd_4589682] using wordTrace_append hprefix tailTrace_4589682
  have hstable : (prefixWord ++ tailWord_4589682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589682).length < 2 ^ (prefixWord ++ tailWord_4589682).sum := by decide
  have hdescent : baseEnd_4589682 < baseStart_4589682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589691 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 3]
def baseStart_4589691 : Nat := 118140960795 + 4589691 * 2 ^ 59
def prefixEnd_4589691 : Nat := 4983230072969 + 3 ^ 40 * 4589691 * 2
def baseEnd_4589691 : Nat := 2356717538614907546554901

theorem tailTrace_4589691 : CollatzResearch.WordTrace tailWord_4589691 prefixEnd_4589691 2356717538614907546554901 := by
  unfold tailWord_4589691
  simp only [CollatzResearch.WordTrace]
  refine ⟨167399783215340838661880927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111599855476893892441253951 167399783215340838661880927)
  ·
    refine ⟨251099674823011257992821391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167399783215340838661880927 251099674823011257992821391)
    ·
      refine ⟨376649512234516886989232087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251099674823011257992821391 376649512234516886989232087)
      ·
        refine ⟨564974268351775330483848131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376649512234516886989232087 564974268351775330483848131)
        ·
          refine ⟨847461402527662995725772197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564974268351775330483848131 847461402527662995725772197)
          ·
            refine ⟨158899012973936811698582287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 847461402527662995725772197 158899012973936811698582287)
            ·
              refine ⟨238348519460905217547873431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158899012973936811698582287 238348519460905217547873431)
              ·
                refine ⟨357522779191357826321810147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238348519460905217547873431 357522779191357826321810147)
                ·
                  refine ⟨536284168787036739482715221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357522779191357826321810147 536284168787036739482715221)
                  ·
                    refine ⟨6284580102973086790813069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 536284168787036739482715221 6284580102973086790813069)
                    ·
                      refine ⟨2356717538614907546554901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6284580102973086790813069 2356717538614907546554901)
                      ·
                        rfl

theorem cell23_4589691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 3].length) (baseStart_4589691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589691 prefixEnd_4589691 := by exact prefixLift 4589691
  have htrace : WordTrace (prefixWord ++ tailWord_4589691) baseStart_4589691 baseEnd_4589691 := by
    simpa [prefixWord, tailWord_4589691, baseEnd_4589691] using wordTrace_append hprefix tailTrace_4589691
  have hstable : (prefixWord ++ tailWord_4589691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589691).length < 2 ^ (prefixWord ++ tailWord_4589691).sum := by decide
  have hdescent : baseEnd_4589691 < baseStart_4589691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589705 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 5, 2, 2]
def baseStart_4589705 : Nat := 118140960795 + 4589705 * 2 ^ 59
def prefixEnd_4589705 : Nat := 4983230072969 + 3 ^ 40 * 4589705 * 2
def baseEnd_4589705 : Nat := 2356724727344070491779837

theorem tailTrace_4589705 : CollatzResearch.WordTrace tailWord_4589705 prefixEnd_4589705 2356724727344070491779837 := by
  unfold tailWord_4589705
  simp only [CollatzResearch.WordTrace]
  refine ⟨167400293837290119052890569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111600195891526746035260379 167400293837290119052890569)
  ·
    refine ⟨125550220377967589289667927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167400293837290119052890569 125550220377967589289667927)
    ·
      refine ⟨188325330566951383934501891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125550220377967589289667927 188325330566951383934501891)
      ·
        refine ⟨282487995850427075901752837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188325330566951383934501891 282487995850427075901752837)
        ·
          refine ⟨52966499221955076731578657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282487995850427075901752837 52966499221955076731578657)
          ·
            refine ⟨39724874416466307548683993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52966499221955076731578657 39724874416466307548683993)
            ·
              refine ⟨29793655812349730661512995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39724874416466307548683993 29793655812349730661512995)
              ·
                refine ⟨44690483718524595992269493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29793655812349730661512995 44690483718524595992269493)
                ·
                  refine ⟨4189732848611680874275265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44690483718524595992269493 4189732848611680874275265)
                  ·
                    refine ⟨3142299636458760655706449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4189732848611680874275265 3142299636458760655706449)
                    ·
                      refine ⟨2356724727344070491779837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142299636458760655706449 2356724727344070491779837)
                      ·
                        rfl

theorem cell23_4589705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 2, 2].length) (baseStart_4589705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589705 prefixEnd_4589705 := by exact prefixLift 4589705
  have htrace : WordTrace (prefixWord ++ tailWord_4589705) baseStart_4589705 baseEnd_4589705 := by
    simpa [prefixWord, tailWord_4589705, baseEnd_4589705] using wordTrace_append hprefix tailTrace_4589705
  have hstable : (prefixWord ++ tailWord_4589705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589705).length < 2 ^ (prefixWord ++ tailWord_4589705).sum := by decide
  have hdescent : baseEnd_4589705 < baseStart_4589705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589725 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_4589725 : Nat := 118140960795 + 4589725 * 2 ^ 59
def prefixEnd_4589725 : Nat := 4983230072969 + 3 ^ 40 * 4589725 * 2
def baseEnd_4589725 : Nat := 2356734996957160413529745

theorem tailTrace_4589725 : CollatzResearch.WordTrace tailWord_4589725 prefixEnd_4589725 2356734996957160413529745 := by
  unfold tailWord_4589725
  simp only [CollatzResearch.WordTrace]
  refine ⟨167401023297217662468618629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111600682198145108312412419 167401023297217662468618629)
  ·
    refine ⟨31387691868228311712865993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167401023297217662468618629 31387691868228311712865993)
    ·
      refine ⟨23540768901171233784649495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31387691868228311712865993 23540768901171233784649495)
      ·
        refine ⟨35311153351756850676974243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23540768901171233784649495 35311153351756850676974243)
        ·
          refine ⟨52966730027635276015461365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35311153351756850676974243 52966730027635276015461365)
          ·
            refine ⟨4965630940090807126449503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52966730027635276015461365 4965630940090807126449503)
            ·
              refine ⟨7448446410136210689674255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4965630940090807126449503 7448446410136210689674255)
              ·
                refine ⟨11172669615204316034511383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7448446410136210689674255 11172669615204316034511383)
                ·
                  refine ⟨16759004422806474051767075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11172669615204316034511383 16759004422806474051767075)
                  ·
                    refine ⟨25138506634209711077650613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16759004422806474051767075 25138506634209711077650613)
                    ·
                      refine ⟨2356734996957160413529745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25138506634209711077650613 2356734996957160413529745)
                      ·
                        rfl

theorem cell23_4589725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_4589725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589725 prefixEnd_4589725 := by exact prefixLift 4589725
  have htrace : WordTrace (prefixWord ++ tailWord_4589725) baseStart_4589725 baseEnd_4589725 := by
    simpa [prefixWord, tailWord_4589725, baseEnd_4589725] using wordTrace_append hprefix tailTrace_4589725
  have hstable : (prefixWord ++ tailWord_4589725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589725).length < 2 ^ (prefixWord ++ tailWord_4589725).sum := by decide
  have hdescent : baseEnd_4589725 < baseStart_4589725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589732 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_4589732 : Nat := 118140960795 + 4589732 * 2 ^ 59
def prefixEnd_4589732 : Nat := 4983230072969 + 3 ^ 40 * 4589732 * 2
def baseEnd_4589732 : Nat := 785579530440580628714071

theorem tailTrace_4589732 : CollatzResearch.WordTrace tailWord_4589732 prefixEnd_4589732 785579530440580628714071 := by
  unfold tailWord_4589732
  simp only [CollatzResearch.WordTrace]
  refine ⟨83700639304096151332061725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111600852405461535109415633 83700639304096151332061725)
  ·
    refine ⟨31387739739036056749523147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83700639304096151332061725 31387739739036056749523147)
    ·
      refine ⟨47081609608554085124284721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31387739739036056749523147 47081609608554085124284721)
      ·
        refine ⟨35311207206415563843213541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47081609608554085124284721 35311207206415563843213541)
        ·
          refine ⟨6620851351202918220602539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35311207206415563843213541 6620851351202918220602539)
          ·
            refine ⟨9931277026804377330903809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6620851351202918220602539 9931277026804377330903809)
            ·
              refine ⟨7448457770103282998177857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9931277026804377330903809 7448457770103282998177857)
              ·
                refine ⟨5586343327577462248633393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7448457770103282998177857 5586343327577462248633393)
                ·
                  refine ⟨4189757495683096686475045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5586343327577462248633393 4189757495683096686475045)
                  ·
                    refine ⟨785579530440580628714071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4189757495683096686475045 785579530440580628714071)
                    ·
                      rfl

theorem cell23_4589732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_4589732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589732 prefixEnd_4589732 := by exact prefixLift 4589732
  have htrace : WordTrace (prefixWord ++ tailWord_4589732) baseStart_4589732 baseEnd_4589732 := by
    simpa [prefixWord, tailWord_4589732, baseEnd_4589732] using wordTrace_append hprefix tailTrace_4589732
  have hstable : (prefixWord ++ tailWord_4589732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589732).length < 2 ^ (prefixWord ++ tailWord_4589732).sum := by decide
  have hdescent : baseEnd_4589732 < baseStart_4589732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589745 : List Nat := [1, 2, 2, 5, 2, 2, 1, 8]
def baseStart_4589745 : Nat := 118140960795 + 4589745 * 2 ^ 59
def prefixEnd_4589745 : Nat := 4983230072969 + 3 ^ 40 * 4589745 * 2
def baseEnd_4589745 : Nat := 87286861724824086491839

theorem tailTrace_4589745 : CollatzResearch.WordTrace tailWord_4589745 prefixEnd_4589745 87286861724824086491839 := by
  unfold tailWord_4589745
  simp only [CollatzResearch.WordTrace]
  refine ⟨167401752757145205884346689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111601168504763470589564459 167401752757145205884346689)
  ·
    refine ⟨125551314567858904413260017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167401752757145205884346689 125551314567858904413260017)
    ·
      refine ⟨94163485925894178309945013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125551314567858904413260017 94163485925894178309945013)
      ·
        refine ⟨8827826805552579216557345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94163485925894178309945013 8827826805552579216557345)
        ·
          refine ⟨6620870104164434412418009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8827826805552579216557345 6620870104164434412418009)
          ·
            refine ⟨4965652578123325809313507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6620870104164434412418009 4965652578123325809313507)
            ·
              refine ⟨7448478867184988713970261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4965652578123325809313507 7448478867184988713970261)
              ·
                refine ⟨87286861724824086491839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7448478867184988713970261 87286861724824086491839)
                ·
                  rfl

theorem cell23_4589745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 8].length) (baseStart_4589745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589745 prefixEnd_4589745 := by exact prefixLift 4589745
  have htrace : WordTrace (prefixWord ++ tailWord_4589745) baseStart_4589745 baseEnd_4589745 := by
    simpa [prefixWord, tailWord_4589745, baseEnd_4589745] using wordTrace_append hprefix tailTrace_4589745
  have hstable : (prefixWord ++ tailWord_4589745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589745).length < 2 ^ (prefixWord ++ tailWord_4589745).sum := by decide
  have hdescent : baseEnd_4589745 < baseStart_4589745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589755 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 3]
def baseStart_4589755 : Nat := 118140960795 + 4589755 * 2 ^ 59
def prefixEnd_4589755 : Nat := 4983230072969 + 3 ^ 40 * 4589755 * 2
def baseEnd_4589755 : Nat := 2356750401376795296154607

theorem tailTrace_4589755 : CollatzResearch.WordTrace tailWord_4589755 prefixEnd_4589755 2356750401376795296154607 := by
  unfold tailWord_4589755
  simp only [CollatzResearch.WordTrace]
  refine ⟨167402117487108977592210719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111601411658072651728140479 167402117487108977592210719)
  ·
    refine ⟨251103176230663466388316079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167402117487108977592210719 251103176230663466388316079)
    ·
      refine ⟨376654764345995199582474119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251103176230663466388316079 376654764345995199582474119)
      ·
        refine ⟨564982146518992799373711179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376654764345995199582474119 564982146518992799373711179)
        ·
          refine ⟨847473219778489199060566769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564982146518992799373711179 847473219778489199060566769)
          ·
            refine ⟨635604914833866899295425077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847473219778489199060566769 635604914833866899295425077)
            ·
              refine ⟨59587960765675021808946101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 635604914833866899295425077 59587960765675021808946101)
              ·
                refine ⟨5586371321782033294588697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59587960765675021808946101 5586371321782033294588697)
                ·
                  refine ⟨4189778491336524970941523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5586371321782033294588697 4189778491336524970941523)
                  ·
                    refine ⟨6284667737004787456412285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4189778491336524970941523 6284667737004787456412285)
                    ·
                      refine ⟨2356750401376795296154607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6284667737004787456412285 2356750401376795296154607)
                      ·
                        rfl

theorem cell23_4589755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 3].length) (baseStart_4589755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589755 prefixEnd_4589755 := by exact prefixLift 4589755
  have htrace : WordTrace (prefixWord ++ tailWord_4589755) baseStart_4589755 baseEnd_4589755 := by
    simpa [prefixWord, tailWord_4589755, baseEnd_4589755] using wordTrace_append hprefix tailTrace_4589755
  have hstable : (prefixWord ++ tailWord_4589755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589755).length < 2 ^ (prefixWord ++ tailWord_4589755).sum := by decide
  have hdescent : baseEnd_4589755 < baseStart_4589755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589765 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 3, 3, 2]
def baseStart_4589765 : Nat := 118140960795 + 4589765 * 2 ^ 59
def prefixEnd_4589765 : Nat := 4983230072969 + 3 ^ 40 * 4589765 * 2
def baseEnd_4589765 : Nat := 2356755536183340257029561

theorem tailTrace_4589765 : CollatzResearch.WordTrace tailWord_4589765 prefixEnd_4589765 2356755536183340257029561 := by
  unfold tailWord_4589765
  simp only [CollatzResearch.WordTrace]
  refine ⟨167402482217072749300074749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111601654811381832866716499 167402482217072749300074749)
  ·
    refine ⟨62775930831402280987528031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167402482217072749300074749 62775930831402280987528031)
    ·
      refine ⟨94163896247103421481292047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62775930831402280987528031 94163896247103421481292047)
      ·
        refine ⟨141245844370655132221938071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94163896247103421481292047 141245844370655132221938071)
        ·
          refine ⟨211868766555982698332907107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141245844370655132221938071 211868766555982698332907107)
          ·
            refine ⟨317803149833974047499360661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211868766555982698332907107 317803149833974047499360661)
            ·
              refine ⟨14897022648467533476532531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 317803149833974047499360661 14897022648467533476532531)
              ·
                refine ⟨22345533972701300214798797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14897022648467533476532531 22345533972701300214798797)
                ·
                  refine ⟨8379575239762987580549549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22345533972701300214798797 8379575239762987580549549)
                  ·
                    refine ⟨3142340714911120342706081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8379575239762987580549549 3142340714911120342706081)
                    ·
                      refine ⟨2356755536183340257029561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3142340714911120342706081 2356755536183340257029561)
                      ·
                        rfl

theorem cell23_4589765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_4589765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589765 prefixEnd_4589765 := by exact prefixLift 4589765
  have htrace : WordTrace (prefixWord ++ tailWord_4589765) baseStart_4589765 baseEnd_4589765 := by
    simpa [prefixWord, tailWord_4589765, baseEnd_4589765] using wordTrace_append hprefix tailTrace_4589765
  have hstable : (prefixWord ++ tailWord_4589765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589765).length < 2 ^ (prefixWord ++ tailWord_4589765).sum := by decide
  have hdescent : baseEnd_4589765 < baseStart_4589765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589771 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 1, 8]
def baseStart_4589771 : Nat := 118140960795 + 4589771 * 2 ^ 59
def prefixEnd_4589771 : Nat := 4983230072969 + 3 ^ 40 * 4589771 * 2
def baseEnd_4589771 : Nat := 785586205689089077851511

theorem tailTrace_4589771 : CollatzResearch.WordTrace tailWord_4589771 prefixEnd_4589771 785586205689089077851511 := by
  unfold tailWord_4589771
  simp only [CollatzResearch.WordTrace]
  refine ⟨167402701055051012324793167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111601800703367341549862111 167402701055051012324793167)
  ·
    refine ⟨251104051582576518487189751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167402701055051012324793167 251104051582576518487189751)
    ·
      refine ⟨376656077373864777730784627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251104051582576518487189751 376656077373864777730784627)
      ·
        refine ⟨564984116060797166596176941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376656077373864777730784627 564984116060797166596176941)
        ·
          refine ⟨211869043522798937473566353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 564984116060797166596176941 211869043522798937473566353)
          ·
            refine ⟨158901782642099203105174765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211869043522798937473566353 158901782642099203105174765)
            ·
              refine ⟨59588168490787201164440537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158901782642099203105174765 59588168490787201164440537)
              ·
                refine ⟨44691126368090400873330403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59588168490787201164440537 44691126368090400873330403)
                ·
                  refine ⟨67036689552135601309995605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44691126368090400873330403 67036689552135601309995605)
                  ·
                    refine ⟨785586205689089077851511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67036689552135601309995605 785586205689089077851511)
                    ·
                      rfl

theorem cell23_4589771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 8].length) (baseStart_4589771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589771 prefixEnd_4589771 := by exact prefixLift 4589771
  have htrace : WordTrace (prefixWord ++ tailWord_4589771) baseStart_4589771 baseEnd_4589771 := by
    simpa [prefixWord, tailWord_4589771, baseEnd_4589771] using wordTrace_append hprefix tailTrace_4589771
  have hstable : (prefixWord ++ tailWord_4589771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589771).length < 2 ^ (prefixWord ++ tailWord_4589771).sum := by decide
  have hdescent : baseEnd_4589771 < baseStart_4589771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589789 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4589789 : Nat := 118140960795 + 4589789 * 2 ^ 59
def prefixEnd_4589789 : Nat := 4983230072969 + 3 ^ 40 * 4589789 * 2
def baseEnd_4589789 : Nat := 2356767859719048163129451

theorem tailTrace_4589789 : CollatzResearch.WordTrace tailWord_4589789 prefixEnd_4589789 2356767859719048163129451 := by
  unfold tailWord_4589789
  simp only [CollatzResearch.WordTrace]
  refine ⟨167403357568985801398948421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111602238379323867599298947 167403357568985801398948421)
  ·
    refine ⟨31388129544184837762302829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167403357568985801398948421 31388129544184837762302829)
    ·
      refine ⟨11770548579069314160863561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31388129544184837762302829 11770548579069314160863561)
      ·
        refine ⟨8827911434301985620647671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11770548579069314160863561 8827911434301985620647671)
        ·
          refine ⟨13241867151452978430971507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8827911434301985620647671 13241867151452978430971507)
          ·
            refine ⟨19862800727179467646457261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13241867151452978430971507 19862800727179467646457261)
            ·
              refine ⟨7448550272692300367421473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19862800727179467646457261 7448550272692300367421473)
              ·
                refine ⟨5586412704519225275566105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7448550272692300367421473 5586412704519225275566105)
                ·
                  refine ⟨4189809528389418956674579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5586412704519225275566105 4189809528389418956674579)
                  ·
                    refine ⟨6284714292584128435011869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4189809528389418956674579 6284714292584128435011869)
                    ·
                      refine ⟨2356767859719048163129451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6284714292584128435011869 2356767859719048163129451)
                      ·
                        rfl

theorem cell23_4589789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4589789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589789 prefixEnd_4589789 := by exact prefixLift 4589789
  have htrace : WordTrace (prefixWord ++ tailWord_4589789) baseStart_4589789 baseEnd_4589789 := by
    simpa [prefixWord, tailWord_4589789, baseEnd_4589789] using wordTrace_append hprefix tailTrace_4589789
  have hstable : (prefixWord ++ tailWord_4589789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589789).length < 2 ^ (prefixWord ++ tailWord_4589789).sum := by decide
  have hdescent : baseEnd_4589789 < baseStart_4589789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589801 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 11]
def baseStart_4589801 : Nat := 118140960795 + 4589801 * 2 ^ 59
def prefixEnd_4589801 : Nat := 4983230072969 + 3 ^ 40 * 4589801 * 2
def baseEnd_4589801 : Nat := 261863780165211346242155

theorem tailTrace_4589801 : CollatzResearch.WordTrace tailWord_4589801 prefixEnd_4589801 261863780165211346242155 := by
  unfold tailWord_4589801
  simp only [CollatzResearch.WordTrace]
  refine ⟨167403795244942327448385257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111602530163294884965590171 167403795244942327448385257)
  ·
    refine ⟨125552846433706745586288943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167403795244942327448385257 125552846433706745586288943)
    ·
      refine ⟨188329269650560118379433415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125552846433706745586288943 188329269650560118379433415)
      ·
        refine ⟨282493904475840177569150123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188329269650560118379433415 282493904475840177569150123)
        ·
          refine ⟨423740856713760266353725185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282493904475840177569150123 423740856713760266353725185)
          ·
            refine ⟨317805642535320199765293889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423740856713760266353725185 317805642535320199765293889)
            ·
              refine ⟨238354231901490149823970417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317805642535320199765293889 238354231901490149823970417)
              ·
                refine ⟨178765673926117612367977813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238354231901490149823970417 178765673926117612367977813)
                ·
                  refine ⟨261863780165211346242155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 178765673926117612367977813 261863780165211346242155)
                  ·
                    rfl

theorem cell23_4589801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 11].length) (baseStart_4589801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589801 prefixEnd_4589801 := by exact prefixLift 4589801
  have htrace : WordTrace (prefixWord ++ tailWord_4589801) baseStart_4589801 baseEnd_4589801 := by
    simpa [prefixWord, tailWord_4589801, baseEnd_4589801] using wordTrace_append hprefix tailTrace_4589801
  have hstable : (prefixWord ++ tailWord_4589801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589801).length < 2 ^ (prefixWord ++ tailWord_4589801).sum := by decide
  have hdescent : baseEnd_4589801 < baseStart_4589801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4589818 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 7]
def baseStart_4589818 : Nat := 118140960795 + 4589818 * 2 ^ 59
def prefixEnd_4589818 : Nat := 4983230072969 + 3 ^ 40 * 4589818 * 2
def baseEnd_4589818 : Nat := 261864750073114283296313

theorem tailTrace_4589818 : CollatzResearch.WordTrace tailWord_4589818 prefixEnd_4589818 261864750073114283296313 := by
  unfold tailWord_4589818
  simp only [CollatzResearch.WordTrace]
  refine ⟨41851103821470184837938527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111602943523920492901169405 41851103821470184837938527)
  ·
    refine ⟨62776655732205277256907791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41851103821470184837938527 62776655732205277256907791)
    ·
      refine ⟨94164983598307915885361687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62776655732205277256907791 94164983598307915885361687)
      ·
        refine ⟨141247475397461873828042531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94164983598307915885361687 141247475397461873828042531)
        ·
          refine ⟨211871213096192810742063797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141247475397461873828042531 211871213096192810742063797)
          ·
            refine ⟨19862926227768076007068481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211871213096192810742063797 19862926227768076007068481)
            ·
              refine ⟨14897194670826057005301361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19862926227768076007068481 14897194670826057005301361)
              ·
                refine ⟨11172896003119542753976021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14897194670826057005301361 11172896003119542753976021)
                ·
                  refine ⟨261864750073114283296313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11172896003119542753976021 261864750073114283296313)
                  ·
                    rfl

theorem cell23_4589818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_4589818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4589818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4589818 prefixEnd_4589818 := by exact prefixLift 4589818
  have htrace : WordTrace (prefixWord ++ tailWord_4589818) baseStart_4589818 baseEnd_4589818 := by
    simpa [prefixWord, tailWord_4589818, baseEnd_4589818] using wordTrace_append hprefix tailTrace_4589818
  have hstable : (prefixWord ++ tailWord_4589818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4589818).length < 2 ^ (prefixWord ++ tailWord_4589818).sum := by decide
  have hdescent : baseEnd_4589818 < baseStart_4589818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4589818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
