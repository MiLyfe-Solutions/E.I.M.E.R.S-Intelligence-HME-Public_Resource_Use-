import V185TrunkScan20Chunk037

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_231978 : List Nat := [3, 1, 4, 1, 1, 2, 8]
def baseStart_231978 : Nat := 118140960795 + 231978 * 2 ^ 59
def prefixEnd_231978 : Nat := 4983230072969 + 3 ^ 40 * 231978 * 2
def baseEnd_231978 : Nat := 11764564470992456168707

theorem tailTrace_231978 : CollatzResearch.WordTrace tailWord_231978 prefixEnd_231978 11764564470992456168707 := by
  unfold tailWord_231978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115233188397699883326147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5640621835727199688869725 2115233188397699883326147)
  ·
    refine ⟨3172849782596549824989221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2115233188397699883326147 3172849782596549824989221)
    ·
      refine ⟨594909334236853092185479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3172849782596549824989221 594909334236853092185479)
      ·
        refine ⟨892364001355279638278219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594909334236853092185479 892364001355279638278219)
        ·
          refine ⟨1338546002032919457417329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892364001355279638278219 1338546002032919457417329)
          ·
            refine ⟨1003909501524689593062997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338546002032919457417329 1003909501524689593062997)
            ·
              refine ⟨11764564470992456168707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1003909501524689593062997 11764564470992456168707)
              ·
                rfl

theorem cell20_231978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 8].length) (baseStart_231978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231978 prefixEnd_231978 := by exact prefixLift 231978
  have htrace : WordTrace (prefixWord ++ tailWord_231978) baseStart_231978 baseEnd_231978 := by
    simpa [prefixWord, tailWord_231978, baseEnd_231978] using wordTrace_append hprefix tailTrace_231978
  have hstable : (prefixWord ++ tailWord_231978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231978).length < 2 ^ (prefixWord ++ tailWord_231978).sum := by decide
  have hdescent : baseEnd_231978 < baseStart_231978 := by decide
  rcases family_descends (prefixWord ++ tailWord_231978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231985 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_231985 : Nat := 118140960795 + 231985 * 2 ^ 59
def prefixEnd_231985 : Nat := 4983230072969 + 3 ^ 40 * 231985 * 2
def baseEnd_231985 : Nat := 105884275229671192285001

theorem tailTrace_231985 : CollatzResearch.WordTrace tailWord_231985 prefixEnd_231985 105884275229671192285001 := by
  unfold tailWord_231985
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461188064565439728809409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5640792043043626485872939 8461188064565439728809409)
  ·
    refine ⟨6345891048424079796607057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8461188064565439728809409 6345891048424079796607057)
    ·
      refine ⟨4759418286318059847455293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6345891048424079796607057 4759418286318059847455293)
      ·
        refine ⟨1784781857369272442795735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4759418286318059847455293 1784781857369272442795735)
        ·
          refine ⟨2677172786053908664193603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784781857369272442795735 2677172786053908664193603)
          ·
            refine ⟨4015759179080862996290405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677172786053908664193603 4015759179080862996290405)
            ·
              refine ⟨752954846077661811804451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4015759179080862996290405 752954846077661811804451)
              ·
                refine ⟨1129432269116492717706677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752954846077661811804451 1129432269116492717706677)
                ·
                  refine ⟨105884275229671192285001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1129432269116492717706677 105884275229671192285001)
                  ·
                    rfl

theorem cell20_231985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_231985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231985 prefixEnd_231985 := by exact prefixLift 231985
  have htrace : WordTrace (prefixWord ++ tailWord_231985) baseStart_231985 baseEnd_231985 := by
    simpa [prefixWord, tailWord_231985, baseEnd_231985] using wordTrace_append hprefix tailTrace_231985
  have hstable : (prefixWord ++ tailWord_231985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231985).length < 2 ^ (prefixWord ++ tailWord_231985).sum := by decide
  have hdescent : baseEnd_231985 < baseStart_231985 := by decide
  rcases family_descends (prefixWord ++ tailWord_231985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231998 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_231998 : Nat := 118140960795 + 231998 * 2 ^ 59
def prefixEnd_231998 : Nat := 4983230072969 + 3 ^ 40 * 231998 * 2
def baseEnd_231998 : Nat := 105890208783900924851615

theorem tailTrace_231998 : CollatzResearch.WordTrace tailWord_231998 prefixEnd_231998 105890208783900924851615 := by
  unfold tailWord_231998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057707776689792868629081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5641108142345561966021765 1057707776689792868629081)
  ·
    refine ⟨793280832517344651471811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1057707776689792868629081 793280832517344651471811)
    ·
      refine ⟨1189921248776016977207717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793280832517344651471811 1189921248776016977207717)
      ·
        refine ⟨223110234145503183226447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1189921248776016977207717 223110234145503183226447)
        ·
          refine ⟨334665351218254774839671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223110234145503183226447 334665351218254774839671)
          ·
            refine ⟨501998026827382162259507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334665351218254774839671 501998026827382162259507)
            ·
              refine ⟨752997040241073243389261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501998026827382162259507 752997040241073243389261)
              ·
                refine ⟨282373890090402466270973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 752997040241073243389261 282373890090402466270973)
                ·
                  refine ⟨105890208783900924851615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282373890090402466270973 105890208783900924851615)
                  ·
                    rfl

theorem cell20_231998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_231998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_231998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_231998 prefixEnd_231998 := by exact prefixLift 231998
  have htrace : WordTrace (prefixWord ++ tailWord_231998) baseStart_231998 baseEnd_231998 := by
    simpa [prefixWord, tailWord_231998, baseEnd_231998] using wordTrace_append hprefix tailTrace_231998
  have hstable : (prefixWord ++ tailWord_231998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231998).length < 2 ^ (prefixWord ++ tailWord_231998).sum := by decide
  have hdescent : baseEnd_231998 < baseStart_231998 := by decide
  rcases family_descends (prefixWord ++ tailWord_231998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232037 : List Nat := [1, 3, 1, 3, 12]
def baseStart_232037 : Nat := 118140960795 + 232037 * 2 ^ 59
def prefixEnd_232037 : Nat := 4983230072969 + 3 ^ 40 * 232037 * 2
def baseEnd_232037 : Nat := 1307506289464075587055

theorem tailTrace_232037 : CollatzResearch.WordTrace tailWord_232037 prefixEnd_232037 1307506289464075587055 := by
  unfold tailWord_232037
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463084660377052609702365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5642056440251368406468243 8463084660377052609702365)
  ·
    refine ⟨3173656747641394728638387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8463084660377052609702365 3173656747641394728638387)
    ·
      refine ⟨4760485121462092092957581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3173656747641394728638387 4760485121462092092957581)
      ·
        refine ⟨1785181920548284534859093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4760485121462092092957581 1785181920548284534859093)
        ·
          refine ⟨1307506289464075587055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1785181920548284534859093 1307506289464075587055)
          ·
            rfl

theorem cell20_232037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 12].length) (baseStart_232037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232037 prefixEnd_232037 := by exact prefixLift 232037
  have htrace : WordTrace (prefixWord ++ tailWord_232037) baseStart_232037 baseEnd_232037 := by
    simpa [prefixWord, tailWord_232037, baseEnd_232037] using wordTrace_append hprefix tailTrace_232037
  have hstable : (prefixWord ++ tailWord_232037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232037).length < 2 ^ (prefixWord ++ tailWord_232037).sum := by decide
  have hdescent : baseEnd_232037 < baseStart_232037 := by decide
  rcases family_descends (prefixWord ++ tailWord_232037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232050 : List Nat := [3, 2, 1, 2, 5, 1, 1, 5]
def baseStart_232050 : Nat := 118140960795 + 232050 * 2 ^ 59
def prefixEnd_232050 : Nat := 4983230072969 + 3 ^ 40 * 232050 * 2
def baseEnd_232050 : Nat := 35304647666939951706023

theorem tailTrace_232050 : CollatzResearch.WordTrace tailWord_232050 prefixEnd_232050 35304647666939951706023 := by
  unfold tailWord_232050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115889702332488957481401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5642372539553303886617069 2115889702332488957481401)
  ·
    refine ⟨1586917276749366718111051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2115889702332488957481401 1586917276749366718111051)
    ·
      refine ⟨2380375915124050077166577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586917276749366718111051 2380375915124050077166577)
      ·
        refine ⟨1785281936343037557874933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2380375915124050077166577 1785281936343037557874933)
        ·
          refine ⟨167370181532159771050775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1785281936343037557874933 167370181532159771050775)
          ·
            refine ⟨251055272298239656576163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167370181532159771050775 251055272298239656576163)
            ·
              refine ⟨376582908447359484864245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251055272298239656576163 376582908447359484864245)
              ·
                refine ⟨35304647666939951706023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376582908447359484864245 35304647666939951706023)
                ·
                  rfl

theorem cell20_232050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_232050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232050 prefixEnd_232050 := by exact prefixLift 232050
  have htrace : WordTrace (prefixWord ++ tailWord_232050) baseStart_232050 baseEnd_232050 := by
    simpa [prefixWord, tailWord_232050, baseEnd_232050] using wordTrace_append hprefix tailTrace_232050
  have hstable : (prefixWord ++ tailWord_232050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232050).length < 2 ^ (prefixWord ++ tailWord_232050).sum := by decide
  have hdescent : baseEnd_232050 < baseStart_232050 := by decide
  rcases family_descends (prefixWord ++ tailWord_232050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232092 : List Nat := [2, 2, 3, 2, 2, 2, 7]
def baseStart_232092 : Nat := 118140960795 + 232092 * 2 ^ 59
def prefixEnd_232092 : Nat := 4983230072969 + 3 ^ 40 * 232092 * 2
def baseEnd_232092 : Nat := 11770345882806041746433

theorem tailTrace_232092 : CollatzResearch.WordTrace tailWord_232092 prefixEnd_232092 11770345882806041746433 := by
  unfold tailWord_232092
  simp only [CollatzResearch.WordTrace]
  refine ⟨4232545337588898501477265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5643393783451864668636353 4232545337588898501477265)
  ·
    refine ⟨3174409003191673876107949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4232545337588898501477265 3174409003191673876107949)
    ·
      refine ⟨1190403376196877703540481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3174409003191673876107949 1190403376196877703540481)
      ·
        refine ⟨892802532147658277655361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190403376196877703540481 892802532147658277655361)
        ·
          refine ⟨669601899110743708241521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892802532147658277655361 669601899110743708241521)
          ·
            refine ⟨502201424333057781181141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669601899110743708241521 502201424333057781181141)
            ·
              refine ⟨11770345882806041746433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 502201424333057781181141 11770345882806041746433)
              ·
                rfl

theorem cell20_232092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 7].length) (baseStart_232092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232092 prefixEnd_232092 := by exact prefixLift 232092
  have htrace : WordTrace (prefixWord ++ tailWord_232092) baseStart_232092 baseEnd_232092 := by
    simpa [prefixWord, tailWord_232092, baseEnd_232092] using wordTrace_append hprefix tailTrace_232092
  have hstable : (prefixWord ++ tailWord_232092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232092).length < 2 ^ (prefixWord ++ tailWord_232092).sum := by decide
  have hdescent : baseEnd_232092 < baseStart_232092 := by decide
  rcases family_descends (prefixWord ++ tailWord_232092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232099 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 3]
def baseStart_232099 : Nat := 118140960795 + 232099 * 2 ^ 59
def prefixEnd_232099 : Nat := 4983230072969 + 3 ^ 40 * 232099 * 2
def baseEnd_232099 : Nat := 105936307935993462484535

theorem tailTrace_232099 : CollatzResearch.WordTrace tailWord_232099 prefixEnd_232099 105936307935993462484535 := by
  unfold tailWord_232099
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465345986152437198459351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5643563990768291465639567 8465345986152437198459351)
  ·
    refine ⟨12698018979228655797689027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8465345986152437198459351 12698018979228655797689027)
    ·
      refine ⟨19047028468842983696533541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12698018979228655797689027 19047028468842983696533541)
      ·
        refine ⟨3571317837908059443100039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19047028468842983696533541 3571317837908059443100039)
        ·
          refine ⟨5356976756862089164650059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571317837908059443100039 5356976756862089164650059)
          ·
            refine ⟨8035465135293133746975089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356976756862089164650059 8035465135293133746975089)
            ·
              refine ⟨6026598851469850310231317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8035465135293133746975089 6026598851469850310231317)
              ·
                refine ⟨282496821162649233292093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6026598851469850310231317 282496821162649233292093)
                ·
                  refine ⟨105936307935993462484535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282496821162649233292093 105936307935993462484535)
                  ·
                    rfl

theorem cell20_232099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_232099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232099 prefixEnd_232099 := by exact prefixLift 232099
  have htrace : WordTrace (prefixWord ++ tailWord_232099) baseStart_232099 baseEnd_232099 := by
    simpa [prefixWord, tailWord_232099, baseEnd_232099] using wordTrace_append hprefix tailTrace_232099
  have hstable : (prefixWord ++ tailWord_232099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232099).length < 2 ^ (prefixWord ++ tailWord_232099).sum := by decide
  have hdescent : baseEnd_232099 < baseStart_232099 := by decide
  rcases family_descends (prefixWord ++ tailWord_232099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232151 : List Nat := [1, 1, 3, 2, 1, 4, 8]
def baseStart_232151 : Nat := 118140960795 + 232151 * 2 ^ 59
def prefixEnd_232151 : Nat := 4983230072969 + 3 ^ 40 * 232151 * 2
def baseEnd_232151 : Nat := 11773338016990265861221

theorem tailTrace_232151 : CollatzResearch.WordTrace tailWord_232151 prefixEnd_232151 11773338016990265861221 := by
  unfold tailWord_232151
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467242581964050079352307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5644828387976033386234871 8467242581964050079352307)
  ·
    refine ⟨12700863872946075119028461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8467242581964050079352307 12700863872946075119028461)
    ·
      refine ⟨4762823952354778169635673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12700863872946075119028461 4762823952354778169635673)
      ·
        refine ⟨3572117964266083627226755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4762823952354778169635673 3572117964266083627226755)
        ·
          refine ⟨5358176946399125440840133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572117964266083627226755 5358176946399125440840133)
          ·
            refine ⟨1004658177449836020157525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5358176946399125440840133 1004658177449836020157525)
            ·
              refine ⟨11773338016990265861221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1004658177449836020157525 11773338016990265861221)
              ·
                rfl

theorem cell20_232151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 8].length) (baseStart_232151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232151 prefixEnd_232151 := by exact prefixLift 232151
  have htrace : WordTrace (prefixWord ++ tailWord_232151) baseStart_232151 baseEnd_232151 := by
    simpa [prefixWord, tailWord_232151, baseEnd_232151] using wordTrace_append hprefix tailTrace_232151
  have hstable : (prefixWord ++ tailWord_232151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232151).length < 2 ^ (prefixWord ++ tailWord_232151).sum := by decide
  have hdescent : baseEnd_232151 < baseStart_232151 := by decide
  rcases family_descends (prefixWord ++ tailWord_232151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232161 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_232161 : Nat := 118140960795 + 232161 * 2 ^ 59
def prefixEnd_232161 : Nat := 4983230072969 + 3 ^ 40 * 232161 * 2
def baseEnd_232161 : Nat := 105964606425396802417615

theorem tailTrace_232161 : CollatzResearch.WordTrace tailWord_232161 prefixEnd_232161 105964606425396802417615 := by
  unfold tailWord_232161
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467607311927821787216337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5645071541285214524810891 8467607311927821787216337)
  ·
    refine ⟨6350705483945866340412253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8467607311927821787216337 6350705483945866340412253)
    ·
      refine ⟨2381514556479699877654595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6350705483945866340412253 2381514556479699877654595)
      ·
        refine ⟨3572271834719549816481893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381514556479699877654595 3572271834719549816481893)
        ·
          refine ⟨669800969009915590590355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3572271834719549816481893 669800969009915590590355)
          ·
            refine ⟨1004701453514873385885533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669800969009915590590355 1004701453514873385885533)
            ·
              refine ⟨376763045068077519707075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1004701453514873385885533 376763045068077519707075)
              ·
                refine ⟨565144567602116279560613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376763045068077519707075 565144567602116279560613)
                ·
                  refine ⟨105964606425396802417615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565144567602116279560613 105964606425396802417615)
                  ·
                    rfl

theorem cell20_232161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_232161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232161 prefixEnd_232161 := by exact prefixLift 232161
  have htrace : WordTrace (prefixWord ++ tailWord_232161) baseStart_232161 baseEnd_232161 := by
    simpa [prefixWord, tailWord_232161, baseEnd_232161] using wordTrace_append hprefix tailTrace_232161
  have hstable : (prefixWord ++ tailWord_232161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232161).length < 2 ^ (prefixWord ++ tailWord_232161).sum := by decide
  have hdescent : baseEnd_232161 < baseStart_232161 := by decide
  rcases family_descends (prefixWord ++ tailWord_232161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232189 : List Nat := [1, 4, 1, 1, 1, 1, 3, 8]
def baseStart_232189 : Nat := 118140960795 + 232189 * 2 ^ 59
def prefixEnd_232189 : Nat := 4983230072969 + 3 ^ 40 * 232189 * 2
def baseEnd_232189 : Nat := 35325795462784383161389

theorem tailTrace_232189 : CollatzResearch.WordTrace tailWord_232189 prefixEnd_232189 35325795462784383161389 := by
  unfold tailWord_232189
  simp only [CollatzResearch.WordTrace]
  refine ⟨8468628555826382569235621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5645752370550921712823747 8468628555826382569235621)
  ·
    refine ⟨1587867854217446731731679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8468628555826382569235621 1587867854217446731731679)
    ·
      refine ⟨2381801781326170097597519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1587867854217446731731679 2381801781326170097597519)
      ·
        refine ⟨3572702671989255146396279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381801781326170097597519 3572702671989255146396279)
        ·
          refine ⟨5359054007983882719594419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572702671989255146396279 5359054007983882719594419)
          ·
            refine ⟨8038581011975824079391629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359054007983882719594419 8038581011975824079391629)
            ·
              refine ⟨3014467879490934029771861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8038581011975824079391629 3014467879490934029771861)
              ·
                refine ⟨35325795462784383161389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3014467879490934029771861 35325795462784383161389)
                ·
                  rfl

theorem cell20_232189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_232189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232189 prefixEnd_232189 := by exact prefixLift 232189
  have htrace : WordTrace (prefixWord ++ tailWord_232189) baseStart_232189 baseEnd_232189 := by
    simpa [prefixWord, tailWord_232189, baseEnd_232189] using wordTrace_append hprefix tailTrace_232189
  have hstable : (prefixWord ++ tailWord_232189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232189).length < 2 ^ (prefixWord ++ tailWord_232189).sum := by decide
  have hdescent : baseEnd_232189 < baseStart_232189 := by decide
  rcases family_descends (prefixWord ++ tailWord_232189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232265 : List Nat := [1, 2, 1, 1, 2, 6, 7]
def baseStart_232265 : Nat := 118140960795 + 232265 * 2 ^ 59
def prefixEnd_232265 : Nat := 4983230072969 + 3 ^ 40 * 232265 * 2
def baseEnd_232265 : Nat := 11779119428803851438947

theorem tailTrace_232265 : CollatzResearch.WordTrace tailWord_232265 prefixEnd_232265 11779119428803851438947 := by
  unfold tailWord_232265
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471400503551047549002249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5647600335700698366001499 8471400503551047549002249)
  ·
    refine ⟨6353550377663285661751687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8471400503551047549002249 6353550377663285661751687)
    ·
      refine ⟨9530325566494928492627531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353550377663285661751687 9530325566494928492627531)
      ·
        refine ⟨14295488349742392738941297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9530325566494928492627531 14295488349742392738941297)
        ·
          refine ⟨10721616262306794554205973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14295488349742392738941297 10721616262306794554205973)
          ·
            refine ⟨502575762295630994728405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10721616262306794554205973 502575762295630994728405)
            ·
              refine ⟨11779119428803851438947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 502575762295630994728405 11779119428803851438947)
              ·
                rfl

theorem cell20_232265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 7].length) (baseStart_232265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232265 prefixEnd_232265 := by exact prefixLift 232265
  have htrace : WordTrace (prefixWord ++ tailWord_232265) baseStart_232265 baseEnd_232265 := by
    simpa [prefixWord, tailWord_232265, baseEnd_232265] using wordTrace_append hprefix tailTrace_232265
  have hstable : (prefixWord ++ tailWord_232265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232265).length < 2 ^ (prefixWord ++ tailWord_232265).sum := by decide
  have hdescent : baseEnd_232265 < baseStart_232265 := by decide
  rcases family_descends (prefixWord ++ tailWord_232265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232268 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_232268 : Nat := 118140960795 + 232268 * 2 ^ 59
def prefixEnd_232268 : Nat := 4983230072969 + 3 ^ 40 * 232268 * 2
def baseEnd_232268 : Nat := 106013444140979985850511

theorem tailTrace_232268 : CollatzResearch.WordTrace tailWord_232268 prefixEnd_232268 106013444140979985850511 := by
  unfold tailWord_232268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4235754961270089530680729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5647673281693452707574305 4235754961270089530680729)
  ·
    refine ⟨3176816220952567148010547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4235754961270089530680729 3176816220952567148010547)
    ·
      refine ⟨4765224331428850722015821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3176816220952567148010547 4765224331428850722015821)
      ·
        refine ⟨1786959124285819020755933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4765224331428850722015821 1786959124285819020755933)
        ·
          refine ⟨670109671607182132783475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1786959124285819020755933 670109671607182132783475)
          ·
            refine ⟨1005164507410773199175213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670109671607182132783475 1005164507410773199175213)
            ·
              refine ⟨376936690279039949690705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1005164507410773199175213 376936690279039949690705)
              ·
                refine ⟨282702517709279962268029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376936690279039949690705 282702517709279962268029)
                ·
                  refine ⟨106013444140979985850511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282702517709279962268029 106013444140979985850511)
                  ·
                    rfl

theorem cell20_232268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_232268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232268 prefixEnd_232268 := by exact prefixLift 232268
  have htrace : WordTrace (prefixWord ++ tailWord_232268) baseStart_232268 baseEnd_232268 := by
    simpa [prefixWord, tailWord_232268, baseEnd_232268] using wordTrace_append hprefix tailTrace_232268
  have hstable : (prefixWord ++ tailWord_232268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232268).length < 2 ^ (prefixWord ++ tailWord_232268).sum := by decide
  have hdescent : baseEnd_232268 < baseStart_232268 := by decide
  rcases family_descends (prefixWord ++ tailWord_232268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232309 : List Nat := [1, 3, 4, 1, 1, 4, 1, 3, 2]
def baseStart_232309 : Nat := 118140960795 + 232309 * 2 ^ 59
def prefixEnd_232309 : Nat := 4983230072969 + 3 ^ 40 * 232309 * 2
def baseEnd_232309 : Nat := 106032157658166065483677

theorem tailTrace_232309 : CollatzResearch.WordTrace tailWord_232309 prefixEnd_232309 106032157658166065483677 := by
  unfold tailWord_232309
  simp only [CollatzResearch.WordTrace]
  refine ⟨8473005315391643063603981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5648670210261095375735987 8473005315391643063603981)
  ·
    refine ⟨3177376993271866148851493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8473005315391643063603981 3177376993271866148851493)
    ·
      refine ⟨595758186238474902909655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3177376993271866148851493 595758186238474902909655)
      ·
        refine ⟨893637279357712354364483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595758186238474902909655 893637279357712354364483)
        ·
          refine ⟨1340455919036568531546725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893637279357712354364483 1340455919036568531546725)
          ·
            refine ⟨251335484819356599665011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1340455919036568531546725 251335484819356599665011)
            ·
              refine ⟨377003227229034899497517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251335484819356599665011 377003227229034899497517)
              ·
                refine ⟨141376210210888087311569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377003227229034899497517 141376210210888087311569)
                ·
                  refine ⟨106032157658166065483677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141376210210888087311569 106032157658166065483677)
                  ·
                    rfl

theorem cell20_232309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_232309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232309 prefixEnd_232309 := by exact prefixLift 232309
  have htrace : WordTrace (prefixWord ++ tailWord_232309) baseStart_232309 baseEnd_232309 := by
    simpa [prefixWord, tailWord_232309, baseEnd_232309] using wordTrace_append hprefix tailTrace_232309
  have hstable : (prefixWord ++ tailWord_232309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232309).length < 2 ^ (prefixWord ++ tailWord_232309).sum := by decide
  have hdescent : baseEnd_232309 < baseStart_232309 := by decide
  rcases family_descends (prefixWord ++ tailWord_232309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232327 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_232327 : Nat := 118140960795 + 232327 * 2 ^ 59
def prefixEnd_232327 : Nat := 4983230072969 + 3 ^ 40 * 232327 * 2
def baseEnd_232327 : Nat := 106040373348638002883603

theorem tailTrace_232327 : CollatzResearch.WordTrace tailWord_232327 prefixEnd_232327 106040373348638002883603 := by
  unfold tailWord_232327
  simp only [CollatzResearch.WordTrace]
  refine ⟨8473661829326432137759235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5649107886217621425172823 8473661829326432137759235)
  ·
    refine ⟨12710492743989648206638853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8473661829326432137759235 12710492743989648206638853)
    ·
      refine ⟨2383217389498059038744785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12710492743989648206638853 2383217389498059038744785)
      ·
        refine ⟨1787413042123544279058589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2383217389498059038744785 1787413042123544279058589)
        ·
          refine ⟨670279890796329104646971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1787413042123544279058589 670279890796329104646971)
          ·
            refine ⟨1005419836194493656970457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670279890796329104646971 1005419836194493656970457)
            ·
              refine ⟨754064877145870242727843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005419836194493656970457 754064877145870242727843)
              ·
                refine ⟨1131097315718805364091765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754064877145870242727843 1131097315718805364091765)
                ·
                  refine ⟨106040373348638002883603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1131097315718805364091765 106040373348638002883603)
                  ·
                    rfl

theorem cell20_232327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_232327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232327 prefixEnd_232327 := by exact prefixLift 232327
  have htrace : WordTrace (prefixWord ++ tailWord_232327) baseStart_232327 baseEnd_232327 := by
    simpa [prefixWord, tailWord_232327, baseEnd_232327] using wordTrace_append hprefix tailTrace_232327
  have hstable : (prefixWord ++ tailWord_232327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232327).length < 2 ^ (prefixWord ++ tailWord_232327).sum := by decide
  have hdescent : baseEnd_232327 < baseStart_232327 := by decide
  rcases family_descends (prefixWord ++ tailWord_232327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232330 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_232330 : Nat := 118140960795 + 232330 * 2 ^ 59
def prefixEnd_232330 : Nat := 4983230072969 + 3 ^ 40 * 232330 * 2
def baseEnd_232330 : Nat := 106041742630383325783591

theorem tailTrace_232330 : CollatzResearch.WordTrace tailWord_232330 prefixEnd_232330 106041742630383325783591 := by
  unfold tailWord_232330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118442812078890912529611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5649180832210375766745629 2118442812078890912529611)
  ·
    refine ⟨3177664218118336368794417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2118442812078890912529611 3177664218118336368794417)
    ·
      refine ⟨2383248163588752276595813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3177664218118336368794417 2383248163588752276595813)
      ·
        refine ⟨446859030672891051861715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2383248163588752276595813 446859030672891051861715)
        ·
          refine ⟨670288546009336577792573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446859030672891051861715 670288546009336577792573)
          ·
            refine ⟨251358204753501216672215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670288546009336577792573 251358204753501216672215)
            ·
              refine ⟨377037307130251825008323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251358204753501216672215 377037307130251825008323)
              ·
                refine ⟨565555960695377737512485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377037307130251825008323 565555960695377737512485)
                ·
                  refine ⟨106041742630383325783591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565555960695377737512485 106041742630383325783591)
                  ·
                    rfl

theorem cell20_232330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_232330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232330 prefixEnd_232330 := by exact prefixLift 232330
  have htrace : WordTrace (prefixWord ++ tailWord_232330) baseStart_232330 baseEnd_232330 := by
    simpa [prefixWord, tailWord_232330, baseEnd_232330] using wordTrace_append hprefix tailTrace_232330
  have hstable : (prefixWord ++ tailWord_232330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232330).length < 2 ^ (prefixWord ++ tailWord_232330).sum := by decide
  have hdescent : baseEnd_232330 < baseStart_232330 := by decide
  rcases family_descends (prefixWord ++ tailWord_232330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232341 : List Nat := [1, 3, 2, 1, 1, 4, 1, 7]
def baseStart_232341 : Nat := 118140960795 + 232341 * 2 ^ 59
def prefixEnd_232341 : Nat := 4983230072969 + 3 ^ 40 * 232341 * 2
def baseEnd_232341 : Nat := 35348921110038725472293

theorem tailTrace_232341 : CollatzResearch.WordTrace tailWord_232341 prefixEnd_232341 35348921110038725472293 := by
  unfold tailWord_232341
  simp only [CollatzResearch.WordTrace]
  refine ⟨8474172451275712528768877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5649448300850475019179251 8474172451275712528768877)
  ·
    refine ⟨3177814669228392198288329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8474172451275712528768877 3177814669228392198288329)
    ·
      refine ⟨2383361001921294148716247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3177814669228392198288329 2383361001921294148716247)
      ·
        refine ⟨3575041502881941223074371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383361001921294148716247 3575041502881941223074371)
        ·
          refine ⟨5362562254322911834611557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575041502881941223074371 5362562254322911834611557)
          ·
            refine ⟨1005480422685545968989667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5362562254322911834611557 1005480422685545968989667)
            ·
              refine ⟨1508220634028318953484501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005480422685545968989667 1508220634028318953484501)
              ·
                refine ⟨35348921110038725472293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1508220634028318953484501 35348921110038725472293)
                ·
                  rfl

theorem cell20_232341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_232341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232341 prefixEnd_232341 := by exact prefixLift 232341
  have htrace : WordTrace (prefixWord ++ tailWord_232341) baseStart_232341 baseEnd_232341 := by
    simpa [prefixWord, tailWord_232341, baseEnd_232341] using wordTrace_append hprefix tailTrace_232341
  have hstable : (prefixWord ++ tailWord_232341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232341).length < 2 ^ (prefixWord ++ tailWord_232341).sum := by decide
  have hdescent : baseEnd_232341 < baseStart_232341 := by decide
  rcases family_descends (prefixWord ++ tailWord_232341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232382 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_232382 : Nat := 118140960795 + 232382 * 2 ^ 59
def prefixEnd_232382 : Nat := 4983230072969 + 3 ^ 40 * 232382 * 2
def baseEnd_232382 : Nat := 106065476847302256050045

theorem tailTrace_232382 : CollatzResearch.WordTrace tailWord_232382 prefixEnd_232382 106065476847302256050045 := by
  unfold tailWord_232382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059458480515897066376425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5650445229418117687340933 1059458480515897066376425)
  ·
    refine ⟨794593860386922799782319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1059458480515897066376425 794593860386922799782319)
    ·
      refine ⟨1191890790580384199673479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794593860386922799782319 1191890790580384199673479)
      ·
        refine ⟨1787836185870576299510219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191890790580384199673479 1787836185870576299510219)
        ·
          refine ⟨2681754278805864449265329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787836185870576299510219 2681754278805864449265329)
          ·
            refine ⟨2011315709104398336948997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2681754278805864449265329 2011315709104398336948997)
            ·
              refine ⟨377121695457074688177937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2011315709104398336948997 377121695457074688177937)
              ·
                refine ⟨282841271592806016133453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377121695457074688177937 282841271592806016133453)
                ·
                  refine ⟨106065476847302256050045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282841271592806016133453 106065476847302256050045)
                  ·
                    rfl

theorem cell20_232382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_232382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232382 prefixEnd_232382 := by exact prefixLift 232382
  have htrace : WordTrace (prefixWord ++ tailWord_232382) baseStart_232382 baseEnd_232382 := by
    simpa [prefixWord, tailWord_232382, baseEnd_232382] using wordTrace_append hprefix tailTrace_232382
  have hstable : (prefixWord ++ tailWord_232382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232382).length < 2 ^ (prefixWord ++ tailWord_232382).sum := by decide
  have hdescent : baseEnd_232382 < baseStart_232382 := by decide
  rcases family_descends (prefixWord ++ tailWord_232382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232406 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_232406 : Nat := 118140960795 + 232406 * 2 ^ 59
def prefixEnd_232406 : Nat := 4983230072969 + 3 ^ 40 * 232406 * 2
def baseEnd_232406 : Nat := 106076431101264839249947

theorem tailTrace_232406 : CollatzResearch.WordTrace tailWord_232406 prefixEnd_232406 106076431101264839249947 := by
  unfold tailWord_232406
  simp only [CollatzResearch.WordTrace]
  refine ⟨529783949752514289367817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5651028797360152419923381 529783949752514289367817)
  ·
    refine ⟨397337962314385717025863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 529783949752514289367817 397337962314385717025863)
    ·
      refine ⟨596006943471578575538795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397337962314385717025863 596006943471578575538795)
      ·
        refine ⟨894010415207367863308193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596006943471578575538795 894010415207367863308193)
        ·
          refine ⟨670507811405525897481145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894010415207367863308193 670507811405525897481145)
          ·
            refine ⟨502880858554144423110859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670507811405525897481145 502880858554144423110859)
            ·
              refine ⟨754321287831216634666289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502880858554144423110859 754321287831216634666289)
              ·
                refine ⟨565740965873412475999717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754321287831216634666289 565740965873412475999717)
                ·
                  refine ⟨106076431101264839249947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 565740965873412475999717 106076431101264839249947)
                  ·
                    rfl

theorem cell20_232406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_232406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232406 prefixEnd_232406 := by exact prefixLift 232406
  have htrace : WordTrace (prefixWord ++ tailWord_232406) baseStart_232406 baseEnd_232406 := by
    simpa [prefixWord, tailWord_232406, baseEnd_232406] using wordTrace_append hprefix tailTrace_232406
  have hstable : (prefixWord ++ tailWord_232406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232406).length < 2 ^ (prefixWord ++ tailWord_232406).sum := by decide
  have hdescent : baseEnd_232406 < baseStart_232406 := by decide
  rcases family_descends (prefixWord ++ tailWord_232406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232410 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_232410 : Nat := 118140960795 + 232410 * 2 ^ 59
def prefixEnd_232410 : Nat := 4983230072969 + 3 ^ 40 * 232410 * 2
def baseEnd_232410 : Nat := 106078256810258603116597

theorem tailTrace_232410 : CollatzResearch.WordTrace tailWord_232410 prefixEnd_232410 106078256810258603116597 := by
  unfold tailWord_232410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119172272006434328257671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5651126058683824875353789 2119172272006434328257671)
  ·
    refine ⟨3178758408009651492386507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119172272006434328257671 3178758408009651492386507)
    ·
      refine ⟨4768137612014477238579761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3178758408009651492386507 4768137612014477238579761)
      ·
        refine ⟨3576103209010857928934821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4768137612014477238579761 3576103209010857928934821)
        ·
          refine ⟨670519351689535861675279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3576103209010857928934821 670519351689535861675279)
          ·
            refine ⟨1005779027534303792512919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670519351689535861675279 1005779027534303792512919)
            ·
              refine ⟨1508668541301455688769379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005779027534303792512919 1508668541301455688769379)
              ·
                refine ⟨2263002811952183533154069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508668541301455688769379 2263002811952183533154069)
                ·
                  refine ⟨106078256810258603116597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2263002811952183533154069 106078256810258603116597)
                  ·
                    rfl

theorem cell20_232410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_232410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232410 prefixEnd_232410 := by exact prefixLift 232410
  have htrace : WordTrace (prefixWord ++ tailWord_232410) baseStart_232410 baseEnd_232410 := by
    simpa [prefixWord, tailWord_232410, baseEnd_232410] using wordTrace_append hprefix tailTrace_232410
  have hstable : (prefixWord ++ tailWord_232410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232410).length < 2 ^ (prefixWord ++ tailWord_232410).sum := by decide
  have hdescent : baseEnd_232410 < baseStart_232410 := by decide
  rcases family_descends (prefixWord ++ tailWord_232410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232413 : List Nat := [1, 4, 3, 1, 2, 2, 3, 4]
def baseStart_232413 : Nat := 118140960795 + 232413 * 2 ^ 59
def prefixEnd_232413 : Nat := 4983230072969 + 3 ^ 40 * 232413 * 2
def baseEnd_232413 : Nat := 35359875364001308672195

theorem tailTrace_232413 : CollatzResearch.WordTrace tailWord_232413 prefixEnd_232413 35359875364001308672195 := by
  unfold tailWord_232413
  simp only [CollatzResearch.WordTrace]
  refine ⟨8476798507014868825389893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5651199004676579216926595 8476798507014868825389893)
  ·
    refine ⟨1589399720065287904760605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8476798507014868825389893 1589399720065287904760605)
    ·
      refine ⟨596024895024482964285227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1589399720065287904760605 596024895024482964285227)
      ·
        refine ⟨894037342536724446427841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596024895024482964285227 894037342536724446427841)
        ·
          refine ⟨670528006902543334820881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894037342536724446427841 670528006902543334820881)
          ·
            refine ⟨502896005176907501115661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670528006902543334820881 502896005176907501115661)
            ·
              refine ⟨188586001941340312918373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502896005176907501115661 188586001941340312918373)
              ·
                refine ⟨35359875364001308672195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188586001941340312918373 35359875364001308672195)
                ·
                  rfl

theorem cell20_232413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 4].length) (baseStart_232413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232413 prefixEnd_232413 := by exact prefixLift 232413
  have htrace : WordTrace (prefixWord ++ tailWord_232413) baseStart_232413 baseEnd_232413 := by
    simpa [prefixWord, tailWord_232413, baseEnd_232413] using wordTrace_append hprefix tailTrace_232413
  have hstable : (prefixWord ++ tailWord_232413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232413).length < 2 ^ (prefixWord ++ tailWord_232413).sum := by decide
  have hdescent : baseEnd_232413 < baseStart_232413 := by decide
  rcases family_descends (prefixWord ++ tailWord_232413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232437 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 5]
def baseStart_232437 : Nat := 118140960795 + 232437 * 2 ^ 59
def prefixEnd_232437 : Nat := 4983230072969 + 3 ^ 40 * 232437 * 2
def baseEnd_232437 : Nat := 106090580345966509216487

theorem tailTrace_232437 : CollatzResearch.WordTrace tailWord_232437 prefixEnd_232437 106090580345966509216487 := by
  unfold tailWord_232437
  simp only [CollatzResearch.WordTrace]
  refine ⟨8477673858927920924263565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5651782572618613949509043 8477673858927920924263565)
  ·
    refine ⟨3179127697097970346598837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8477673858927920924263565 3179127697097970346598837)
    ·
      refine ⟨298043221602934719993641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3179127697097970346598837 298043221602934719993641)
      ·
        refine ⟨223532416202201039995231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298043221602934719993641 223532416202201039995231)
        ·
          refine ⟨335298624303301559992847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223532416202201039995231 335298624303301559992847)
          ·
            refine ⟨502947936454952339989271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335298624303301559992847 502947936454952339989271)
            ·
              refine ⟨754421904682428509983907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502947936454952339989271 754421904682428509983907)
              ·
                refine ⟨1131632857023642764975861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754421904682428509983907 1131632857023642764975861)
                ·
                  refine ⟨106090580345966509216487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1131632857023642764975861 106090580345966509216487)
                  ·
                    rfl

theorem cell20_232437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_232437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232437 prefixEnd_232437 := by exact prefixLift 232437
  have htrace : WordTrace (prefixWord ++ tailWord_232437) baseStart_232437 baseEnd_232437 := by
    simpa [prefixWord, tailWord_232437, baseEnd_232437] using wordTrace_append hprefix tailTrace_232437
  have hstable : (prefixWord ++ tailWord_232437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232437).length < 2 ^ (prefixWord ++ tailWord_232437).sum := by decide
  have hdescent : baseEnd_232437 < baseStart_232437 := by decide
  rcases family_descends (prefixWord ++ tailWord_232437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232455 : List Nat := [1, 1, 4, 3, 1, 1, 2, 7]
def baseStart_232455 : Nat := 118140960795 + 232455 * 2 ^ 59
def prefixEnd_232455 : Nat := 4983230072969 + 3 ^ 40 * 232455 * 2
def baseEnd_232455 : Nat := 35366265345479482205471

theorem tailTrace_232455 : CollatzResearch.WordTrace tailWord_232455 prefixEnd_232455 35366265345479482205471 := by
  unfold tailWord_232455
  simp only [CollatzResearch.WordTrace]
  refine ⟨8478330372862709998418819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5652220248575139998945879 8478330372862709998418819)
  ·
    refine ⟨12717495559294064997628229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8478330372862709998418819 12717495559294064997628229)
    ·
      refine ⟨2384530417367637187055293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12717495559294064997628229 2384530417367637187055293)
      ·
        refine ⟨894198906512863945145735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2384530417367637187055293 894198906512863945145735)
        ·
          refine ⟨1341298359769295917718603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894198906512863945145735 1341298359769295917718603)
          ·
            refine ⟨2011947539653943876577905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341298359769295917718603 2011947539653943876577905)
            ·
              refine ⟨1508960654740457907433429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011947539653943876577905 1508960654740457907433429)
              ·
                refine ⟨35366265345479482205471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1508960654740457907433429 35366265345479482205471)
                ·
                  rfl

theorem cell20_232455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_232455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232455 prefixEnd_232455 := by exact prefixLift 232455
  have htrace : WordTrace (prefixWord ++ tailWord_232455) baseStart_232455 baseEnd_232455 := by
    simpa [prefixWord, tailWord_232455, baseEnd_232455] using wordTrace_append hprefix tailTrace_232455
  have hstable : (prefixWord ++ tailWord_232455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232455).length < 2 ^ (prefixWord ++ tailWord_232455).sum := by decide
  have hdescent : baseEnd_232455 < baseStart_232455 := by decide
  rcases family_descends (prefixWord ++ tailWord_232455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232472 : List Nat := [2, 1, 2, 3, 2, 2, 4, 4]
def baseStart_232472 : Nat := 118140960795 + 232472 * 2 ^ 59
def prefixEnd_232472 : Nat := 4983230072969 + 3 ^ 40 * 232472 * 2
def baseEnd_232472 : Nat := 35368851766553981016559

theorem tailTrace_232472 : CollatzResearch.WordTrace tailWord_232472 prefixEnd_232472 35368851766553981016559 := by
  unfold tailWord_232472
  simp only [CollatzResearch.WordTrace]
  refine ⟨4239475206900560950893835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5652633609200747934525113 4239475206900560950893835)
  ·
    refine ⟨6359212810350841426340753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4239475206900560950893835 6359212810350841426340753)
    ·
      refine ⟨4769409607763131069755565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6359212810350841426340753 4769409607763131069755565)
      ·
        refine ⟨1788528602911174151158337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4769409607763131069755565 1788528602911174151158337)
        ·
          refine ⟨1341396452183380613368753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1788528602911174151158337 1341396452183380613368753)
          ·
            refine ⟨1006047339137535460026565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341396452183380613368753 1006047339137535460026565)
            ·
              refine ⟨188633876088287898754981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1006047339137535460026565 188633876088287898754981)
              ·
                refine ⟨35368851766553981016559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188633876088287898754981 35368851766553981016559)
                ·
                  rfl

theorem cell20_232472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_232472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232472 prefixEnd_232472 := by exact prefixLift 232472
  have htrace : WordTrace (prefixWord ++ tailWord_232472) baseStart_232472 baseEnd_232472 := by
    simpa [prefixWord, tailWord_232472, baseEnd_232472] using wordTrace_append hprefix tailTrace_232472
  have hstable : (prefixWord ++ tailWord_232472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232472).length < 2 ^ (prefixWord ++ tailWord_232472).sum := by decide
  have hdescent : baseEnd_232472 < baseStart_232472 := by decide
  rcases family_descends (prefixWord ++ tailWord_232472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232482 : List Nat := [3, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_232482 : Nat := 118140960795 + 232482 * 2 ^ 59
def prefixEnd_232482 : Nat := 4983230072969 + 3 ^ 40 * 232482 * 2
def baseEnd_232482 : Nat := 106111119572146352716303

theorem tailTrace_232482 : CollatzResearch.WordTrace tailWord_232482 prefixEnd_232482 106111119572146352716303 := by
  unfold tailWord_232482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119828785941223402412925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5652876762509929073101133 2119828785941223402412925)
  ·
    refine ⟨794935794727958775904847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2119828785941223402412925 794935794727958775904847)
    ·
      refine ⟨1192403692091938163857271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794935794727958775904847 1192403692091938163857271)
      ·
        refine ⟨1788605538137907245785907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192403692091938163857271 1788605538137907245785907)
        ·
          refine ⟨2682908307206860868678861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788605538137907245785907 2682908307206860868678861)
          ·
            refine ⟨1006090615202572825754573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2682908307206860868678861 1006090615202572825754573)
            ·
              refine ⟨377283980700964809657965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1006090615202572825754573 377283980700964809657965)
              ·
                refine ⟨141481492762861803621737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377283980700964809657965 141481492762861803621737)
                ·
                  refine ⟨106111119572146352716303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141481492762861803621737 106111119572146352716303)
                  ·
                    rfl

theorem cell20_232482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_232482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232482 prefixEnd_232482 := by exact prefixLift 232482
  have htrace : WordTrace (prefixWord ++ tailWord_232482) baseStart_232482 baseEnd_232482 := by
    simpa [prefixWord, tailWord_232482, baseEnd_232482] using wordTrace_append hprefix tailTrace_232482
  have hstable : (prefixWord ++ tailWord_232482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232482).length < 2 ^ (prefixWord ++ tailWord_232482).sum := by decide
  have hdescent : baseEnd_232482 < baseStart_232482 := by decide
  rcases family_descends (prefixWord ++ tailWord_232482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232510 : List Nat := [4, 2, 1, 3, 1, 1, 1, 7]
def baseStart_232510 : Nat := 118140960795 + 232510 * 2 ^ 59
def prefixEnd_232510 : Nat := 4983230072969 + 3 ^ 40 * 232510 * 2
def baseEnd_232510 : Nat := 35374633178367566594285

theorem tailTrace_232510 : CollatzResearch.WordTrace tailWord_232510 prefixEnd_232510 35374633178367566594285 := by
  unfold tailWord_232510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060042048457931798958873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5653557591775636261113989 1060042048457931798958873)
  ·
    refine ⟨795031536343448849219155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1060042048457931798958873 795031536343448849219155)
    ·
      refine ⟨1192547304515173273828733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795031536343448849219155 1192547304515173273828733)
      ·
        refine ⟨447205239193189977685775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1192547304515173273828733 447205239193189977685775)
        ·
          refine ⟨670807858789784966528663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447205239193189977685775 670807858789784966528663)
          ·
            refine ⟨1006211788184677449792995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670807858789784966528663 1006211788184677449792995)
            ·
              refine ⟨1509317682277016174689493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006211788184677449792995 1509317682277016174689493)
              ·
                refine ⟨35374633178367566594285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1509317682277016174689493 35374633178367566594285)
                ·
                  rfl

theorem cell20_232510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_232510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232510 prefixEnd_232510 := by exact prefixLift 232510
  have htrace : WordTrace (prefixWord ++ tailWord_232510) baseStart_232510 baseEnd_232510 := by
    simpa [prefixWord, tailWord_232510, baseEnd_232510] using wordTrace_append hprefix tailTrace_232510
  have hstable : (prefixWord ++ tailWord_232510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232510).length < 2 ^ (prefixWord ++ tailWord_232510).sum := by decide
  have hdescent : baseEnd_232510 < baseStart_232510 := by decide
  rcases family_descends (prefixWord ++ tailWord_232510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232538 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_232538 : Nat := 118140960795 + 232538 * 2 ^ 59
def prefixEnd_232538 : Nat := 4983230072969 + 3 ^ 40 * 232538 * 2
def baseEnd_232538 : Nat := 106136679498059046849407

theorem tailTrace_232538 : CollatzResearch.WordTrace tailWord_232538 prefixEnd_232538 106136679498059046849407 := by
  unfold tailWord_232538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120339407890503793422567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5654238421041343449126845 2120339407890503793422567)
  ·
    refine ⟨3180509111835755690133851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2120339407890503793422567 3180509111835755690133851)
    ·
      refine ⟨4770763667753633535200777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180509111835755690133851 4770763667753633535200777)
      ·
        refine ⟨3578072750815225151400583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4770763667753633535200777 3578072750815225151400583)
        ·
          refine ⟨5367109126222837727100875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578072750815225151400583 5367109126222837727100875)
          ·
            refine ⟨8050663689334256590651313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367109126222837727100875 8050663689334256590651313)
            ·
              refine ⟨6037997767000692442988485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8050663689334256590651313 6037997767000692442988485)
              ·
                refine ⟨1132124581312629833060341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6037997767000692442988485 1132124581312629833060341)
                ·
                  refine ⟨106136679498059046849407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1132124581312629833060341 106136679498059046849407)
                  ·
                    rfl

theorem cell20_232538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_232538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232538 prefixEnd_232538 := by exact prefixLift 232538
  have htrace : WordTrace (prefixWord ++ tailWord_232538) baseStart_232538 baseEnd_232538 := by
    simpa [prefixWord, tailWord_232538, baseEnd_232538] using wordTrace_append hprefix tailTrace_232538
  have hstable : (prefixWord ++ tailWord_232538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232538).length < 2 ^ (prefixWord ++ tailWord_232538).sum := by decide
  have hdescent : baseEnd_232538 < baseStart_232538 := by decide
  rcases family_descends (prefixWord ++ tailWord_232538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232558 : List Nat := [4, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_232558 : Nat := 118140960795 + 232558 * 2 ^ 59
def prefixEnd_232558 : Nat := 4983230072969 + 3 ^ 40 * 232558 * 2
def baseEnd_232558 : Nat := 106145808043027866182659

theorem tailTrace_232558 : CollatzResearch.WordTrace tailWord_232558 prefixEnd_232558 106145808043027866182659 := by
  unfold tailWord_232558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060260886436194823677291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5654724727659705726278885 1060260886436194823677291)
  ·
    refine ⟨1590391329654292235515937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1060260886436194823677291 1590391329654292235515937)
    ·
      refine ⟨1192793497240719176636953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1590391329654292235515937 1192793497240719176636953)
      ·
        refine ⟨894595122930539382477715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1192793497240719176636953 894595122930539382477715)
        ·
          refine ⟨1341892684395809073716573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894595122930539382477715 1341892684395809073716573)
          ·
            refine ⟨503209756648428402643715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1341892684395809073716573 503209756648428402643715)
            ·
              refine ⟨754814634972642603965573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503209756648428402643715 754814634972642603965573)
              ·
                refine ⟨141527744057370488243545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754814634972642603965573 141527744057370488243545)
                ·
                  refine ⟨106145808043027866182659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141527744057370488243545 106145808043027866182659)
                  ·
                    rfl

theorem cell20_232558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_232558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232558 prefixEnd_232558 := by exact prefixLift 232558
  have htrace : WordTrace (prefixWord ++ tailWord_232558) baseStart_232558 baseEnd_232558 := by
    simpa [prefixWord, tailWord_232558, baseEnd_232558] using wordTrace_append hprefix tailTrace_232558
  have hstable : (prefixWord ++ tailWord_232558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232558).length < 2 ^ (prefixWord ++ tailWord_232558).sum := by decide
  have hdescent : baseEnd_232558 < baseStart_232558 := by decide
  rcases family_descends (prefixWord ++ tailWord_232558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232562 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_232562 : Nat := 118140960795 + 232562 * 2 ^ 59
def prefixEnd_232562 : Nat := 4983230072969 + 3 ^ 40 * 232562 * 2
def baseEnd_232562 : Nat := 106147633752021630049309

theorem tailTrace_232562 : CollatzResearch.WordTrace tailWord_232562 prefixEnd_232562 106147633752021630049309 := by
  unfold tailWord_232562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120558245868766818140985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5654821988983378181709293 2120558245868766818140985)
  ·
    refine ⟨1590418684401575113605739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2120558245868766818140985 1590418684401575113605739)
    ·
      refine ⟨2385628026602362670408609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1590418684401575113605739 2385628026602362670408609)
      ·
        refine ⟨1789221019951772002806457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2385628026602362670408609 1789221019951772002806457)
        ·
          refine ⟨1341915764963829002104843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789221019951772002806457 1341915764963829002104843)
          ·
            refine ⟨2012873647445743503157265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341915764963829002104843 2012873647445743503157265)
            ·
              refine ⟨1509655235584307627367949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012873647445743503157265 1509655235584307627367949)
              ·
                refine ⟨566120713344115360262981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1509655235584307627367949 566120713344115360262981)
                ·
                  refine ⟨106147633752021630049309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566120713344115360262981 106147633752021630049309)
                  ·
                    rfl

theorem cell20_232562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_232562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232562 prefixEnd_232562 := by exact prefixLift 232562
  have htrace : WordTrace (prefixWord ++ tailWord_232562) baseStart_232562 baseEnd_232562 := by
    simpa [prefixWord, tailWord_232562, baseEnd_232562] using wordTrace_append hprefix tailTrace_232562
  have hstable : (prefixWord ++ tailWord_232562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232562).length < 2 ^ (prefixWord ++ tailWord_232562).sum := by decide
  have hdescent : baseEnd_232562 < baseStart_232562 := by decide
  rcases family_descends (prefixWord ++ tailWord_232562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232586 : List Nat := [3, 1, 2, 3, 1, 1, 5, 4]
def baseStart_232586 : Nat := 118140960795 + 232586 * 2 ^ 59
def prefixEnd_232586 : Nat := 4983230072969 + 3 ^ 40 * 232586 * 2
def baseEnd_232586 : Nat := 35386196001994737749737

theorem tailTrace_232586 : CollatzResearch.WordTrace tailWord_232586 prefixEnd_232586 35386196001994737749737 := by
  unfold tailWord_232586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120777083847029842859403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5655405556925412914291741 2120777083847029842859403)
  ·
    refine ⟨3181165625770544764289105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2120777083847029842859403 3181165625770544764289105)
    ·
      refine ⟨2385874219327908573216829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3181165625770544764289105 2385874219327908573216829)
      ·
        refine ⟨894702832247965714956311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2385874219327908573216829 894702832247965714956311)
        ·
          refine ⟨1342054248371948572434467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894702832247965714956311 1342054248371948572434467)
          ·
            refine ⟨2013081372557922858651701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342054248371948572434467 2013081372557922858651701)
            ·
              refine ⟨188726378677305267998597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2013081372557922858651701 188726378677305267998597)
              ·
                refine ⟨35386196001994737749737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188726378677305267998597 35386196001994737749737)
                ·
                  rfl

theorem cell20_232586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_232586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232586 prefixEnd_232586 := by exact prefixLift 232586
  have htrace : WordTrace (prefixWord ++ tailWord_232586) baseStart_232586 baseEnd_232586 := by
    simpa [prefixWord, tailWord_232586, baseEnd_232586] using wordTrace_append hprefix tailTrace_232586
  have hstable : (prefixWord ++ tailWord_232586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232586).length < 2 ^ (prefixWord ++ tailWord_232586).sum := by decide
  have hdescent : baseEnd_232586 < baseStart_232586 := by decide
  rcases family_descends (prefixWord ++ tailWord_232586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232610 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_232610 : Nat := 118140960795 + 232610 * 2 ^ 59
def prefixEnd_232610 : Nat := 4983230072969 + 3 ^ 40 * 232610 * 2
def baseEnd_232610 : Nat := 106169542259946796449113

theorem tailTrace_232610 : CollatzResearch.WordTrace tailWord_232610 prefixEnd_232610 106169542259946796449113 := by
  unfold tailWord_232610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120995921825292867577821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5655989124867447646874189 2120995921825292867577821)
  ·
    refine ⟨795373470684484825341683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2120995921825292867577821 795373470684484825341683)
    ·
      refine ⟨1193060206026727238012525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795373470684484825341683 1193060206026727238012525)
      ·
        refine ⟨447397577260022714254697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1193060206026727238012525 447397577260022714254697)
        ·
          refine ⟨335548182945017035691023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447397577260022714254697 335548182945017035691023)
          ·
            refine ⟨503322274417525553536535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335548182945017035691023 503322274417525553536535)
            ·
              refine ⟨754983411626288330304803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503322274417525553536535 754983411626288330304803)
              ·
                refine ⟨1132475117439432495457205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754983411626288330304803 1132475117439432495457205)
                ·
                  refine ⟨106169542259946796449113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1132475117439432495457205 106169542259946796449113)
                  ·
                    rfl

theorem cell20_232610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_232610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232610 prefixEnd_232610 := by exact prefixLift 232610
  have htrace : WordTrace (prefixWord ++ tailWord_232610) baseStart_232610 baseEnd_232610 := by
    simpa [prefixWord, tailWord_232610, baseEnd_232610] using wordTrace_append hprefix tailTrace_232610
  have hstable : (prefixWord ++ tailWord_232610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232610).length < 2 ^ (prefixWord ++ tailWord_232610).sum := by decide
  have hdescent : baseEnd_232610 < baseStart_232610 := by decide
  rcases family_descends (prefixWord ++ tailWord_232610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232641 : List Nat := [1, 2, 6, 1, 1, 1, 4, 4]
def baseStart_232641 : Nat := 118140960795 + 232641 * 2 ^ 59
def prefixEnd_232641 : Nat := 4983230072969 + 3 ^ 40 * 232641 * 2
def baseEnd_232641 : Nat := 35394563834882822138551

theorem tailTrace_232641 : CollatzResearch.WordTrace tailWord_232641 prefixEnd_232641 35394563834882822138551 := by
  unfold tailWord_232641
  simp only [CollatzResearch.WordTrace]
  refine ⟨8485114350188863764689777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5656742900125909176459851 8485114350188863764689777)
  ·
    refine ⟨6363835762641647823517333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8485114350188863764689777 6363835762641647823517333)
    ·
      refine ⟨298304801373827241727375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6363835762641647823517333 298304801373827241727375)
      ·
        refine ⟨447457202060740862591063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298304801373827241727375 447457202060740862591063)
        ·
          refine ⟨671185803091111293886595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447457202060740862591063 671185803091111293886595)
          ·
            refine ⟨1006778704636666940829893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671185803091111293886595 1006778704636666940829893)
            ·
              refine ⟨188771007119375051405605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1006778704636666940829893 188771007119375051405605)
              ·
                refine ⟨35394563834882822138551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188771007119375051405605 35394563834882822138551)
                ·
                  rfl

theorem cell20_232641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 4].length) (baseStart_232641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232641 prefixEnd_232641 := by exact prefixLift 232641
  have htrace : WordTrace (prefixWord ++ tailWord_232641) baseStart_232641 baseEnd_232641 := by
    simpa [prefixWord, tailWord_232641, baseEnd_232641] using wordTrace_append hprefix tailTrace_232641
  have hstable : (prefixWord ++ tailWord_232641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232641).length < 2 ^ (prefixWord ++ tailWord_232641).sum := by decide
  have hdescent : baseEnd_232641 < baseStart_232641 := by decide
  rcases family_descends (prefixWord ++ tailWord_232641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232672 : List Nat := [2, 1, 1, 3, 1, 5, 3, 2, 2]
def baseStart_232672 : Nat := 118140960795 + 232672 * 2 ^ 59
def prefixEnd_232672 : Nat := 4983230072969 + 3 ^ 40 * 232672 * 2
def baseEnd_232672 : Nat := 106197840749350136382193

theorem tailTrace_232672 : CollatzResearch.WordTrace tailWord_232672 prefixEnd_232672 106197840749350136382193 := by
  unfold tailWord_232672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243122506538278029534135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5657496675384370706045513 4243122506538278029534135)
  ·
    refine ⟨6364683759807417044301203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4243122506538278029534135 6364683759807417044301203)
    ·
      refine ⟨9547025639711125566451805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6364683759807417044301203 9547025639711125566451805)
      ·
        refine ⟨3580134614891672087419427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9547025639711125566451805 3580134614891672087419427)
        ·
          refine ⟨5370201922337508131129141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580134614891672087419427 5370201922337508131129141)
          ·
            refine ⟨503456430219141387293357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5370201922337508131129141 503456430219141387293357)
            ·
              refine ⟨188796161332178020235009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503456430219141387293357 188796161332178020235009)
              ·
                refine ⟨141597120999133515176257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188796161332178020235009 141597120999133515176257)
                ·
                  refine ⟨106197840749350136382193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141597120999133515176257 106197840749350136382193)
                  ·
                    rfl

theorem cell20_232672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_232672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232672 prefixEnd_232672 := by exact prefixLift 232672
  have htrace : WordTrace (prefixWord ++ tailWord_232672) baseStart_232672 baseEnd_232672 := by
    simpa [prefixWord, tailWord_232672, baseEnd_232672] using wordTrace_append hprefix tailTrace_232672
  have hstable : (prefixWord ++ tailWord_232672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232672).length < 2 ^ (prefixWord ++ tailWord_232672).sum := by decide
  have hdescent : baseEnd_232672 < baseStart_232672 := by decide
  rcases family_descends (prefixWord ++ tailWord_232672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232676 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_232676 : Nat := 118140960795 + 232676 * 2 ^ 59
def prefixEnd_232676 : Nat := 4983230072969 + 3 ^ 40 * 232676 * 2
def baseEnd_232676 : Nat := 106199666458343900248843

theorem tailTrace_232676 : CollatzResearch.WordTrace tailWord_232676 prefixEnd_232676 106199666458343900248843 := by
  unfold tailWord_232676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243195452531032371106941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5657593936708043161475921 4243195452531032371106941)
  ·
    refine ⟨1591198294699137139165103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4243195452531032371106941 1591198294699137139165103)
    ·
      refine ⟨2386797442048705708747655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591198294699137139165103 2386797442048705708747655)
      ·
        refine ⟨3580196163073058563121483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386797442048705708747655 3580196163073058563121483)
        ·
          refine ⟨5370294244609587844682225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580196163073058563121483 5370294244609587844682225)
          ·
            refine ⟨4027720683457190883511669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5370294244609587844682225 4027720683457190883511669)
            ·
              refine ⟨377598814074111645329219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4027720683457190883511669 377598814074111645329219)
              ·
                refine ⟨566398221111167467993829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377598814074111645329219 566398221111167467993829)
                ·
                  refine ⟨106199666458343900248843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566398221111167467993829 106199666458343900248843)
                  ·
                    rfl

theorem cell20_232676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_232676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232676 prefixEnd_232676 := by exact prefixLift 232676
  have htrace : WordTrace (prefixWord ++ tailWord_232676) baseStart_232676 baseEnd_232676 := by
    simpa [prefixWord, tailWord_232676, baseEnd_232676] using wordTrace_append hprefix tailTrace_232676
  have hstable : (prefixWord ++ tailWord_232676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232676).length < 2 ^ (prefixWord ++ tailWord_232676).sum := by decide
  have hdescent : baseEnd_232676 < baseStart_232676 := by decide
  rcases family_descends (prefixWord ++ tailWord_232676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232683 : List Nat := [1, 1, 1, 1, 2, 7, 2, 5]
def baseStart_232683 : Nat := 118140960795 + 232683 * 2 ^ 59
def prefixEnd_232683 : Nat := 4983230072969 + 3 ^ 40 * 232683 * 2
def baseEnd_232683 : Nat := 35400953816360995671827

theorem tailTrace_232683 : CollatzResearch.WordTrace tailWord_232683 prefixEnd_232683 35400953816360995671827 := by
  unfold tailWord_232683
  simp only [CollatzResearch.WordTrace]
  refine ⟨8486646216036704937718703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5657764144024469958479135 8486646216036704937718703)
  ·
    refine ⟨12729969324055057406578055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8486646216036704937718703 12729969324055057406578055)
    ·
      refine ⟨19094953986082586109867083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12729969324055057406578055 19094953986082586109867083)
      ·
        refine ⟨28642430979123879164800625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19094953986082586109867083 28642430979123879164800625)
        ·
          refine ⟨21481823234342909373600469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28642430979123879164800625 21481823234342909373600469)
          ·
            refine ⟨503480232054911938443761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21481823234342909373600469 503480232054911938443761)
            ·
              refine ⟨377610174041183953832821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503480232054911938443761 377610174041183953832821)
              ·
                refine ⟨35400953816360995671827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377610174041183953832821 35400953816360995671827)
                ·
                  rfl

theorem cell20_232683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_232683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232683 prefixEnd_232683 := by exact prefixLift 232683
  have htrace : WordTrace (prefixWord ++ tailWord_232683) baseStart_232683 baseEnd_232683 := by
    simpa [prefixWord, tailWord_232683, baseEnd_232683] using wordTrace_append hprefix tailTrace_232683
  have hstable : (prefixWord ++ tailWord_232683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232683).length < 2 ^ (prefixWord ++ tailWord_232683).sum := by decide
  have hdescent : baseEnd_232683 < baseStart_232683 := by decide
  rcases family_descends (prefixWord ++ tailWord_232683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232686 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_232686 : Nat := 118140960795 + 232686 * 2 ^ 59
def prefixEnd_232686 : Nat := 4983230072969 + 3 ^ 40 * 232686 * 2
def baseEnd_232686 : Nat := 106204230730828309915469

theorem tailTrace_232686 : CollatzResearch.WordTrace tailWord_232686 prefixEnd_232686 106204230730828309915469 := by
  unfold tailWord_232686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060844454378229556259739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5657837090017224300051941 1060844454378229556259739)
  ·
    refine ⟨1591266681567344334389609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1060844454378229556259739 1591266681567344334389609)
    ·
      refine ⟨1193450011175508250792207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1591266681567344334389609 1193450011175508250792207)
      ·
        refine ⟨1790175016763262376188311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193450011175508250792207 1790175016763262376188311)
        ·
          refine ⟨2685262525144893564282467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790175016763262376188311 2685262525144893564282467)
          ·
            refine ⟨4027893787717340346423701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685262525144893564282467 4027893787717340346423701)
            ·
              refine ⟨188807521299250328738611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4027893787717340346423701 188807521299250328738611)
              ·
                refine ⟨283211281948875493107917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188807521299250328738611 283211281948875493107917)
                ·
                  refine ⟨106204230730828309915469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283211281948875493107917 106204230730828309915469)
                  ·
                    rfl

theorem cell20_232686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_232686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232686 prefixEnd_232686 := by exact prefixLift 232686
  have htrace : WordTrace (prefixWord ++ tailWord_232686) baseStart_232686 baseEnd_232686 := by
    simpa [prefixWord, tailWord_232686, baseEnd_232686] using wordTrace_append hprefix tailTrace_232686
  have hstable : (prefixWord ++ tailWord_232686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232686).length < 2 ^ (prefixWord ++ tailWord_232686).sum := by decide
  have hdescent : baseEnd_232686 < baseStart_232686 := by decide
  rcases family_descends (prefixWord ++ tailWord_232686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232697 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_232697 : Nat := 118140960795 + 232697 * 2 ^ 59
def prefixEnd_232697 : Nat := 4983230072969 + 3 ^ 40 * 232697 * 2
def baseEnd_232697 : Nat := 106209251430561160548757

theorem tailTrace_232697 : CollatzResearch.WordTrace tailWord_232697 prefixEnd_232697 106209251430561160548757 := by
  unfold tailWord_232697
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487156837985985328728345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5658104558657323552485563 8487156837985985328728345)
  ·
    refine ⟨6365367628489488996546259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8487156837985985328728345 6365367628489488996546259)
    ·
      refine ⟨9548051442734233494819389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6365367628489488996546259 9548051442734233494819389)
      ·
        refine ⟨3580519291025337560557271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9548051442734233494819389 3580519291025337560557271)
        ·
          refine ⟨5370778936538006340835907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580519291025337560557271 5370778936538006340835907)
          ·
            refine ⟨8056168404807009511253861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370778936538006340835907 8056168404807009511253861)
            ·
              refine ⟨1510531575901314283360099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8056168404807009511253861 1510531575901314283360099)
              ·
                refine ⟨2265797363851971425040149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510531575901314283360099 2265797363851971425040149)
                ·
                  refine ⟨106209251430561160548757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2265797363851971425040149 106209251430561160548757)
                  ·
                    rfl

theorem cell20_232697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_232697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232697 prefixEnd_232697 := by exact prefixLift 232697
  have htrace : WordTrace (prefixWord ++ tailWord_232697) baseStart_232697 baseEnd_232697 := by
    simpa [prefixWord, tailWord_232697, baseEnd_232697] using wordTrace_append hprefix tailTrace_232697
  have hstable : (prefixWord ++ tailWord_232697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232697).length < 2 ^ (prefixWord ++ tailWord_232697).sum := by decide
  have hdescent : baseEnd_232697 < baseStart_232697 := by decide
  rcases family_descends (prefixWord ++ tailWord_232697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232734 : List Nat := [4, 3, 2, 1, 2, 2, 1, 5]
def baseStart_232734 : Nat := 118140960795 + 232734 * 2 ^ 59
def prefixEnd_232734 : Nat := 4983230072969 + 3 ^ 40 * 232734 * 2
def baseEnd_232734 : Nat := 35408713079584492105091

theorem tailTrace_232734 : CollatzResearch.WordTrace tailWord_232734 prefixEnd_232734 35408713079584492105091 := by
  unfold tailWord_232734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061063292356492580978157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5659004225901293765216837 1061063292356492580978157)
  ·
    refine ⟨397898734633684717866809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1061063292356492580978157 397898734633684717866809)
    ·
      refine ⟨298424050975263538400107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397898734633684717866809 298424050975263538400107)
      ·
        refine ⟨447636076462895307600161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298424050975263538400107 447636076462895307600161)
        ·
          refine ⟨335727057347171480700121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447636076462895307600161 335727057347171480700121)
          ·
            refine ⟨251795293010378610525091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335727057347171480700121 251795293010378610525091)
            ·
              refine ⟨377692939515567915787637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251795293010378610525091 377692939515567915787637)
              ·
                refine ⟨35408713079584492105091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377692939515567915787637 35408713079584492105091)
                ·
                  rfl

theorem cell20_232734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_232734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232734 prefixEnd_232734 := by exact prefixLift 232734
  have htrace : WordTrace (prefixWord ++ tailWord_232734) baseStart_232734 baseEnd_232734 := by
    simpa [prefixWord, tailWord_232734, baseEnd_232734] using wordTrace_append hprefix tailTrace_232734
  have hstable : (prefixWord ++ tailWord_232734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232734).length < 2 ^ (prefixWord ++ tailWord_232734).sum := by decide
  have hdescent : baseEnd_232734 < baseStart_232734 := by decide
  rcases family_descends (prefixWord ++ tailWord_232734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232765 : List Nat := [1, 4, 1, 5, 1, 1, 2, 3, 2]
def baseStart_232765 : Nat := 118140960795 + 232765 * 2 ^ 59
def prefixEnd_232765 : Nat := 4983230072969 + 3 ^ 40 * 232765 * 2
def baseEnd_232765 : Nat := 106240288483455146281813

theorem tailTrace_232765 : CollatzResearch.WordTrace tailWord_232765 prefixEnd_232765 106240288483455146281813 := by
  unfold tailWord_232765
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489637001739632942203749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5659758001159755294802499 8489637001739632942203749)
  ·
    refine ⟨1591806937826181176663203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8489637001739632942203749 1591806937826181176663203)
    ·
      refine ⟨2387710406739271764994805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591806937826181176663203 2387710406739271764994805)
      ·
        refine ⟨223847850631806727968263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2387710406739271764994805 223847850631806727968263)
        ·
          refine ⟨335771775947710091952395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223847850631806727968263 335771775947710091952395)
          ·
            refine ⟨503657663921565137928593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335771775947710091952395 503657663921565137928593)
            ·
              refine ⟨377743247941173853446445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503657663921565137928593 377743247941173853446445)
              ·
                refine ⟨141653717977940195042417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377743247941173853446445 141653717977940195042417)
                ·
                  refine ⟨106240288483455146281813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141653717977940195042417 106240288483455146281813)
                  ·
                    rfl

theorem cell20_232765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_232765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232765 prefixEnd_232765 := by exact prefixLift 232765
  have htrace : WordTrace (prefixWord ++ tailWord_232765) baseStart_232765 baseEnd_232765 := by
    simpa [prefixWord, tailWord_232765, baseEnd_232765] using wordTrace_append hprefix tailTrace_232765
  have hstable : (prefixWord ++ tailWord_232765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232765).length < 2 ^ (prefixWord ++ tailWord_232765).sum := by decide
  have hdescent : baseEnd_232765 < baseStart_232765 := by decide
  rcases family_descends (prefixWord ++ tailWord_232765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232800 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_232800 : Nat := 118140960795 + 232800 * 2 ^ 59
def prefixEnd_232800 : Nat := 4983230072969 + 3 ^ 40 * 232800 * 2
def baseEnd_232800 : Nat := 106256263437150580115003

theorem tailTrace_232800 : CollatzResearch.WordTrace tailWord_232800 prefixEnd_232800 106256263437150580115003 := by
  unfold tailWord_232800
  simp only [CollatzResearch.WordTrace]
  refine ⟨4245456778306416959863927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5660609037741889279818569 4245456778306416959863927)
  ·
    refine ⟨6368185167459625439795891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4245456778306416959863927 6368185167459625439795891)
    ·
      refine ⟨9552277751189438159693837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6368185167459625439795891 9552277751189438159693837)
      ·
        refine ⟨3582104156696039309885189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9552277751189438159693837 3582104156696039309885189)
        ·
          refine ⟨671644529380507370603473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3582104156696039309885189 671644529380507370603473)
          ·
            refine ⟨503733397035380527952605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671644529380507370603473 503733397035380527952605)
            ·
              refine ⟨188900023888267697982227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503733397035380527952605 188900023888267697982227)
              ·
                refine ⟨283350035832401546973341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188900023888267697982227 283350035832401546973341)
                ·
                  refine ⟨106256263437150580115003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283350035832401546973341 106256263437150580115003)
                  ·
                    rfl

theorem cell20_232800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_232800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232800 prefixEnd_232800 := by exact prefixLift 232800
  have htrace : WordTrace (prefixWord ++ tailWord_232800) baseStart_232800 baseEnd_232800 := by
    simpa [prefixWord, tailWord_232800, baseEnd_232800] using wordTrace_append hprefix tailTrace_232800
  have hstable : (prefixWord ++ tailWord_232800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232800).length < 2 ^ (prefixWord ++ tailWord_232800).sum := by decide
  have hdescent : baseEnd_232800 < baseStart_232800 := by decide
  rcases family_descends (prefixWord ++ tailWord_232800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232810 : List Nat := [3, 1, 3, 3, 3, 1, 2, 4]
def baseStart_232810 : Nat := 118140960795 + 232810 * 2 ^ 59
def prefixEnd_232810 : Nat := 4983230072969 + 3 ^ 40 * 232810 * 2
def baseEnd_232810 : Nat := 35420275903211663260543

theorem tailTrace_232810 : CollatzResearch.WordTrace tailWord_232810 prefixEnd_232810 35420275903211663260543 := by
  unfold tailWord_232810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122819571644151406897971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5660852191051070418394589 2122819571644151406897971)
  ·
    refine ⟨3184229357466227110346957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2122819571644151406897971 3184229357466227110346957)
    ·
      refine ⟨1194086009049835166380109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3184229357466227110346957 1194086009049835166380109)
      ·
        refine ⟨447782253393688187392541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1194086009049835166380109 447782253393688187392541)
        ·
          refine ⟨167918345022633070272203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447782253393688187392541 167918345022633070272203)
          ·
            refine ⟨251877517533949605408305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167918345022633070272203 251877517533949605408305)
            ·
              refine ⟨188908138150462204056229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251877517533949605408305 188908138150462204056229)
              ·
                refine ⟨35420275903211663260543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188908138150462204056229 35420275903211663260543)
                ·
                  rfl

theorem cell20_232810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_232810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232810 prefixEnd_232810 := by exact prefixLift 232810
  have htrace : WordTrace (prefixWord ++ tailWord_232810) baseStart_232810 baseEnd_232810 := by
    simpa [prefixWord, tailWord_232810, baseEnd_232810] using wordTrace_append hprefix tailTrace_232810
  have hstable : (prefixWord ++ tailWord_232810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232810).length < 2 ^ (prefixWord ++ tailWord_232810).sum := by decide
  have hdescent : baseEnd_232810 < baseStart_232810 := by decide
  rcases family_descends (prefixWord ++ tailWord_232810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232835 : List Nat := [1, 1, 1, 3, 5, 3, 6]
def baseStart_232835 : Nat := 118140960795 + 232835 * 2 ^ 59
def prefixEnd_232835 : Nat := 4983230072969 + 3 ^ 40 * 232835 * 2
def baseEnd_232835 : Nat := 11808026487871779327577

theorem tailTrace_232835 : CollatzResearch.WordTrace tailWord_232835 prefixEnd_232835 11808026487871779327577 := by
  unfold tailWord_232835
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492190111486034897251959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5661460074324023264834639 8492190111486034897251959)
  ·
    refine ⟨12738285167229052345877939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8492190111486034897251959 12738285167229052345877939)
    ·
      refine ⟨19107427750843578518816909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12738285167229052345877939 19107427750843578518816909)
      ·
        refine ⟨7165285406566341944556341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19107427750843578518816909 7165285406566341944556341)
        ·
          refine ⟨671745506865594557302157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7165285406566341944556341 671745506865594557302157)
          ·
            refine ⟨251904565074597958988309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 671745506865594557302157 251904565074597958988309)
            ·
              refine ⟨11808026487871779327577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 251904565074597958988309 11808026487871779327577)
              ·
                rfl

theorem cell20_232835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 6].length) (baseStart_232835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232835 prefixEnd_232835 := by exact prefixLift 232835
  have htrace : WordTrace (prefixWord ++ tailWord_232835) baseStart_232835 baseEnd_232835 := by
    simpa [prefixWord, tailWord_232835, baseEnd_232835] using wordTrace_append hprefix tailTrace_232835
  have hstable : (prefixWord ++ tailWord_232835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232835).length < 2 ^ (prefixWord ++ tailWord_232835).sum := by decide
  have hdescent : baseEnd_232835 < baseStart_232835 := by decide
  rcases family_descends (prefixWord ++ tailWord_232835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232852 : List Nat := [2, 4, 2, 1, 2, 2, 2, 5]
def baseStart_232852 : Nat := 118140960795 + 232852 * 2 ^ 59
def prefixEnd_232852 : Nat := 4983230072969 + 3 ^ 40 * 232852 * 2
def baseEnd_232852 : Nat := 35426665884689836793819

theorem tailTrace_232852 : CollatzResearch.WordTrace tailWord_232852 prefixEnd_232852 35426665884689836793819 := by
  unfold tailWord_232852
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246405076212223400310405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5661873434949631200413873 4246405076212223400310405)
  ·
    refine ⟨796200951789791887558201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4246405076212223400310405 796200951789791887558201)
    ·
      refine ⟨597150713842343915668651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 796200951789791887558201 597150713842343915668651)
      ·
        refine ⟨895726070763515873502977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597150713842343915668651 895726070763515873502977)
        ·
          refine ⟨671794553072636905127233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895726070763515873502977 671794553072636905127233)
          ·
            refine ⟨503845914804477678845425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671794553072636905127233 503845914804477678845425)
            ·
              refine ⟨377884436103358259134069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503845914804477678845425 377884436103358259134069)
              ·
                refine ⟨35426665884689836793819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377884436103358259134069 35426665884689836793819)
                ·
                  rfl

theorem cell20_232852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_232852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232852 prefixEnd_232852 := by exact prefixLift 232852
  have htrace : WordTrace (prefixWord ++ tailWord_232852) baseStart_232852 baseEnd_232852 := by
    simpa [prefixWord, tailWord_232852, baseEnd_232852] using wordTrace_append hprefix tailTrace_232852
  have hstable : (prefixWord ++ tailWord_232852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232852).length < 2 ^ (prefixWord ++ tailWord_232852).sum := by decide
  have hdescent : baseEnd_232852 < baseStart_232852 := by decide
  rcases family_descends (prefixWord ++ tailWord_232852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232900 : List Nat := [2, 3, 3, 2, 1, 2, 1, 4, 2]
def baseStart_232900 : Nat := 118140960795 + 232900 * 2 ^ 59
def prefixEnd_232900 : Nat := 4983230072969 + 3 ^ 40 * 232900 * 2
def baseEnd_232900 : Nat := 106301906161994676781261

theorem tailTrace_232900 : CollatzResearch.WordTrace tailWord_232900 prefixEnd_232900 106301906161994676781261 := by
  unfold tailWord_232900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4247280428125275499184077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5663040570833700665578769 4247280428125275499184077)
  ·
    refine ⟨1592730160546978312194029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4247280428125275499184077 1592730160546978312194029)
    ·
      refine ⟨597273810205116867072761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1592730160546978312194029 597273810205116867072761)
      ·
        refine ⟨447955357653837650304571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597273810205116867072761 447955357653837650304571)
        ·
          refine ⟨671933036480756475456857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447955357653837650304571 671933036480756475456857)
          ·
            refine ⟨503949777360567356592643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671933036480756475456857 503949777360567356592643)
            ·
              refine ⟨755924666040851034888965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503949777360567356592643 755924666040851034888965)
              ·
                refine ⟨141735874882659569041681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 755924666040851034888965 141735874882659569041681)
                ·
                  refine ⟨106301906161994676781261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141735874882659569041681 106301906161994676781261)
                  ·
                    rfl

theorem cell20_232900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_232900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232900 prefixEnd_232900 := by exact prefixLift 232900
  have htrace : WordTrace (prefixWord ++ tailWord_232900) baseStart_232900 baseEnd_232900 := by
    simpa [prefixWord, tailWord_232900, baseEnd_232900] using wordTrace_append hprefix tailTrace_232900
  have hstable : (prefixWord ++ tailWord_232900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232900).length < 2 ^ (prefixWord ++ tailWord_232900).sum := by decide
  have hdescent : baseEnd_232900 < baseStart_232900 := by decide
  rcases family_descends (prefixWord ++ tailWord_232900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232932 : List Nat := [2, 3, 1, 1, 1, 1, 1, 10]
def baseStart_232932 : Nat := 118140960795 + 232932 * 2 ^ 59
def prefixEnd_232932 : Nat := 4983230072969 + 3 ^ 40 * 232932 * 2
def baseEnd_232932 : Nat := 35438837277981595904821

theorem tailTrace_232932 : CollatzResearch.WordTrace tailWord_232932 prefixEnd_232932 35438837277981595904821 := by
  unfold tailWord_232932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4247863996067310231766525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5663818661423080309022033 4247863996067310231766525)
  ·
    refine ⟨1592948998525241336912447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4247863996067310231766525 1592948998525241336912447)
    ·
      refine ⟨2389423497787862005368671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592948998525241336912447 2389423497787862005368671)
      ·
        refine ⟨3584135246681793008053007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389423497787862005368671 3584135246681793008053007)
        ·
          refine ⟨5376202870022689512079511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584135246681793008053007 5376202870022689512079511)
          ·
            refine ⟨8064304305034034268119267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376202870022689512079511 8064304305034034268119267)
            ·
              refine ⟨12096456457551051402178901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8064304305034034268119267 12096456457551051402178901)
              ·
                refine ⟨35438837277981595904821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12096456457551051402178901 35438837277981595904821)
                ·
                  rfl

theorem cell20_232932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_232932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232932 prefixEnd_232932 := by exact prefixLift 232932
  have htrace : WordTrace (prefixWord ++ tailWord_232932) baseStart_232932 baseEnd_232932 := by
    simpa [prefixWord, tailWord_232932, baseEnd_232932] using wordTrace_append hprefix tailTrace_232932
  have hstable : (prefixWord ++ tailWord_232932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232932).length < 2 ^ (prefixWord ++ tailWord_232932).sum := by decide
  have hdescent : baseEnd_232932 < baseStart_232932 := by decide
  rcases family_descends (prefixWord ++ tailWord_232932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232938 : List Nat := [3, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_232938 : Nat := 118140960795 + 232938 * 2 ^ 59
def prefixEnd_232938 : Nat := 4983230072969 + 3 ^ 40 * 232938 * 2
def baseEnd_232938 : Nat := 106319250397435433514439

theorem tailTrace_232938 : CollatzResearch.WordTrace tailWord_232938 prefixEnd_232938 106319250397435433514439 := by
  unfold tailWord_232938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123986707528220872062867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5663964553408588992167645 2123986707528220872062867)
  ·
    refine ⟨3185980061292331308094301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2123986707528220872062867 3185980061292331308094301)
    ·
      refine ⟨1194742522984624240535363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3185980061292331308094301 1194742522984624240535363)
      ·
        refine ⟨1792113784476936360803045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194742522984624240535363 1792113784476936360803045)
        ·
          refine ⟨336021334589425567650571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1792113784476936360803045 336021334589425567650571)
          ·
            refine ⟨504032001884138351475857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336021334589425567650571 504032001884138351475857)
            ·
              refine ⟨378024001413103763606893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504032001884138351475857 378024001413103763606893)
              ·
                refine ⟨141759000529913911352585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378024001413103763606893 141759000529913911352585)
                ·
                  refine ⟨106319250397435433514439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141759000529913911352585 106319250397435433514439)
                  ·
                    rfl

theorem cell20_232938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_232938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232938 prefixEnd_232938 := by exact prefixLift 232938
  have htrace : WordTrace (prefixWord ++ tailWord_232938) baseStart_232938 baseEnd_232938 := by
    simpa [prefixWord, tailWord_232938, baseEnd_232938] using wordTrace_append hprefix tailTrace_232938
  have hstable : (prefixWord ++ tailWord_232938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232938).length < 2 ^ (prefixWord ++ tailWord_232938).sum := by decide
  have hdescent : baseEnd_232938 < baseStart_232938 := by decide
  rcases family_descends (prefixWord ++ tailWord_232938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232994 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_232994 : Nat := 118140960795 + 232994 * 2 ^ 59
def prefixEnd_232994 : Nat := 4983230072969 + 3 ^ 40 * 232994 * 2
def baseEnd_232994 : Nat := 106344810323348127647543

theorem tailTrace_232994 : CollatzResearch.WordTrace tailWord_232994 prefixEnd_232994 106344810323348127647543 := by
  unfold tailWord_232994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124497329477501263072509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5665326211940003368193357 2124497329477501263072509)
  ·
    refine ⟨796686498554062973652191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2124497329477501263072509 796686498554062973652191)
    ·
      refine ⟨1195029747831094460478287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796686498554062973652191 1195029747831094460478287)
      ·
        refine ⟨1792544621746641690717431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195029747831094460478287 1792544621746641690717431)
        ·
          refine ⟨2688816932619962536076147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1792544621746641690717431 2688816932619962536076147)
          ·
            refine ⟨4033225398929943804114221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688816932619962536076147 4033225398929943804114221)
            ·
              refine ⟨1512459524598728926542833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4033225398929943804114221 1512459524598728926542833)
              ·
                refine ⟨1134344643449046694907125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512459524598728926542833 1134344643449046694907125)
                ·
                  refine ⟨106344810323348127647543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1134344643449046694907125 106344810323348127647543)
                  ·
                    rfl

theorem cell20_232994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_232994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_232994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_232994 prefixEnd_232994 := by exact prefixLift 232994
  have htrace : WordTrace (prefixWord ++ tailWord_232994) baseStart_232994 baseEnd_232994 := by
    simpa [prefixWord, tailWord_232994, baseEnd_232994] using wordTrace_append hprefix tailTrace_232994
  have hstable : (prefixWord ++ tailWord_232994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232994).length < 2 ^ (prefixWord ++ tailWord_232994).sum := by decide
  have hdescent : baseEnd_232994 < baseStart_232994 := by decide
  rcases family_descends (prefixWord ++ tailWord_232994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233014 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_233014 : Nat := 118140960795 + 233014 * 2 ^ 59
def prefixEnd_233014 : Nat := 4983230072969 + 3 ^ 40 * 233014 * 2
def baseEnd_233014 : Nat := 106353938868316946980795

theorem tailTrace_233014 : CollatzResearch.WordTrace tailWord_233014 prefixEnd_233014 106353938868316946980795 := by
  unfold tailWord_233014
  simp only [CollatzResearch.WordTrace]
  refine ⟨531169923614846779251131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5665812518558365645345397 531169923614846779251131)
  ·
    refine ⟨796754885422270168876697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 531169923614846779251131 796754885422270168876697)
    ·
      refine ⟨597566164066702626657523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 796754885422270168876697 597566164066702626657523)
      ·
        refine ⟨896349246100053939986285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597566164066702626657523 896349246100053939986285)
        ·
          refine ⟨336130967287520227494857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 896349246100053939986285 336130967287520227494857)
          ·
            refine ⟨252098225465640170621143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336130967287520227494857 252098225465640170621143)
            ·
              refine ⟨378147338198460255931715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252098225465640170621143 378147338198460255931715)
              ·
                refine ⟨567221007297690383897573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378147338198460255931715 567221007297690383897573)
                ·
                  refine ⟨106353938868316946980795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567221007297690383897573 106353938868316946980795)
                  ·
                    rfl

theorem cell20_233014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_233014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233014 prefixEnd_233014 := by exact prefixLift 233014
  have htrace : WordTrace (prefixWord ++ tailWord_233014) baseStart_233014 baseEnd_233014 := by
    simpa [prefixWord, tailWord_233014, baseEnd_233014] using wordTrace_append hprefix tailTrace_233014
  have hstable : (prefixWord ++ tailWord_233014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233014).length < 2 ^ (prefixWord ++ tailWord_233014).sum := by decide
  have hdescent : baseEnd_233014 < baseStart_233014 := by decide
  rcases family_descends (prefixWord ++ tailWord_233014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233025 : List Nat := [1, 2, 5, 1, 1, 1, 4, 5]
def baseStart_233025 : Nat := 118140960795 + 233025 * 2 ^ 59
def prefixEnd_233025 : Nat := 4983230072969 + 3 ^ 40 * 233025 * 2
def baseEnd_233025 : Nat := 35452986522683265871361

theorem tailTrace_233025 : CollatzResearch.WordTrace tailWord_233025 prefixEnd_233025 35452986522683265871361 := by
  unfold tailWord_233025
  simp only [CollatzResearch.WordTrace]
  refine ⟨8499119980797697346668529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5666079987198464897779019 8499119980797697346668529)
  ·
    refine ⟨6374339985598273010001397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8499119980797697346668529 6374339985598273010001397)
    ·
      refine ⟨597594373649838094687631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6374339985598273010001397 597594373649838094687631)
      ·
        refine ⟨896391560474757142031447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597594373649838094687631 896391560474757142031447)
        ·
          refine ⟨1344587340712135713047171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896391560474757142031447 1344587340712135713047171)
          ·
            refine ⟨2016881011068203569570757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344587340712135713047171 2016881011068203569570757)
            ·
              refine ⟨378165189575288169294517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2016881011068203569570757 378165189575288169294517)
              ·
                refine ⟨35452986522683265871361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 378165189575288169294517 35452986522683265871361)
                ·
                  rfl

theorem cell20_233025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_233025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233025 prefixEnd_233025 := by exact prefixLift 233025
  have htrace : WordTrace (prefixWord ++ tailWord_233025) baseStart_233025 baseEnd_233025 := by
    simpa [prefixWord, tailWord_233025, baseEnd_233025] using wordTrace_append hprefix tailTrace_233025
  have hstable : (prefixWord ++ tailWord_233025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233025).length < 2 ^ (prefixWord ++ tailWord_233025).sum := by decide
  have hdescent : baseEnd_233025 < baseStart_233025 := by decide
  rcases family_descends (prefixWord ++ tailWord_233025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233056 : List Nat := [2, 1, 1, 3, 2, 1, 1, 7, 2]
def baseStart_233056 : Nat := 118140960795 + 233056 * 2 ^ 59
def prefixEnd_233056 : Nat := 4983230072969 + 3 ^ 40 * 233056 * 2
def baseEnd_233056 : Nat := 106373108812751467580623

theorem tailTrace_233056 : CollatzResearch.WordTrace tailWord_233056 prefixEnd_233056 106373108812751467580623 := by
  unfold tailWord_233056
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250125321842694820523511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5666833762456926427364681 4250125321842694820523511)
  ·
    refine ⟨6375187982764042230785267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4250125321842694820523511 6375187982764042230785267)
    ·
      refine ⟨9562781974146063346177901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6375187982764042230785267 9562781974146063346177901)
      ·
        refine ⟨3586043240304773754816713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9562781974146063346177901 3586043240304773754816713)
        ·
          refine ⟨2689532430228580316112535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3586043240304773754816713 2689532430228580316112535)
          ·
            refine ⟨4034298645342870474168803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689532430228580316112535 4034298645342870474168803)
            ·
              refine ⟨6051447968014305711253205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034298645342870474168803 6051447968014305711253205)
              ·
                refine ⟨141830811750335290107497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6051447968014305711253205 141830811750335290107497)
                ·
                  refine ⟨106373108812751467580623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141830811750335290107497 106373108812751467580623)
                  ·
                    rfl

theorem cell20_233056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_233056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233056 prefixEnd_233056 := by exact prefixLift 233056
  have htrace : WordTrace (prefixWord ++ tailWord_233056) baseStart_233056 baseEnd_233056 := by
    simpa [prefixWord, tailWord_233056, baseEnd_233056] using wordTrace_append hprefix tailTrace_233056
  have hstable : (prefixWord ++ tailWord_233056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233056).length < 2 ^ (prefixWord ++ tailWord_233056).sum := by decide
  have hdescent : baseEnd_233056 < baseStart_233056 := by decide
  rcases family_descends (prefixWord ++ tailWord_233056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233069 : List Nat := [1, 5, 1, 1, 4, 2, 2, 2, 2]
def baseStart_233069 : Nat := 118140960795 + 233069 * 2 ^ 59
def prefixEnd_233069 : Nat := 4983230072969 + 3 ^ 40 * 233069 * 2
def baseEnd_233069 : Nat := 106379042366981200147237

theorem tailTrace_233069 : CollatzResearch.WordTrace tailWord_233069 prefixEnd_233069 106379042366981200147237 := by
  unfold tailWord_233069
  simp only [CollatzResearch.WordTrace]
  refine ⟨8500724792638292861270261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5667149861758861907513507 8500724792638292861270261)
  ·
    refine ⟨796942949309839955744087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8500724792638292861270261 796942949309839955744087)
    ·
      refine ⟨1195414423964759933616131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796942949309839955744087 1195414423964759933616131)
      ·
        refine ⟨1793121635947139900424197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195414423964759933616131 1793121635947139900424197)
        ·
          refine ⟨336210306740088731329537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1793121635947139900424197 336210306740088731329537)
          ·
            refine ⟨252157730055066548497153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336210306740088731329537 252157730055066548497153)
            ·
              refine ⟨189118297541299911372865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252157730055066548497153 189118297541299911372865)
              ·
                refine ⟨141838723155974933529649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189118297541299911372865 141838723155974933529649)
                ·
                  refine ⟨106379042366981200147237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141838723155974933529649 106379042366981200147237)
                  ·
                    rfl

theorem cell20_233069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_233069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233069 prefixEnd_233069 := by exact prefixLift 233069
  have htrace : WordTrace (prefixWord ++ tailWord_233069) baseStart_233069 baseEnd_233069 := by
    simpa [prefixWord, tailWord_233069, baseEnd_233069] using wordTrace_append hprefix tailTrace_233069
  have hstable : (prefixWord ++ tailWord_233069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233069).length < 2 ^ (prefixWord ++ tailWord_233069).sum := by decide
  have hdescent : baseEnd_233069 < baseStart_233069 := by decide
  rcases family_descends (prefixWord ++ tailWord_233069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233091 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_233091 : Nat := 118140960795 + 233091 * 2 ^ 59
def prefixEnd_233091 : Nat := 4983230072969 + 3 ^ 40 * 233091 * 2
def baseEnd_233091 : Nat := 106389083766446901413813

theorem tailTrace_233091 : CollatzResearch.WordTrace tailWord_233091 prefixEnd_233091 106389083766446901413813 := by
  unfold tailWord_233091
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501527198558590618571127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5667684799039060412380751 8501527198558590618571127)
  ·
    refine ⟨12752290797837885927856691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8501527198558590618571127 12752290797837885927856691)
    ·
      refine ⟨19128436196756828891785037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12752290797837885927856691 19128436196756828891785037)
      ·
        refine ⟨7173163573783810834419389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19128436196756828891785037 7173163573783810834419389)
        ·
          refine ⟨2689936340168929062907271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7173163573783810834419389 2689936340168929062907271)
          ·
            refine ⟨4034904510253393594360907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689936340168929062907271 4034904510253393594360907)
            ·
              refine ⟨6052356765380090391541361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034904510253393594360907 6052356765380090391541361)
              ·
                refine ⟨4539267574035067793656021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052356765380090391541361 4539267574035067793656021)
                ·
                  refine ⟨106389083766446901413813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4539267574035067793656021 106389083766446901413813)
                  ·
                    rfl

theorem cell20_233091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_233091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233091 prefixEnd_233091 := by exact prefixLift 233091
  have htrace : WordTrace (prefixWord ++ tailWord_233091) baseStart_233091 baseEnd_233091 := by
    simpa [prefixWord, tailWord_233091, baseEnd_233091] using wordTrace_append hprefix tailTrace_233091
  have hstable : (prefixWord ++ tailWord_233091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233091).length < 2 ^ (prefixWord ++ tailWord_233091).sum := by decide
  have hdescent : baseEnd_233091 < baseStart_233091 := by decide
  rcases family_descends (prefixWord ++ tailWord_233091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233111 : List Nat := [1, 1, 3, 3, 2, 3, 2, 3, 2]
def baseStart_233111 : Nat := 118140960795 + 233111 * 2 ^ 59
def prefixEnd_233111 : Nat := 4983230072969 + 3 ^ 40 * 233111 * 2
def baseEnd_233111 : Nat := 106398212311415720747065

theorem tailTrace_233111 : CollatzResearch.WordTrace tailWord_233111 prefixEnd_233111 106398212311415720747065 := by
  unfold tailWord_233111
  simp only [CollatzResearch.WordTrace]
  refine ⟨8502256658486134034299187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5668171105657422689532791 8502256658486134034299187)
  ·
    refine ⟨12753384987729201051448781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8502256658486134034299187 12753384987729201051448781)
    ·
      refine ⟨4782519370398450394293293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12753384987729201051448781 4782519370398450394293293)
      ·
        refine ⟨1793444763899418897859985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4782519370398450394293293 1793444763899418897859985)
        ·
          refine ⟨1345083572924564173394989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1793444763899418897859985 1345083572924564173394989)
          ·
            refine ⟨504406339846711565023121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1345083572924564173394989 504406339846711565023121)
            ·
              refine ⟨378304754885033673767341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504406339846711565023121 378304754885033673767341)
              ·
                refine ⟨141864283081887627662753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378304754885033673767341 141864283081887627662753)
                ·
                  refine ⟨106398212311415720747065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141864283081887627662753 106398212311415720747065)
                  ·
                    rfl

theorem cell20_233111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 2].length) (baseStart_233111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233111 prefixEnd_233111 := by exact prefixLift 233111
  have htrace : WordTrace (prefixWord ++ tailWord_233111) baseStart_233111 baseEnd_233111 := by
    simpa [prefixWord, tailWord_233111, baseEnd_233111] using wordTrace_append hprefix tailTrace_233111
  have hstable : (prefixWord ++ tailWord_233111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233111).length < 2 ^ (prefixWord ++ tailWord_233111).sum := by decide
  have hdescent : baseEnd_233111 < baseStart_233111 := by decide
  rcases family_descends (prefixWord ++ tailWord_233111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233160 : List Nat := [2, 1, 3, 1, 2, 2, 3, 6]
def baseStart_233160 : Nat := 118140960795 + 233160 * 2 ^ 59
def prefixEnd_233160 : Nat := 4983230072969 + 3 ^ 40 * 233160 * 2
def baseEnd_233160 : Nat := 35473525748863109371177

theorem tailTrace_233160 : CollatzResearch.WordTrace tailWord_233160 prefixEnd_233160 35473525748863109371177 := by
  unfold tailWord_233160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4252021917654307701416467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5669362556872410268555289 4252021917654307701416467)
  ·
    refine ⟨6378032876481461552124701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4252021917654307701416467 6378032876481461552124701)
    ·
      refine ⟨2391762328680548082046763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6378032876481461552124701 2391762328680548082046763)
      ·
        refine ⟨3587643493020822123070145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391762328680548082046763 3587643493020822123070145)
        ·
          refine ⟨2690732619765616592302609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3587643493020822123070145 2690732619765616592302609)
          ·
            refine ⟨2018049464824212444226957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2690732619765616592302609 2018049464824212444226957)
            ·
              refine ⟨756768549309079666585109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2018049464824212444226957 756768549309079666585109)
              ·
                refine ⟨35473525748863109371177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 756768549309079666585109 35473525748863109371177)
                ·
                  rfl

theorem cell20_233160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_233160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233160 prefixEnd_233160 := by exact prefixLift 233160
  have htrace : WordTrace (prefixWord ++ tailWord_233160) baseStart_233160 baseEnd_233160 := by
    simpa [prefixWord, tailWord_233160, baseEnd_233160] using wordTrace_append hprefix tailTrace_233160
  have hstable : (prefixWord ++ tailWord_233160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233160).length < 2 ^ (prefixWord ++ tailWord_233160).sum := by decide
  have hdescent : baseEnd_233160 < baseStart_233160 := by decide
  rcases family_descends (prefixWord ++ tailWord_233160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233187 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 4]
def baseStart_233187 : Nat := 118140960795 + 233187 * 2 ^ 59
def prefixEnd_233187 : Nat := 4983230072969 + 3 ^ 40 * 233187 * 2
def baseEnd_233187 : Nat := 106432900782297234213421

theorem tailTrace_233187 : CollatzResearch.WordTrace tailWord_233187 prefixEnd_233187 106432900782297234213421 := by
  unfold tailWord_233187
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505028606210799014065815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5670019070807199342710543 8505028606210799014065815)
  ·
    refine ⟨12757542909316198521098723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8505028606210799014065815 12757542909316198521098723)
    ·
      refine ⟨19136314363974297781648085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757542909316198521098723 19136314363974297781648085)
      ·
        refine ⟨448507367905647604257377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19136314363974297781648085 448507367905647604257377)
        ·
          refine ⟨336380525929235703193033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448507367905647604257377 336380525929235703193033)
          ·
            refine ⟨252285394446926777394775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336380525929235703193033 252285394446926777394775)
            ·
              refine ⟨378428091670390166092163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252285394446926777394775 378428091670390166092163)
              ·
                refine ⟨567642137505585249138245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378428091670390166092163 567642137505585249138245)
                ·
                  refine ⟨106432900782297234213421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567642137505585249138245 106432900782297234213421)
                  ·
                    rfl

theorem cell20_233187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 4].length) (baseStart_233187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233187 prefixEnd_233187 := by exact prefixLift 233187
  have htrace : WordTrace (prefixWord ++ tailWord_233187) baseStart_233187 baseEnd_233187 := by
    simpa [prefixWord, tailWord_233187, baseEnd_233187] using wordTrace_append hprefix tailTrace_233187
  have hstable : (prefixWord ++ tailWord_233187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233187).length < 2 ^ (prefixWord ++ tailWord_233187).sum := by decide
  have hdescent : baseEnd_233187 < baseStart_233187 := by decide
  rcases family_descends (prefixWord ++ tailWord_233187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233201 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 3]
def baseStart_233201 : Nat := 118140960795 + 233201 * 2 ^ 59
def prefixEnd_233201 : Nat := 4983230072969 + 3 ^ 40 * 233201 * 2
def baseEnd_233201 : Nat := 106439290763775407746697

theorem tailTrace_233201 : CollatzResearch.WordTrace tailWord_233201 prefixEnd_233201 106439290763775407746697 := by
  unfold tailWord_233201
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505539228160079405075457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5670359485440052936716971 8505539228160079405075457)
  ·
    refine ⟨6379154421120059553806593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8505539228160079405075457 6379154421120059553806593)
    ·
      refine ⟨4784365815840044665354945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6379154421120059553806593 4784365815840044665354945)
      ·
        refine ⟨3588274361880033499016209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4784365815840044665354945 3588274361880033499016209)
        ·
          refine ⟨2691205771410025124262157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588274361880033499016209 2691205771410025124262157)
          ·
            refine ⟨1009202164278759421598309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2691205771410025124262157 1009202164278759421598309)
            ·
              refine ⟨189225405802267391549683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1009202164278759421598309 189225405802267391549683)
              ·
                refine ⟨283838108703401087324525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189225405802267391549683 283838108703401087324525)
                ·
                  refine ⟨106439290763775407746697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283838108703401087324525 106439290763775407746697)
                  ·
                    rfl

theorem cell20_233201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_233201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233201 prefixEnd_233201 := by exact prefixLift 233201
  have htrace : WordTrace (prefixWord ++ tailWord_233201) baseStart_233201 baseEnd_233201 := by
    simpa [prefixWord, tailWord_233201, baseEnd_233201] using wordTrace_append hprefix tailTrace_233201
  have hstable : (prefixWord ++ tailWord_233201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233201).length < 2 ^ (prefixWord ++ tailWord_233201).sum := by decide
  have hdescent : baseEnd_233201 < baseStart_233201 := by decide
  rcases family_descends (prefixWord ++ tailWord_233201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233239 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 3]
def baseStart_233239 : Nat := 118140960795 + 233239 * 2 ^ 59
def prefixEnd_233239 : Nat := 4983230072969 + 3 ^ 40 * 233239 * 2
def baseEnd_233239 : Nat := 106456634999216164479875

theorem tailTrace_233239 : CollatzResearch.WordTrace tailWord_233239 prefixEnd_233239 106456634999216164479875 := by
  unfold tailWord_233239
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506925202022411894958771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5671283468014941263305847 8506925202022411894958771)
  ·
    refine ⟨12760387803033617842438157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8506925202022411894958771 12760387803033617842438157)
    ·
      refine ⟨4785145426137606690914309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12760387803033617842438157 4785145426137606690914309)
      ·
        refine ⟨897214767400801254546433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4785145426137606690914309 897214767400801254546433)
        ·
          refine ⟨672911075550600940909825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897214767400801254546433 672911075550600940909825)
          ·
            refine ⟨504683306662950705682369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672911075550600940909825 504683306662950705682369)
            ·
              refine ⟨378512479997213029261777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504683306662950705682369 378512479997213029261777)
              ·
                refine ⟨283884359997909771946333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378512479997213029261777 283884359997909771946333)
                ·
                  refine ⟨106456634999216164479875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283884359997909771946333 106456634999216164479875)
                  ·
                    rfl

theorem cell20_233239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_233239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233239 prefixEnd_233239 := by exact prefixLift 233239
  have htrace : WordTrace (prefixWord ++ tailWord_233239) baseStart_233239 baseEnd_233239 := by
    simpa [prefixWord, tailWord_233239, baseEnd_233239] using wordTrace_append hprefix tailTrace_233239
  have hstable : (prefixWord ++ tailWord_233239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233239).length < 2 ^ (prefixWord ++ tailWord_233239).sum := by decide
  have hdescent : baseEnd_233239 < baseStart_233239 := by decide
  rcases family_descends (prefixWord ++ tailWord_233239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233242 : List Nat := [3, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_233242 : Nat := 118140960795 + 233242 * 2 ^ 59
def prefixEnd_233242 : Nat := 4983230072969 + 3 ^ 40 * 233242 * 2
def baseEnd_233242 : Nat := 106458004280961487379863

theorem tailTrace_233242 : CollatzResearch.WordTrace tailWord_233242 prefixEnd_233242 106458004280961487379863 := by
  unfold tailWord_233242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126758655252885851829495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5671356414007695604878653 2126758655252885851829495)
  ·
    refine ⟨3190137982879328777744243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2126758655252885851829495 3190137982879328777744243)
    ·
      refine ⟨4785206974318993166616365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190137982879328777744243 4785206974318993166616365)
      ·
        refine ⟨1794452615369622437481137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4785206974318993166616365 1794452615369622437481137)
        ·
          refine ⟨1345839461527216828110853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1794452615369622437481137 1345839461527216828110853)
          ·
            refine ⟨252344899036353155270785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1345839461527216828110853 252344899036353155270785)
            ·
              refine ⟨189258674277264866453089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252344899036353155270785 189258674277264866453089)
              ·
                refine ⟨141944005707948649839817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189258674277264866453089 141944005707948649839817)
                ·
                  refine ⟨106458004280961487379863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141944005707948649839817 106458004280961487379863)
                  ·
                    rfl

theorem cell20_233242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_233242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233242 prefixEnd_233242 := by exact prefixLift 233242
  have htrace : WordTrace (prefixWord ++ tailWord_233242) baseStart_233242 baseEnd_233242 := by
    simpa [prefixWord, tailWord_233242, baseEnd_233242] using wordTrace_append hprefix tailTrace_233242
  have hstable : (prefixWord ++ tailWord_233242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233242).length < 2 ^ (prefixWord ++ tailWord_233242).sum := by decide
  have hdescent : baseEnd_233242 < baseStart_233242 := by decide
  rcases family_descends (prefixWord ++ tailWord_233242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233253 : List Nat := [1, 3, 1, 2, 3, 4, 1, 5]
def baseStart_233253 : Nat := 118140960795 + 233253 * 2 ^ 59
def prefixEnd_233253 : Nat := 4983230072969 + 3 ^ 40 * 233253 * 2
def baseEnd_233253 : Nat := 35487674993564779337717

theorem tailTrace_233253 : CollatzResearch.WordTrace tailWord_233253 prefixEnd_233253 35487674993564779337717 := by
  unfold tailWord_233253
  simp only [CollatzResearch.WordTrace]
  refine ⟨8507435823971692285968413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5671623882647794857312275 8507435823971692285968413)
  ·
    refine ⟨3190288433989384607238155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8507435823971692285968413 3190288433989384607238155)
    ·
      refine ⟨4785432650984076910857233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190288433989384607238155 4785432650984076910857233)
      ·
        refine ⟨3589074488238057683142925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785432650984076910857233 3589074488238057683142925)
        ·
          refine ⟨1345902933089271631178597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3589074488238057683142925 1345902933089271631178597)
          ·
            refine ⟨252356799954238430845987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1345902933089271631178597 252356799954238430845987)
            ·
              refine ⟨378535199931357646268981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252356799954238430845987 378535199931357646268981)
              ·
                refine ⟨35487674993564779337717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 378535199931357646268981 35487674993564779337717)
                ·
                  rfl

theorem cell20_233253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_233253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233253 prefixEnd_233253 := by exact prefixLift 233253
  have htrace : WordTrace (prefixWord ++ tailWord_233253) baseStart_233253 baseEnd_233253 := by
    simpa [prefixWord, tailWord_233253, baseEnd_233253] using wordTrace_append hprefix tailTrace_233253
  have hstable : (prefixWord ++ tailWord_233253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233253).length < 2 ^ (prefixWord ++ tailWord_233253).sum := by decide
  have hdescent : baseEnd_233253 < baseStart_233253 := by decide
  rcases family_descends (prefixWord ++ tailWord_233253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233260 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_233260 : Nat := 118140960795 + 233260 * 2 ^ 59
def prefixEnd_233260 : Nat := 4983230072969 + 3 ^ 40 * 233260 * 2
def baseEnd_233260 : Nat := 106466219971433424779789

theorem tailTrace_233260 : CollatzResearch.WordTrace tailWord_233260 prefixEnd_233260 106466219971433424779789 := by
  unfold tailWord_233260
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253845567473166240736617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5671794089964221654315489 4253845567473166240736617)
  ·
    refine ⟨3190384175604874680552463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4253845567473166240736617 3190384175604874680552463)
    ·
      refine ⟨4785576263407312020828695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190384175604874680552463 4785576263407312020828695)
      ·
        refine ⟨7178364395110968031243043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785576263407312020828695 7178364395110968031243043)
        ·
          refine ⟨10767546592666452046864565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7178364395110968031243043 10767546592666452046864565)
          ·
            refine ⟨1009457493062479879393553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10767546592666452046864565 1009457493062479879393553)
            ·
              refine ⟨757093119796859909545165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009457493062479879393553 757093119796859909545165)
              ·
                refine ⟨283909919923822466079437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757093119796859909545165 283909919923822466079437)
                ·
                  refine ⟨106466219971433424779789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283909919923822466079437 106466219971433424779789)
                  ·
                    rfl

theorem cell20_233260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_233260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233260 prefixEnd_233260 := by exact prefixLift 233260
  have htrace : WordTrace (prefixWord ++ tailWord_233260) baseStart_233260 baseEnd_233260 := by
    simpa [prefixWord, tailWord_233260, baseEnd_233260] using wordTrace_append hprefix tailTrace_233260
  have hstable : (prefixWord ++ tailWord_233260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233260).length < 2 ^ (prefixWord ++ tailWord_233260).sum := by decide
  have hdescent : baseEnd_233260 < baseStart_233260 := by decide
  rcases family_descends (prefixWord ++ tailWord_233260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233298 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_233298 : Nat := 118140960795 + 233298 * 2 ^ 59
def prefixEnd_233298 : Nat := 4983230072969 + 3 ^ 40 * 233298 * 2
def baseEnd_233298 : Nat := 106483564206874181512967

theorem tailTrace_233298 : CollatzResearch.WordTrace tailWord_233298 prefixEnd_233298 106483564206874181512967 := by
  unfold tailWord_233298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127269277202166242839137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5672718072539109980904365 2127269277202166242839137)
  ·
    refine ⟨1595451957901624682129353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2127269277202166242839137 1595451957901624682129353)
    ·
      refine ⟨1196588968426218511597015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1595451957901624682129353 1196588968426218511597015)
      ·
        refine ⟨1794883452639327767395523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196588968426218511597015 1794883452639327767395523)
        ·
          refine ⟨2692325178958991651093285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794883452639327767395523 2692325178958991651093285)
          ·
            refine ⟨504810971054810934579991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2692325178958991651093285 504810971054810934579991)
            ·
              refine ⟨757216456582216401869987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504810971054810934579991 757216456582216401869987)
              ·
                refine ⟨1135824684873324602804981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757216456582216401869987 1135824684873324602804981)
                ·
                  refine ⟨106483564206874181512967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1135824684873324602804981 106483564206874181512967)
                  ·
                    rfl

theorem cell20_233298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_233298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233298 prefixEnd_233298 := by exact prefixLift 233298
  have htrace : WordTrace (prefixWord ++ tailWord_233298) baseStart_233298 baseEnd_233298 := by
    simpa [prefixWord, tailWord_233298, baseEnd_233298] using wordTrace_append hprefix tailTrace_233298
  have hstable : (prefixWord ++ tailWord_233298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233298).length < 2 ^ (prefixWord ++ tailWord_233298).sum := by decide
  have hdescent : baseEnd_233298 < baseStart_233298 := by decide
  rcases family_descends (prefixWord ++ tailWord_233298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233305 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_233305 : Nat := 118140960795 + 233305 * 2 ^ 59
def prefixEnd_233305 : Nat := 4983230072969 + 3 ^ 40 * 233305 * 2
def baseEnd_233305 : Nat := 106486759197613268279605

theorem tailTrace_233305 : CollatzResearch.WordTrace tailWord_233305 prefixEnd_233305 106486759197613268279605 := by
  unfold tailWord_233305
  simp only [CollatzResearch.WordTrace]
  refine ⟨8509332419783305166861369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5672888279855536777907579 8509332419783305166861369)
  ·
    refine ⟨6381999314837478875146027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8509332419783305166861369 6381999314837478875146027)
    ·
      refine ⟨9572998972256218312719041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6381999314837478875146027 9572998972256218312719041)
      ·
        refine ⟨7179749229192163734539281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9572998972256218312719041 7179749229192163734539281)
        ·
          refine ⟨5384811921894122800904461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7179749229192163734539281 5384811921894122800904461)
          ·
            refine ⟨2019304470710296050339173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5384811921894122800904461 2019304470710296050339173)
            ·
              refine ⟨378619588258180509438595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2019304470710296050339173 378619588258180509438595)
              ·
                refine ⟨567929382387270764157893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378619588258180509438595 567929382387270764157893)
                ·
                  refine ⟨106486759197613268279605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 567929382387270764157893 106486759197613268279605)
                  ·
                    rfl

theorem cell20_233305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_233305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233305 prefixEnd_233305 := by exact prefixLift 233305
  have htrace : WordTrace (prefixWord ++ tailWord_233305) baseStart_233305 baseEnd_233305 := by
    simpa [prefixWord, tailWord_233305, baseEnd_233305] using wordTrace_append hprefix tailTrace_233305
  have hstable : (prefixWord ++ tailWord_233305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233305).length < 2 ^ (prefixWord ++ tailWord_233305).sum := by decide
  have hdescent : baseEnd_233305 < baseStart_233305 := by decide
  rcases family_descends (prefixWord ++ tailWord_233305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233370 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_233370 : Nat := 118140960795 + 233370 * 2 ^ 59
def prefixEnd_233370 : Nat := 4983230072969 + 3 ^ 40 * 233370 * 2
def baseEnd_233370 : Nat := 106516426968761931112673

theorem tailTrace_233370 : CollatzResearch.WordTrace tailWord_233370 prefixEnd_233370 106516426968761931112673 := by
  unfold tailWord_233370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127925791136955316994391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5674468776365214178651709 2127925791136955316994391)
  ·
    refine ⟨3191888686705432975491587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2127925791136955316994391 3191888686705432975491587)
    ·
      refine ⟨4787833030058149463237381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191888686705432975491587 4787833030058149463237381)
      ·
        refine ⟨897718693135903024357009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4787833030058149463237381 897718693135903024357009)
        ·
          refine ⟨673289019851927268267757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897718693135903024357009 673289019851927268267757)
          ·
            refine ⟨252483382444472725600409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673289019851927268267757 252483382444472725600409)
            ·
              refine ⟨189362536833354544200307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252483382444472725600409 189362536833354544200307)
              ·
                refine ⟨284043805250031816300461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189362536833354544200307 284043805250031816300461)
                ·
                  refine ⟨106516426968761931112673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284043805250031816300461 106516426968761931112673)
                  ·
                    rfl

theorem cell20_233370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_233370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233370 prefixEnd_233370 := by exact prefixLift 233370
  have htrace : WordTrace (prefixWord ++ tailWord_233370) baseStart_233370 baseEnd_233370 := by
    simpa [prefixWord, tailWord_233370, baseEnd_233370] using wordTrace_append hprefix tailTrace_233370
  have hstable : (prefixWord ++ tailWord_233370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233370).length < 2 ^ (prefixWord ++ tailWord_233370).sum := by decide
  have hdescent : baseEnd_233370 < baseStart_233370 := by decide
  rcases family_descends (prefixWord ++ tailWord_233370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233402 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_233402 : Nat := 118140960795 + 233402 * 2 ^ 59
def prefixEnd_233402 : Nat := 4983230072969 + 3 ^ 40 * 233402 * 2
def baseEnd_233402 : Nat := 106531032640712042045875

theorem tailTrace_233402 : CollatzResearch.WordTrace tailWord_233402 prefixEnd_233402 106531032640712042045875 := by
  unfold tailWord_233402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2128217575107972683285615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5675246866954593822094973 2128217575107972683285615)
  ·
    refine ⟨3192326362661959024928423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2128217575107972683285615 3192326362661959024928423)
    ·
      refine ⟨4788489543992938537392635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192326362661959024928423 4788489543992938537392635)
      ·
        refine ⟨7182734315989407806088953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4788489543992938537392635 7182734315989407806088953)
        ·
          refine ⟨5387050736992055854566715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7182734315989407806088953 5387050736992055854566715)
          ·
            refine ⟨8080576105488083781850073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387050736992055854566715 8080576105488083781850073)
            ·
              refine ⟨6060432079116062836387555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8080576105488083781850073 6060432079116062836387555)
              ·
                refine ⟨9090648118674094254581333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060432079116062836387555 9090648118674094254581333)
                ·
                  refine ⟨106531032640712042045875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9090648118674094254581333 106531032640712042045875)
                  ·
                    rfl

theorem cell20_233402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_233402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233402 prefixEnd_233402 := by exact prefixLift 233402
  have htrace : WordTrace (prefixWord ++ tailWord_233402) baseStart_233402 baseEnd_233402 := by
    simpa [prefixWord, tailWord_233402, baseEnd_233402] using wordTrace_append hprefix tailTrace_233402
  have hstable : (prefixWord ++ tailWord_233402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233402).length < 2 ^ (prefixWord ++ tailWord_233402).sum := by decide
  have hdescent : baseEnd_233402 < baseStart_233402 := by decide
  rcases family_descends (prefixWord ++ tailWord_233402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233409 : List Nat := [1, 2, 17]
def baseStart_233409 : Nat := 118140960795 + 233409 * 2 ^ 59
def prefixEnd_233409 : Nat := 4983230072969 + 3 ^ 40 * 233409 * 2
def baseEnd_233409 : Nat := 146137486462895924297

theorem tailTrace_233409 : CollatzResearch.WordTrace tailWord_233409 prefixEnd_233409 146137486462895924297 := by
  unfold tailWord_233409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8513125611406530928647281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5675417074271020619098187 8513125611406530928647281)
  ·
    refine ⟨6384844208554898196485461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8513125611406530928647281 6384844208554898196485461)
    ·
      refine ⟨146137486462895924297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 6384844208554898196485461 146137486462895924297)
      ·
        rfl

theorem cell20_233409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 17].length) (baseStart_233409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233409 prefixEnd_233409 := by exact prefixLift 233409
  have htrace : WordTrace (prefixWord ++ tailWord_233409) baseStart_233409 baseEnd_233409 := by
    simpa [prefixWord, tailWord_233409, baseEnd_233409] using wordTrace_append hprefix tailTrace_233409
  have hstable : (prefixWord ++ tailWord_233409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233409).length < 2 ^ (prefixWord ++ tailWord_233409).sum := by decide
  have hdescent : baseEnd_233409 < baseStart_233409 := by decide
  rcases family_descends (prefixWord ++ tailWord_233409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233443 : List Nat := [1, 1, 1, 6, 1, 3, 3, 4]
def baseStart_233443 : Nat := 118140960795 + 233443 * 2 ^ 59
def prefixEnd_233443 : Nat := 4983230072969 + 3 ^ 40 * 233443 * 2
def baseEnd_233443 : Nat := 35516582052632707226347

theorem tailTrace_233443 : CollatzResearch.WordTrace tailWord_233443 prefixEnd_233443 35516582052632707226347 := by
  unfold tailWord_233443
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514365693283354735384983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5676243795522236490256655 8514365693283354735384983)
  ·
    refine ⟨12771548539925032103077475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8514365693283354735384983 12771548539925032103077475)
    ·
      refine ⟨19157322809887548154616213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12771548539925032103077475 19157322809887548154616213)
      ·
        refine ⟨897999506713478819747635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19157322809887548154616213 897999506713478819747635)
        ·
          refine ⟨1346999260070218229621453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897999506713478819747635 1346999260070218229621453)
          ·
            refine ⟨505124722526331836108045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1346999260070218229621453 505124722526331836108045)
            ·
              refine ⟨189421770947374438540517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505124722526331836108045 189421770947374438540517)
              ·
                refine ⟨35516582052632707226347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189421770947374438540517 35516582052632707226347)
                ·
                  rfl

theorem cell20_233443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 4].length) (baseStart_233443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233443 prefixEnd_233443 := by exact prefixLift 233443
  have htrace : WordTrace (prefixWord ++ tailWord_233443) baseStart_233443 baseEnd_233443 := by
    simpa [prefixWord, tailWord_233443, baseEnd_233443] using wordTrace_append hprefix tailTrace_233443
  have hstable : (prefixWord ++ tailWord_233443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233443).length < 2 ^ (prefixWord ++ tailWord_233443).sum := by decide
  have hdescent : baseEnd_233443 < baseStart_233443 := by decide
  rcases family_descends (prefixWord ++ tailWord_233443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233508 : List Nat := [2, 3, 1, 4, 2, 2, 1, 3, 2]
def baseStart_233508 : Nat := 118140960795 + 233508 * 2 ^ 59
def prefixEnd_233508 : Nat := 4983230072969 + 3 ^ 40 * 233508 * 2
def baseEnd_233508 : Nat := 106579413929046784512109

theorem tailTrace_233508 : CollatzResearch.WordTrace tailWord_233508 prefixEnd_233508 106579413929046784512109 := by
  unfold tailWord_233508
  simp only [CollatzResearch.WordTrace]
  refine ⟨4258368219023935418250589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5677824292031913891000785 4258368219023935418250589)
  ·
    refine ⟨1596888082133975781843971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4258368219023935418250589 1596888082133975781843971)
    ·
      refine ⟨2395332123200963672765957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1596888082133975781843971 2395332123200963672765957)
      ·
        refine ⟨449124773100180688643617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2395332123200963672765957 449124773100180688643617)
        ·
          refine ⟨336843579825135516482713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449124773100180688643617 336843579825135516482713)
          ·
            refine ⟨252632684868851637362035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336843579825135516482713 252632684868851637362035)
            ·
              refine ⟨378949027303277456043053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252632684868851637362035 378949027303277456043053)
              ·
                refine ⟨142105885238729046016145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378949027303277456043053 142105885238729046016145)
                ·
                  refine ⟨106579413929046784512109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142105885238729046016145 106579413929046784512109)
                  ·
                    rfl

theorem cell20_233508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_233508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233508 prefixEnd_233508 := by exact prefixLift 233508
  have htrace : WordTrace (prefixWord ++ tailWord_233508) baseStart_233508 baseEnd_233508 := by
    simpa [prefixWord, tailWord_233508, baseEnd_233508] using wordTrace_append hprefix tailTrace_233508
  have hstable : (prefixWord ++ tailWord_233508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233508).length < 2 ^ (prefixWord ++ tailWord_233508).sum := by decide
  have hdescent : baseEnd_233508 < baseStart_233508 := by decide
  rcases family_descends (prefixWord ++ tailWord_233508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233509 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_233509 : Nat := 118140960795 + 233509 * 2 ^ 59
def prefixEnd_233509 : Nat := 4983230072969 + 3 ^ 40 * 233509 * 2
def baseEnd_233509 : Nat := 106579870356295225478771

theorem tailTrace_233509 : CollatzResearch.WordTrace tailWord_233509 prefixEnd_233509 106579870356295225478771 := by
  unfold tailWord_233509
  simp only [CollatzResearch.WordTrace]
  refine ⟨8516772911044248007287581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5677848607362832004858387 8516772911044248007287581)
  ·
    refine ⟨3193789841641593002732843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8516772911044248007287581 3193789841641593002732843)
    ·
      refine ⟨4790684762462389504099265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3193789841641593002732843 4790684762462389504099265)
      ·
        refine ⟨3593013571846792128074449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4790684762462389504099265 3593013571846792128074449)
        ·
          refine ⟨2694760178885094096055837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3593013571846792128074449 2694760178885094096055837)
          ·
            refine ⟨1010535067081910286020939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2694760178885094096055837 1010535067081910286020939)
            ·
              refine ⟨1515802600622865429031409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010535067081910286020939 1515802600622865429031409)
              ·
                refine ⟨1136851950467149071773557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515802600622865429031409 1136851950467149071773557)
                ·
                  refine ⟨106579870356295225478771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1136851950467149071773557 106579870356295225478771)
                  ·
                    rfl

theorem cell20_233509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_233509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233509 prefixEnd_233509 := by exact prefixLift 233509
  have htrace : WordTrace (prefixWord ++ tailWord_233509) baseStart_233509 baseEnd_233509 := by
    simpa [prefixWord, tailWord_233509, baseEnd_233509] using wordTrace_append hprefix tailTrace_233509
  have hstable : (prefixWord ++ tailWord_233509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233509).length < 2 ^ (prefixWord ++ tailWord_233509).sum := by decide
  have hdescent : baseEnd_233509 < baseStart_233509 := by decide
  rcases family_descends (prefixWord ++ tailWord_233509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233523 : List Nat := [1, 1, 1, 2, 4, 1, 10]
def baseStart_233523 : Nat := 118140960795 + 233523 * 2 ^ 59
def prefixEnd_233523 : Nat := 4983230072969 + 3 ^ 40 * 233523 * 2
def baseEnd_233523 : Nat := 11842917815308155445783

theorem tailTrace_233523 : CollatzResearch.WordTrace tailWord_233523 prefixEnd_233523 11842917815308155445783 := by
  unfold tailWord_233523
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517283532993528398297223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5678189021995685598864815 8517283532993528398297223)
  ·
    refine ⟨12775925299490292597445835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8517283532993528398297223 12775925299490292597445835)
    ·
      refine ⟨19163887949235438896168753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12775925299490292597445835 19163887949235438896168753)
      ·
        refine ⟨14372915961926579172126565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19163887949235438896168753 14372915961926579172126565)
        ·
          refine ⟨2694921742861233594773731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14372915961926579172126565 2694921742861233594773731)
          ·
            refine ⟨4042382614291850392160597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694921742861233594773731 4042382614291850392160597)
            ·
              refine ⟨11842917815308155445783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4042382614291850392160597 11842917815308155445783)
              ·
                rfl

theorem cell20_233523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 10].length) (baseStart_233523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233523 prefixEnd_233523 := by exact prefixLift 233523
  have htrace : WordTrace (prefixWord ++ tailWord_233523) baseStart_233523 baseEnd_233523 := by
    simpa [prefixWord, tailWord_233523, baseEnd_233523] using wordTrace_append hprefix tailTrace_233523
  have hstable : (prefixWord ++ tailWord_233523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233523).length < 2 ^ (prefixWord ++ tailWord_233523).sum := by decide
  have hdescent : baseEnd_233523 < baseStart_233523 := by decide
  rcases family_descends (prefixWord ++ tailWord_233523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233526 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_233526 : Nat := 118140960795 + 233526 * 2 ^ 59
def prefixEnd_233526 : Nat := 4983230072969 + 3 ^ 40 * 233526 * 2
def baseEnd_233526 : Nat := 106587629619518721912035

theorem tailTrace_233526 : CollatzResearch.WordTrace tailWord_233526 prefixEnd_233526 106587629619518721912035 := by
  unfold tailWord_233526
  simp only [CollatzResearch.WordTrace]
  refine ⟨532337059498916244416027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5678261967988439940437621 532337059498916244416027)
  ·
    refine ⟨798505589248374366624041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 532337059498916244416027 798505589248374366624041)
    ·
      refine ⟨598879191936280774968031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798505589248374366624041 598879191936280774968031)
      ·
        refine ⟨898318787904421162452047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598879191936280774968031 898318787904421162452047)
        ·
          refine ⟨1347478181856631743678071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898318787904421162452047 1347478181856631743678071)
          ·
            refine ⟨2021217272784947615517107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347478181856631743678071 2021217272784947615517107)
            ·
              refine ⟨3031825909177421423275661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021217272784947615517107 3031825909177421423275661)
              ·
                refine ⟨1136934715941533033728373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3031825909177421423275661 1136934715941533033728373)
                ·
                  refine ⟨106587629619518721912035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1136934715941533033728373 106587629619518721912035)
                  ·
                    rfl

theorem cell20_233526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_233526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233526 prefixEnd_233526 := by exact prefixLift 233526
  have htrace : WordTrace (prefixWord ++ tailWord_233526) baseStart_233526 baseEnd_233526 := by
    simpa [prefixWord, tailWord_233526, baseEnd_233526] using wordTrace_append hprefix tailTrace_233526
  have hstable : (prefixWord ++ tailWord_233526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233526).length < 2 ^ (prefixWord ++ tailWord_233526).sum := by decide
  have hdescent : baseEnd_233526 < baseStart_233526 := by decide
  rcases family_descends (prefixWord ++ tailWord_233526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233529 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 4]
def baseStart_233529 : Nat := 118140960795 + 233529 * 2 ^ 59
def prefixEnd_233529 : Nat := 4983230072969 + 3 ^ 40 * 233529 * 2
def baseEnd_233529 : Nat := 106588998901264044812023

theorem tailTrace_233529 : CollatzResearch.WordTrace tailWord_233529 prefixEnd_233529 106588998901264044812023 := by
  unfold tailWord_233529
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517502370971791423015641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5678334913981194282010427 8517502370971791423015641)
  ·
    refine ⟨6388126778228843567261731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8517502370971791423015641 6388126778228843567261731)
    ·
      refine ⟨9582190167343265350892597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6388126778228843567261731 9582190167343265350892597)
      ·
        refine ⟨898330328188431126646181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9582190167343265350892597 898330328188431126646181)
        ·
          refine ⟨168436936535330836246159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 898330328188431126646181 168436936535330836246159)
          ·
            refine ⟨252655404802996254369239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168436936535330836246159 252655404802996254369239)
            ·
              refine ⟨378983107204494381553859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252655404802996254369239 378983107204494381553859)
              ·
                refine ⟨568474660806741572330789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378983107204494381553859 568474660806741572330789)
                ·
                  refine ⟨106588998901264044812023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568474660806741572330789 106588998901264044812023)
                  ·
                    rfl

theorem cell20_233529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_233529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233529 prefixEnd_233529 := by exact prefixLift 233529
  have htrace : WordTrace (prefixWord ++ tailWord_233529) baseStart_233529 baseEnd_233529 := by
    simpa [prefixWord, tailWord_233529, baseEnd_233529] using wordTrace_append hprefix tailTrace_233529
  have hstable : (prefixWord ++ tailWord_233529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233529).length < 2 ^ (prefixWord ++ tailWord_233529).sum := by decide
  have hdescent : baseEnd_233529 < baseStart_233529 := by decide
  rcases family_descends (prefixWord ++ tailWord_233529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233547 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 3]
def baseStart_233547 : Nat := 118140960795 + 233547 * 2 ^ 59
def prefixEnd_233547 : Nat := 4983230072969 + 3 ^ 40 * 233547 * 2
def baseEnd_233547 : Nat := 106597214591735982211949

theorem tailTrace_233547 : CollatzResearch.WordTrace tailWord_233547 prefixEnd_233547 106597214591735982211949 := by
  unfold tailWord_233547
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518158884906580497170895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5678772589937720331447263 8518158884906580497170895)
  ·
    refine ⟨12777238327359870745756343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8518158884906580497170895 12777238327359870745756343)
    ·
      refine ⟨19165857491039806118634515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12777238327359870745756343 19165857491039806118634515)
      ·
        refine ⟨28748786236559709177951773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19165857491039806118634515 28748786236559709177951773)
        ·
          refine ⟨10780794838709890941731915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28748786236559709177951773 10780794838709890941731915)
          ·
            refine ⟨16171192258064836412597873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10780794838709890941731915 16171192258064836412597873)
            ·
              refine ⟨12128394193548627309448405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16171192258064836412597873 12128394193548627309448405)
              ·
                refine ⟨284259238911295952565197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12128394193548627309448405 284259238911295952565197)
                ·
                  refine ⟨106597214591735982211949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284259238911295952565197 106597214591735982211949)
                  ·
                    rfl

theorem cell20_233547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_233547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233547 prefixEnd_233547 := by exact prefixLift 233547
  have htrace : WordTrace (prefixWord ++ tailWord_233547) baseStart_233547 baseEnd_233547 := by
    simpa [prefixWord, tailWord_233547, baseEnd_233547] using wordTrace_append hprefix tailTrace_233547
  have hstable : (prefixWord ++ tailWord_233547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233547).length < 2 ^ (prefixWord ++ tailWord_233547).sum := by decide
  have hdescent : baseEnd_233547 < baseStart_233547 := by decide
  rcases family_descends (prefixWord ++ tailWord_233547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233561 : List Nat := [1, 2, 1, 2, 2, 1, 3, 8]
def baseStart_233561 : Nat := 118140960795 + 233561 * 2 ^ 59
def prefixEnd_233561 : Nat := 4983230072969 + 3 ^ 40 * 233561 * 2
def baseEnd_233561 : Nat := 35534534857738051915075

theorem tailTrace_233561 : CollatzResearch.WordTrace tailWord_233561 prefixEnd_233561 35534534857738051915075 := by
  unfold tailWord_233561
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518669506855860888180537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5679113004570573925453691 8518669506855860888180537)
  ·
    refine ⟨6389002130141895666135403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8518669506855860888180537 6389002130141895666135403)
    ·
      refine ⟨9583503195212843499203105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389002130141895666135403 9583503195212843499203105)
      ·
        refine ⟨7187627396409632624402329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9583503195212843499203105 7187627396409632624402329)
        ·
          refine ⟨5390720547307224468301747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7187627396409632624402329 5390720547307224468301747)
          ·
            refine ⟨8086080820960836702452621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390720547307224468301747 8086080820960836702452621)
            ·
              refine ⟨3032280307860313763419733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8086080820960836702452621 3032280307860313763419733)
              ·
                refine ⟨35534534857738051915075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3032280307860313763419733 35534534857738051915075)
                ·
                  rfl

theorem cell20_233561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_233561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233561 prefixEnd_233561 := by exact prefixLift 233561
  have htrace : WordTrace (prefixWord ++ tailWord_233561) baseStart_233561 baseEnd_233561 := by
    simpa [prefixWord, tailWord_233561, baseEnd_233561] using wordTrace_append hprefix tailTrace_233561
  have hstable : (prefixWord ++ tailWord_233561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233561).length < 2 ^ (prefixWord ++ tailWord_233561).sum := by decide
  have hdescent : baseEnd_233561 < baseStart_233561 := by decide
  rcases family_descends (prefixWord ++ tailWord_233561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233578 : List Nat := [3, 1, 3, 2, 3, 8]
def baseStart_233578 : Nat := 118140960795 + 233578 * 2 ^ 59
def prefixEnd_233578 : Nat := 4983230072969 + 3 ^ 40 * 233578 * 2
def baseEnd_233578 : Nat := 3948569030979172302907

theorem tailTrace_233578 : CollatzResearch.WordTrace tailWord_233578 prefixEnd_233578 3948569030979172302907 := by
  unfold tailWord_233578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129822386948568197887347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5679526365196181861032925 2129822386948568197887347)
  ·
    refine ⟨3194733580422852296831021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2129822386948568197887347 3194733580422852296831021)
    ·
      refine ⟨1198025092658569611311633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3194733580422852296831021 1198025092658569611311633)
      ·
        refine ⟨898518819493927208483725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1198025092658569611311633 898518819493927208483725)
        ·
          refine ⟨336944557310222703181397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 898518819493927208483725 336944557310222703181397)
          ·
            refine ⟨3948569030979172302907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 336944557310222703181397 3948569030979172302907)
            ·
              rfl

theorem cell20_233578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 8].length) (baseStart_233578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233578 prefixEnd_233578 := by exact prefixLift 233578
  have htrace : WordTrace (prefixWord ++ tailWord_233578) baseStart_233578 baseEnd_233578 := by
    simpa [prefixWord, tailWord_233578, baseEnd_233578] using wordTrace_append hprefix tailTrace_233578
  have hstable : (prefixWord ++ tailWord_233578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233578).length < 2 ^ (prefixWord ++ tailWord_233578).sum := by decide
  have hdescent : baseEnd_233578 < baseStart_233578 := by decide
  rcases family_descends (prefixWord ++ tailWord_233578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233592 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_233592 : Nat := 118140960795 + 233592 * 2 ^ 59
def prefixEnd_233592 : Nat := 4983230072969 + 3 ^ 40 * 233592 * 2
def baseEnd_233592 : Nat := 106617753817915825711765

theorem tailTrace_233592 : CollatzResearch.WordTrace tailWord_233592 prefixEnd_233592 106617753817915825711765 := by
  unfold tailWord_233592
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259900084871776591279515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5679866779829035455039353 4259900084871776591279515)
  ·
    refine ⟨6389850127307664886919273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4259900084871776591279515 6389850127307664886919273)
    ·
      refine ⟨4792387595480748665189455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6389850127307664886919273 4792387595480748665189455)
      ·
        refine ⟨7188581393221122997784183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792387595480748665189455 7188581393221122997784183)
        ·
          refine ⟨10782872089831684496676275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188581393221122997784183 10782872089831684496676275)
          ·
            refine ⟨16174308134747526745014413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10782872089831684496676275 16174308134747526745014413)
            ·
              refine ⟨6065365550530322529380405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16174308134747526745014413 6065365550530322529380405)
              ·
                refine ⟨568628020362217737129413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6065365550530322529380405 568628020362217737129413)
                ·
                  refine ⟨106617753817915825711765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568628020362217737129413 106617753817915825711765)
                  ·
                    rfl

theorem cell20_233592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_233592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233592 prefixEnd_233592 := by exact prefixLift 233592
  have htrace : WordTrace (prefixWord ++ tailWord_233592) baseStart_233592 baseEnd_233592 := by
    simpa [prefixWord, tailWord_233592, baseEnd_233592] using wordTrace_append hprefix tailTrace_233592
  have hstable : (prefixWord ++ tailWord_233592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233592).length < 2 ^ (prefixWord ++ tailWord_233592).sum := by decide
  have hdescent : baseEnd_233592 < baseStart_233592 := by decide
  rcases family_descends (prefixWord ++ tailWord_233592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233616 : List Nat := [2, 1, 1, 1, 1, 1, 9, 4]
def baseStart_233616 : Nat := 118140960795 + 233616 * 2 ^ 59
def prefixEnd_233616 : Nat := 4983230072969 + 3 ^ 40 * 233616 * 2
def baseEnd_233616 : Nat := 35542902690626136303889

theorem tailTrace_233616 : CollatzResearch.WordTrace tailWord_233616 prefixEnd_233616 35542902690626136303889 := by
  unfold tailWord_233616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4260337760828302640716351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5680450347771070187621801 4260337760828302640716351)
  ·
    refine ⟨6390506641242453961074527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4260337760828302640716351 6390506641242453961074527)
    ·
      refine ⟨9585759961863680941611791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6390506641242453961074527 9585759961863680941611791)
      ·
        refine ⟨14378639942795521412417687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9585759961863680941611791 14378639942795521412417687)
        ·
          refine ⟨21567959914193282118626531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14378639942795521412417687 21567959914193282118626531)
          ·
            refine ⟨32351939871289923177939797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21567959914193282118626531 32351939871289923177939797)
            ·
              refine ⟨189562147683339393620741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 32351939871289923177939797 189562147683339393620741)
              ·
                refine ⟨35542902690626136303889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189562147683339393620741 35542902690626136303889)
                ·
                  rfl

theorem cell20_233616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_233616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233616 prefixEnd_233616 := by exact prefixLift 233616
  have htrace : WordTrace (prefixWord ++ tailWord_233616) baseStart_233616 baseEnd_233616 := by
    simpa [prefixWord, tailWord_233616, baseEnd_233616] using wordTrace_append hprefix tailTrace_233616
  have hstable : (prefixWord ++ tailWord_233616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233616).length < 2 ^ (prefixWord ++ tailWord_233616).sum := by decide
  have hdescent : baseEnd_233616 < baseStart_233616 := by decide
  rcases family_descends (prefixWord ++ tailWord_233616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233636 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 3]
def baseStart_233636 : Nat := 118140960795 + 233636 * 2 ^ 59
def prefixEnd_233636 : Nat := 4983230072969 + 3 ^ 40 * 233636 * 2
def baseEnd_233636 : Nat := 106637836616847228244919

theorem tailTrace_233636 : CollatzResearch.WordTrace tailWord_233636 prefixEnd_233636 106637836616847228244919 := by
  unfold tailWord_233636
  simp only [CollatzResearch.WordTrace]
  refine ⟨4260702490792074348580381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5680936654389432464773841 4260702490792074348580381)
  ·
    refine ⟨1597763434047027880717643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4260702490792074348580381 1597763434047027880717643)
    ·
      refine ⟨2396645151070541821076465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597763434047027880717643 2396645151070541821076465)
      ·
        refine ⟨1797483863302906365807349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2396645151070541821076465 1797483863302906365807349)
        ·
          refine ⟨168514112184647471794439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1797483863302906365807349 168514112184647471794439)
          ·
            refine ⟨252771168276971207691659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168514112184647471794439 252771168276971207691659)
            ·
              refine ⟨379156752415456811537489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252771168276971207691659 379156752415456811537489)
              ·
                refine ⟨284367564311592608653117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379156752415456811537489 284367564311592608653117)
                ·
                  refine ⟨106637836616847228244919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284367564311592608653117 106637836616847228244919)
                  ·
                    rfl

theorem cell20_233636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_233636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233636 prefixEnd_233636 := by exact prefixLift 233636
  have htrace : WordTrace (prefixWord ++ tailWord_233636) baseStart_233636 baseEnd_233636 := by
    simpa [prefixWord, tailWord_233636, baseEnd_233636] using wordTrace_append hprefix tailTrace_233636
  have hstable : (prefixWord ++ tailWord_233636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233636).length < 2 ^ (prefixWord ++ tailWord_233636).sum := by decide
  have hdescent : baseEnd_233636 < baseStart_233636 := by decide
  rcases family_descends (prefixWord ++ tailWord_233636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233637 : List Nat := [1, 3, 1, 2, 1, 3, 9]
def baseStart_233637 : Nat := 118140960795 + 233637 * 2 ^ 59
def prefixEnd_233637 : Nat := 4983230072969 + 3 ^ 40 * 233637 * 2
def baseEnd_233637 : Nat := 11848699227121741023509

theorem tailTrace_233637 : CollatzResearch.WordTrace tailWord_233637 prefixEnd_233637 11848699227121741023509 := by
  unfold tailWord_233637
  simp only [CollatzResearch.WordTrace]
  refine ⟨8521441454580525867947165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5680960969720350578631443 8521441454580525867947165)
  ·
    refine ⟨3195540545467697200480187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8521441454580525867947165 3195540545467697200480187)
    ·
      refine ⟨4793310818201545800720281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3195540545467697200480187 4793310818201545800720281)
      ·
        refine ⟨3594983113651159350540211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4793310818201545800720281 3594983113651159350540211)
        ·
          refine ⟨5392474670476739025810317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594983113651159350540211 5392474670476739025810317)
          ·
            refine ⟨2022178001428777134678869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5392474670476739025810317 2022178001428777134678869)
            ·
              refine ⟨11848699227121741023509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2022178001428777134678869 11848699227121741023509)
              ·
                rfl

theorem cell20_233637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 9].length) (baseStart_233637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233637 prefixEnd_233637 := by exact prefixLift 233637
  have htrace : WordTrace (prefixWord ++ tailWord_233637) baseStart_233637 baseEnd_233637 := by
    simpa [prefixWord, tailWord_233637, baseEnd_233637] using wordTrace_append hprefix tailTrace_233637
  have hstable : (prefixWord ++ tailWord_233637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233637).length < 2 ^ (prefixWord ++ tailWord_233637).sum := by decide
  have hdescent : baseEnd_233637 < baseStart_233637 := by decide
  rcases family_descends (prefixWord ++ tailWord_233637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233675 : List Nat := [1, 1, 1, 1, 3, 2, 5, 6]
def baseStart_233675 : Nat := 118140960795 + 233675 * 2 ^ 59
def prefixEnd_233675 : Nat := 4983230072969 + 3 ^ 40 * 233675 * 2
def baseEnd_233675 : Nat := 35551879093178808648253

theorem tailTrace_233675 : CollatzResearch.WordTrace tailWord_233675 prefixEnd_233675 35551879093178808648253 := by
  unfold tailWord_233675
  simp only [CollatzResearch.WordTrace]
  refine ⟨8522827428442858357830479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5681884952295238905220319 8522827428442858357830479)
  ·
    refine ⟨12784241142664287536745719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8522827428442858357830479 12784241142664287536745719)
    ·
      refine ⟨19176361713996431305118579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12784241142664287536745719 19176361713996431305118579)
      ·
        refine ⟨28764542570994646957677869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19176361713996431305118579 28764542570994646957677869)
        ·
          refine ⟨10786703464122992609129201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28764542570994646957677869 10786703464122992609129201)
          ·
            refine ⟨8090027598092244456846901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10786703464122992609129201 8090027598092244456846901)
            ·
              refine ⟨758440087321147917829397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8090027598092244456846901 758440087321147917829397)
              ·
                refine ⟨35551879093178808648253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 758440087321147917829397 35551879093178808648253)
                ·
                  rfl

theorem cell20_233675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_233675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233675 prefixEnd_233675 := by exact prefixLift 233675
  have htrace : WordTrace (prefixWord ++ tailWord_233675) baseStart_233675 baseEnd_233675 := by
    simpa [prefixWord, tailWord_233675, baseEnd_233675] using wordTrace_append hprefix tailTrace_233675
  have hstable : (prefixWord ++ tailWord_233675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233675).length < 2 ^ (prefixWord ++ tailWord_233675).sum := by decide
  have hdescent : baseEnd_233675 < baseStart_233675 := by decide
  rcases family_descends (prefixWord ++ tailWord_233675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233709 : List Nat := [1, 5, 1, 2, 3, 1, 2, 5]
def baseStart_233709 : Nat := 118140960795 + 233709 * 2 ^ 59
def prefixEnd_233709 : Nat := 4983230072969 + 3 ^ 40 * 233709 * 2
def baseEnd_233709 : Nat := 35557051935327806270429

theorem tailTrace_233709 : CollatzResearch.WordTrace tailWord_233709 prefixEnd_233709 35557051935327806270429 := by
  unfold tailWord_233709
  simp only [CollatzResearch.WordTrace]
  refine ⟨8524067510319682164568181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5682711673546454776378787 8524067510319682164568181)
  ·
    refine ⟨799131329092470202928267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8524067510319682164568181 799131329092470202928267)
    ·
      refine ⟨1198696993638705304392401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799131329092470202928267 1198696993638705304392401)
      ·
        refine ⟨899022745229028978294301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1198696993638705304392401 899022745229028978294301)
        ·
          refine ⟨337133529460885866860363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 899022745229028978294301 337133529460885866860363)
          ·
            refine ⟨505700294191328800290545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337133529460885866860363 505700294191328800290545)
            ·
              refine ⟨379275220643496600217909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505700294191328800290545 379275220643496600217909)
              ·
                refine ⟨35557051935327806270429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379275220643496600217909 35557051935327806270429)
                ·
                  rfl

theorem cell20_233709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_233709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233709 prefixEnd_233709 := by exact prefixLift 233709
  have htrace : WordTrace (prefixWord ++ tailWord_233709) baseStart_233709 baseEnd_233709 := by
    simpa [prefixWord, tailWord_233709, baseEnd_233709] using wordTrace_append hprefix tailTrace_233709
  have hstable : (prefixWord ++ tailWord_233709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233709).length < 2 ^ (prefixWord ++ tailWord_233709).sum := by decide
  have hdescent : baseEnd_233709 < baseStart_233709 := by decide
  rcases family_descends (prefixWord ++ tailWord_233709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233713 : List Nat := [1, 2, 2, 2, 2, 1, 3, 7]
def baseStart_233713 : Nat := 118140960795 + 233713 * 2 ^ 59
def prefixEnd_233713 : Nat := 4983230072969 + 3 ^ 40 * 233713 * 2
def baseEnd_233713 : Nat := 35557660504992394225979

theorem tailTrace_233713 : CollatzResearch.WordTrace tailWord_233713 prefixEnd_233713 35557660504992394225979 := by
  unfold tailWord_233713
  simp only [CollatzResearch.WordTrace]
  refine ⟨8524213402305190847713793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5682808934870127231809195 8524213402305190847713793)
  ·
    refine ⟨6393160051728893135785345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8524213402305190847713793 6393160051728893135785345)
    ·
      refine ⟨4794870038796669851839009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6393160051728893135785345 4794870038796669851839009)
      ·
        refine ⟨3596152529097502388879257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4794870038796669851839009 3596152529097502388879257)
        ·
          refine ⟨2697114396823126791659443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596152529097502388879257 2697114396823126791659443)
          ·
            refine ⟨4045671595234690187489165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697114396823126791659443 4045671595234690187489165)
            ·
              refine ⟨1517126848213008820308437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4045671595234690187489165 1517126848213008820308437)
              ·
                refine ⟨35557660504992394225979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1517126848213008820308437 35557660504992394225979)
                ·
                  rfl

theorem cell20_233713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_233713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233713 prefixEnd_233713 := by exact prefixLift 233713
  have htrace : WordTrace (prefixWord ++ tailWord_233713) baseStart_233713 baseEnd_233713 := by
    simpa [prefixWord, tailWord_233713, baseEnd_233713] using wordTrace_append hprefix tailTrace_233713
  have hstable : (prefixWord ++ tailWord_233713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233713).length < 2 ^ (prefixWord ++ tailWord_233713).sum := by decide
  have hdescent : baseEnd_233713 < baseStart_233713 := by decide
  rcases family_descends (prefixWord ++ tailWord_233713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233751 : List Nat := [1, 1, 3, 4, 1, 10]
def baseStart_233751 : Nat := 118140960795 + 233751 * 2 ^ 59
def prefixEnd_233751 : Nat := 4983230072969 + 3 ^ 40 * 233751 * 2
def baseEnd_233751 : Nat := 3951493546311775533745

theorem tailTrace_233751 : CollatzResearch.WordTrace tailWord_233751 prefixEnd_233751 3951493546311775533745 := by
  unfold tailWord_233751
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525599376167523337597107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5683732917445015558398071 8525599376167523337597107)
  ·
    refine ⟨12788399064251285006395661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8525599376167523337597107 12788399064251285006395661)
    ·
      refine ⟨4795649649094231877398373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12788399064251285006395661 4795649649094231877398373)
      ·
        refine ⟨899184309205168477012195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4795649649094231877398373 899184309205168477012195)
        ·
          refine ⟨1348776463807752715518293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899184309205168477012195 1348776463807752715518293)
          ·
            refine ⟨3951493546311775533745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1348776463807752715518293 3951493546311775533745)
            ·
              rfl

theorem cell20_233751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 10].length) (baseStart_233751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233751 prefixEnd_233751 := by exact prefixLift 233751
  have htrace : WordTrace (prefixWord ++ tailWord_233751) baseStart_233751 baseEnd_233751 := by
    simpa [prefixWord, tailWord_233751, baseEnd_233751] using wordTrace_append hprefix tailTrace_233751
  have hstable : (prefixWord ++ tailWord_233751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233751).length < 2 ^ (prefixWord ++ tailWord_233751).sum := by decide
  have hdescent : baseEnd_233751 < baseStart_233751 := by decide
  rcases family_descends (prefixWord ++ tailWord_233751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233757 : List Nat := [1, 4, 2, 3, 2, 1, 1, 4, 2]
def baseStart_233757 : Nat := 118140960795 + 233757 * 2 ^ 59
def prefixEnd_233757 : Nat := 4983230072969 + 3 ^ 40 * 233757 * 2
def baseEnd_233757 : Nat := 106693064313908585211091

theorem tailTrace_233757 : CollatzResearch.WordTrace tailWord_233757 prefixEnd_233757 106693064313908585211091 := by
  unfold tailWord_233757
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525818214145786362315525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5683878809430524241543683 8525818214145786362315525)
  ·
    refine ⟨1598590915152334942934161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8525818214145786362315525 1598590915152334942934161)
    ·
      refine ⟨1198943186364251207200621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1598590915152334942934161 1198943186364251207200621)
      ·
        refine ⟨449603694886594202700233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1198943186364251207200621 449603694886594202700233)
        ·
          refine ⟨337202771164945652025175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449603694886594202700233 337202771164945652025175)
          ·
            refine ⟨505804156747418478037763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337202771164945652025175 505804156747418478037763)
            ·
              refine ⟨758706235121127717056645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505804156747418478037763 758706235121127717056645)
              ·
                refine ⟨142257419085211446948121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758706235121127717056645 142257419085211446948121)
                ·
                  refine ⟨106693064313908585211091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142257419085211446948121 106693064313908585211091)
                  ·
                    rfl

theorem cell20_233757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_233757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233757 prefixEnd_233757 := by exact prefixLift 233757
  have htrace : WordTrace (prefixWord ++ tailWord_233757) baseStart_233757 baseEnd_233757 := by
    simpa [prefixWord, tailWord_233757, baseEnd_233757] using wordTrace_append hprefix tailTrace_233757
  have hstable : (prefixWord ++ tailWord_233757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233757).length < 2 ^ (prefixWord ++ tailWord_233757).sum := by decide
  have hdescent : baseEnd_233757 < baseStart_233757 := by decide
  rcases family_descends (prefixWord ++ tailWord_233757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233775 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 3]
def baseStart_233775 : Nat := 118140960795 + 233775 * 2 ^ 59
def prefixEnd_233775 : Nat := 4983230072969 + 3 ^ 40 * 233775 * 2
def baseEnd_233775 : Nat := 106701280004380522611017

theorem tailTrace_233775 : CollatzResearch.WordTrace tailWord_233775 prefixEnd_233775 106701280004380522611017 := by
  unfold tailWord_233775
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526474728080575436470779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5684316485387050290980519 8526474728080575436470779)
  ·
    refine ⟨12789712092120863154706169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8526474728080575436470779 12789712092120863154706169)
    ·
      refine ⟨9592284069090647366029627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12789712092120863154706169 9592284069090647366029627)
      ·
        refine ⟨14388426103635971049044441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9592284069090647366029627 14388426103635971049044441)
        ·
          refine ⟨10791319577726978286783331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14388426103635971049044441 10791319577726978286783331)
          ·
            refine ⟨16186979366590467430174997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10791319577726978286783331 16186979366590467430174997)
            ·
              refine ⟨758764657808928160789453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16186979366590467430174997 758764657808928160789453)
              ·
                refine ⟨284536746678348060296045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 758764657808928160789453 284536746678348060296045)
                ·
                  refine ⟨106701280004380522611017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284536746678348060296045 106701280004380522611017)
                  ·
                    rfl

theorem cell20_233775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_233775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233775 prefixEnd_233775 := by exact prefixLift 233775
  have htrace : WordTrace (prefixWord ++ tailWord_233775) baseStart_233775 baseEnd_233775 := by
    simpa [prefixWord, tailWord_233775, baseEnd_233775] using wordTrace_append hprefix tailTrace_233775
  have hstable : (prefixWord ++ tailWord_233775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233775).length < 2 ^ (prefixWord ++ tailWord_233775).sum := by decide
  have hdescent : baseEnd_233775 < baseStart_233775 := by decide
  rcases family_descends (prefixWord ++ tailWord_233775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233785 : List Nat := [1, 2, 1, 6, 1, 2, 3, 4]
def baseStart_233785 : Nat := 118140960795 + 233785 * 2 ^ 59
def prefixEnd_233785 : Nat := 4983230072969 + 3 ^ 40 * 233785 * 2
def baseEnd_233785 : Nat := 35568614758954977425881

theorem tailTrace_233785 : CollatzResearch.WordTrace tailWord_233785 prefixEnd_233785 35568614758954977425881 := by
  unfold tailWord_233785
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526839458044347144334809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5684559638696231429556539 8526839458044347144334809)
  ·
    refine ⟨6395129593533260358251107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8526839458044347144334809 6395129593533260358251107)
    ·
      refine ⟨9592694390299890537376661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6395129593533260358251107 9592694390299890537376661)
      ·
        refine ⟨449657549545307368939531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9592694390299890537376661 449657549545307368939531)
        ·
          refine ⟨674486324317961053409297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449657549545307368939531 674486324317961053409297)
          ·
            refine ⟨505864743238470790056973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674486324317961053409297 505864743238470790056973)
            ·
              refine ⟨189699278714426546271365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505864743238470790056973 189699278714426546271365)
              ·
                refine ⟨35568614758954977425881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189699278714426546271365 35568614758954977425881)
                ·
                  rfl

theorem cell20_233785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 4].length) (baseStart_233785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233785 prefixEnd_233785 := by exact prefixLift 233785
  have htrace : WordTrace (prefixWord ++ tailWord_233785) baseStart_233785 baseEnd_233785 := by
    simpa [prefixWord, tailWord_233785, baseEnd_233785] using wordTrace_append hprefix tailTrace_233785
  have hstable : (prefixWord ++ tailWord_233785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233785).length < 2 ^ (prefixWord ++ tailWord_233785).sum := by decide
  have hdescent : baseEnd_233785 < baseStart_233785 := by decide
  rcases family_descends (prefixWord ++ tailWord_233785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233827 : List Nat := [1, 1, 1, 5, 2, 1, 2, 7]
def baseStart_233827 : Nat := 118140960795 + 233827 * 2 ^ 59
def prefixEnd_233827 : Nat := 4983230072969 + 3 ^ 40 * 233827 * 2
def baseEnd_233827 : Nat := 35575004740433150959157

theorem tailTrace_233827 : CollatzResearch.WordTrace tailWord_233827 prefixEnd_233827 35575004740433150959157 := by
  unfold tailWord_233827
  simp only [CollatzResearch.WordTrace]
  refine ⟨8528371323892188317363735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5685580882594792211575823 8528371323892188317363735)
  ·
    refine ⟨12792556985838282476045603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8528371323892188317363735 12792556985838282476045603)
    ·
      refine ⟨19188835478757423714068405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12792556985838282476045603 19188835478757423714068405)
      ·
        refine ⟨1798953326133508473193913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19188835478757423714068405 1798953326133508473193913)
        ·
          refine ⟨1349214994600131354895435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1798953326133508473193913 1349214994600131354895435)
          ·
            refine ⟨2023822491900197032343153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349214994600131354895435 2023822491900197032343153)
            ·
              refine ⟨1517866868925147774257365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023822491900197032343153 1517866868925147774257365)
              ·
                refine ⟨35575004740433150959157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1517866868925147774257365 35575004740433150959157)
                ·
                  rfl

theorem cell20_233827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_233827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233827 prefixEnd_233827 := by exact prefixLift 233827
  have htrace : WordTrace (prefixWord ++ tailWord_233827) baseStart_233827 baseEnd_233827 := by
    simpa [prefixWord, tailWord_233827, baseEnd_233827] using wordTrace_append hprefix tailTrace_233827
  have hstable : (prefixWord ++ tailWord_233827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233827).length < 2 ^ (prefixWord ++ tailWord_233827).sum := by decide
  have hdescent : baseEnd_233827 < baseStart_233827 := by decide
  rcases family_descends (prefixWord ++ tailWord_233827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233865 : List Nat := [1, 2, 1, 1, 6, 1, 8]
def baseStart_233865 : Nat := 118140960795 + 233865 * 2 ^ 59
def prefixEnd_233865 : Nat := 4983230072969 + 3 ^ 40 * 233865 * 2
def baseEnd_233865 : Nat := 11860262050748912178961

theorem tailTrace_233865 : CollatzResearch.WordTrace tailWord_233865 prefixEnd_233865 11860262050748912178961 := by
  unfold tailWord_233865
  simp only [CollatzResearch.WordTrace]
  refine ⟨8529757297754520807247049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5686504865169680538164699 8529757297754520807247049)
  ·
    refine ⟨6397317973315890605435287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8529757297754520807247049 6397317973315890605435287)
    ·
      refine ⟨9595976959973835908152931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6397317973315890605435287 9595976959973835908152931)
      ·
        refine ⟨14393965439960753862229397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9595976959973835908152931 14393965439960753862229397)
        ·
          refine ⟨674717129998160337292003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14393965439960753862229397 674717129998160337292003)
          ·
            refine ⟨1012075694997240505938005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674717129998160337292003 1012075694997240505938005)
            ·
              refine ⟨11860262050748912178961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1012075694997240505938005 11860262050748912178961)
              ·
                rfl

theorem cell20_233865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 8].length) (baseStart_233865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233865 prefixEnd_233865 := by exact prefixLift 233865
  have htrace : WordTrace (prefixWord ++ tailWord_233865) baseStart_233865 baseEnd_233865 := by
    simpa [prefixWord, tailWord_233865, baseEnd_233865] using wordTrace_append hprefix tailTrace_233865
  have hstable : (prefixWord ++ tailWord_233865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233865).length < 2 ^ (prefixWord ++ tailWord_233865).sum := by decide
  have hdescent : baseEnd_233865 < baseStart_233865 := by decide
  rcases family_descends (prefixWord ++ tailWord_233865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233882 : List Nat := [3, 1, 1, 4, 1, 3, 2, 5]
def baseStart_233882 : Nat := 118140960795 + 233882 * 2 ^ 59
def prefixEnd_233882 : Nat := 4983230072969 + 3 ^ 40 * 233882 * 2
def baseEnd_233882 : Nat := 35583372573321235347971

theorem tailTrace_233882 : CollatzResearch.WordTrace tailWord_233882 prefixEnd_233882 35583372573321235347971 := by
  unfold tailWord_233882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132594334673233177653975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5686918225795288473743933 2132594334673233177653975)
  ·
    refine ⟨3198891502009849766480963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2132594334673233177653975 3198891502009849766480963)
    ·
      refine ⟨4798337253014774649721445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198891502009849766480963 4798337253014774649721445)
      ·
        refine ⟨899688234940270246822771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4798337253014774649721445 899688234940270246822771)
        ·
          refine ⟨1349532352410405370234157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899688234940270246822771 1349532352410405370234157)
          ·
            refine ⟨506074632153902013837809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1349532352410405370234157 506074632153902013837809)
            ·
              refine ⟨379555974115426510378357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506074632153902013837809 379555974115426510378357)
              ·
                refine ⟨35583372573321235347971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379555974115426510378357 35583372573321235347971)
                ·
                  rfl

theorem cell20_233882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_233882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233882 prefixEnd_233882 := by exact prefixLift 233882
  have htrace : WordTrace (prefixWord ++ tailWord_233882) baseStart_233882 baseEnd_233882 := by
    simpa [prefixWord, tailWord_233882, baseEnd_233882] using wordTrace_append hprefix tailTrace_233882
  have hstable : (prefixWord ++ tailWord_233882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233882).length < 2 ^ (prefixWord ++ tailWord_233882).sum := by decide
  have hdescent : baseEnd_233882 < baseStart_233882 := by decide
  rcases family_descends (prefixWord ++ tailWord_233882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233927 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 3]
def baseStart_233927 : Nat := 118140960795 + 233927 * 2 ^ 59
def prefixEnd_233927 : Nat := 4983230072969 + 3 ^ 40 * 233927 * 2
def baseEnd_233927 : Nat := 106770656946143549543729

theorem tailTrace_233927 : CollatzResearch.WordTrace tailWord_233927 prefixEnd_233927 106770656946143549543729 := by
  unfold tailWord_233927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8532018623529905396004035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5688012415686603597336023 8532018623529905396004035)
  ·
    refine ⟨12798027935294858094006053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8532018623529905396004035 12798027935294858094006053)
    ·
      refine ⟨2399630237867785892626135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12798027935294858094006053 2399630237867785892626135)
      ·
        refine ⟨3599445356801678838939203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399630237867785892626135 3599445356801678838939203)
        ·
          refine ⟨5399168035202518258408805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599445356801678838939203 5399168035202518258408805)
          ·
            refine ⟨1012344006600472173451651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5399168035202518258408805 1012344006600472173451651)
            ·
              refine ⟨1518516009900708260177477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012344006600472173451651 1518516009900708260177477)
              ·
                refine ⟨284721751856382798783277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1518516009900708260177477 284721751856382798783277)
                ·
                  refine ⟨106770656946143549543729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284721751856382798783277 106770656946143549543729)
                  ·
                    rfl

theorem cell20_233927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_233927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233927 prefixEnd_233927 := by exact prefixLift 233927
  have htrace : WordTrace (prefixWord ++ tailWord_233927) baseStart_233927 baseEnd_233927 := by
    simpa [prefixWord, tailWord_233927, baseEnd_233927] using wordTrace_append hprefix tailTrace_233927
  have hstable : (prefixWord ++ tailWord_233927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233927).length < 2 ^ (prefixWord ++ tailWord_233927).sum := by decide
  have hdescent : baseEnd_233927 < baseStart_233927 := by decide
  rcases family_descends (prefixWord ++ tailWord_233927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233934 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_233934 : Nat := 118140960795 + 233934 * 2 ^ 59
def prefixEnd_233934 : Nat := 4983230072969 + 3 ^ 40 * 233934 * 2
def baseEnd_233934 : Nat := 106773851936882636310367

theorem tailTrace_233934 : CollatzResearch.WordTrace tailWord_233934 prefixEnd_233934 106773851936882636310367 := by
  unfold tailWord_233934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066534241813068198938607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5688182623003030394339237 1066534241813068198938607)
  ·
    refine ⟨1599801362719602298407911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1066534241813068198938607 1599801362719602298407911)
    ·
      refine ⟨2399702044079403447611867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599801362719602298407911 2399702044079403447611867)
      ·
        refine ⟨3599553066119105171417801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399702044079403447611867 3599553066119105171417801)
        ·
          refine ⟨2699664799589328878563351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3599553066119105171417801 2699664799589328878563351)
          ·
            refine ⟨4049497199383993317845027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699664799589328878563351 4049497199383993317845027)
            ·
              refine ⟨6074245799075989976767541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049497199383993317845027 6074245799075989976767541)
              ·
                refine ⟨569460543663374060321957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6074245799075989976767541 569460543663374060321957)
                ·
                  refine ⟨106773851936882636310367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569460543663374060321957 106773851936882636310367)
                  ·
                    rfl

theorem cell20_233934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_233934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233934 prefixEnd_233934 := by exact prefixLift 233934
  have htrace : WordTrace (prefixWord ++ tailWord_233934) baseStart_233934 baseEnd_233934 := by
    simpa [prefixWord, tailWord_233934, baseEnd_233934] using wordTrace_append hprefix tailTrace_233934
  have hstable : (prefixWord ++ tailWord_233934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233934).length < 2 ^ (prefixWord ++ tailWord_233934).sum := by decide
  have hdescent : baseEnd_233934 < baseStart_233934 := by decide
  rcases family_descends (prefixWord ++ tailWord_233934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233989 : List Nat := [1, 3, 1, 1, 2, 2, 4, 4, 2]
def baseStart_233989 : Nat := 118140960795 + 233989 * 2 ^ 59
def prefixEnd_233989 : Nat := 4983230072969 + 3 ^ 40 * 233989 * 2
def baseEnd_233989 : Nat := 106798955435546889476809

theorem tailTrace_233989 : CollatzResearch.WordTrace tailWord_233989 prefixEnd_233989 106798955435546889476809 := by
  unfold tailWord_233989
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534279949305289984761021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5689519966203526656507347 8534279949305289984761021)
  ·
    refine ⟨3200354980989483744285383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8534279949305289984761021 3200354980989483744285383)
    ·
      refine ⟨4800532471484225616428075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200354980989483744285383 4800532471484225616428075)
      ·
        refine ⟨7200798707226338424642113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800532471484225616428075 7200798707226338424642113)
        ·
          refine ⟨5400599030419753818481585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7200798707226338424642113 5400599030419753818481585)
          ·
            refine ⟨4050449272814815363861189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5400599030419753818481585 4050449272814815363861189)
            ·
              refine ⟨759459238652777880723973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4050449272814815363861189 759459238652777880723973)
              ·
                refine ⟨142398607247395852635745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 759459238652777880723973 142398607247395852635745)
                ·
                  refine ⟨106798955435546889476809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142398607247395852635745 106798955435546889476809)
                  ·
                    rfl

theorem cell20_233989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_233989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_233989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_233989 prefixEnd_233989 := by exact prefixLift 233989
  have htrace : WordTrace (prefixWord ++ tailWord_233989) baseStart_233989 baseEnd_233989 := by
    simpa [prefixWord, tailWord_233989, baseEnd_233989] using wordTrace_append hprefix tailTrace_233989
  have hstable : (prefixWord ++ tailWord_233989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233989).length < 2 ^ (prefixWord ++ tailWord_233989).sum := by decide
  have hdescent : baseEnd_233989 < baseStart_233989 := by decide
  rcases family_descends (prefixWord ++ tailWord_233989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234010 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_234010 : Nat := 118140960795 + 234010 * 2 ^ 59
def prefixEnd_234010 : Nat := 4983230072969 + 3 ^ 40 * 234010 * 2
def baseEnd_234010 : Nat := 106808540407764149776723

theorem tailTrace_234010 : CollatzResearch.WordTrace tailWord_234010 prefixEnd_234010 106808540407764149776723 := by
  unfold tailWord_234010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133761470557302642818871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5690030588152807047516989 2133761470557302642818871)
  ·
    refine ⟨3200642205835953964228307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2133761470557302642818871 3200642205835953964228307)
    ·
      refine ⟨4800963308753930946342461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200642205835953964228307 4800963308753930946342461)
      ·
        refine ⟨1800361240782724104878423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4800963308753930946342461 1800361240782724104878423)
        ·
          refine ⟨2700541861174086157317635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800361240782724104878423 2700541861174086157317635)
          ·
            refine ⟨4050812791761129235976453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700541861174086157317635 4050812791761129235976453)
            ·
              refine ⟨759527398455211731745585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4050812791761129235976453 759527398455211731745585)
              ·
                refine ⟨569645548841408798809189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759527398455211731745585 569645548841408798809189)
                ·
                  refine ⟨106808540407764149776723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569645548841408798809189 106808540407764149776723)
                  ·
                    rfl

theorem cell20_234010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_234010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234010 prefixEnd_234010 := by exact prefixLift 234010
  have htrace : WordTrace (prefixWord ++ tailWord_234010) baseStart_234010 baseEnd_234010 := by
    simpa [prefixWord, tailWord_234010, baseEnd_234010] using wordTrace_append hprefix tailTrace_234010
  have hstable : (prefixWord ++ tailWord_234010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234010).length < 2 ^ (prefixWord ++ tailWord_234010).sum := by decide
  have hdescent : baseEnd_234010 < baseStart_234010 := by decide
  rcases family_descends (prefixWord ++ tailWord_234010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234013 : List Nat := [1, 4, 2, 2, 1, 4, 2, 4]
def baseStart_234013 : Nat := 118140960795 + 234013 * 2 ^ 59
def prefixEnd_234013 : Nat := 4983230072969 + 3 ^ 40 * 234013 * 2
def baseEnd_234013 : Nat := 35603303229836490892237

theorem tailTrace_234013 : CollatzResearch.WordTrace tailWord_234013 prefixEnd_234013 35603303229836490892237 := by
  unfold tailWord_234013
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535155301218342083634693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5690103534145561389089795 8535155301218342083634693)
  ·
    refine ⟨1600341618978439140681505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8535155301218342083634693 1600341618978439140681505)
    ·
      refine ⟨1200256214233829355511129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1600341618978439140681505 1200256214233829355511129)
      ·
        refine ⟨900192160675372016633347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200256214233829355511129 900192160675372016633347)
        ·
          refine ⟨1350288241013058024950021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900192160675372016633347 1350288241013058024950021)
          ·
            refine ⟨253179045189948379678129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1350288241013058024950021 253179045189948379678129)
            ·
              refine ⟨189884283892461284758597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253179045189948379678129 189884283892461284758597)
              ·
                refine ⟨35603303229836490892237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189884283892461284758597 35603303229836490892237)
                ·
                  rfl

theorem cell20_234013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 4].length) (baseStart_234013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234013 prefixEnd_234013 := by exact prefixLift 234013
  have htrace : WordTrace (prefixWord ++ tailWord_234013) baseStart_234013 baseEnd_234013 := by
    simpa [prefixWord, tailWord_234013, baseEnd_234013] using wordTrace_append hprefix tailTrace_234013
  have hstable : (prefixWord ++ tailWord_234013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234013).length < 2 ^ (prefixWord ++ tailWord_234013).sum := by decide
  have hdescent : baseEnd_234013 < baseStart_234013 := by decide
  rcases family_descends (prefixWord ++ tailWord_234013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234017 : List Nat := [1, 2, 3, 2, 2, 1, 3, 6]
def baseStart_234017 : Nat := 118140960795 + 234017 * 2 ^ 59
def prefixEnd_234017 : Nat := 4983230072969 + 3 ^ 40 * 234017 * 2
def baseEnd_234017 : Nat := 35603911799501078847787

theorem tailTrace_234017 : CollatzResearch.WordTrace tailWord_234017 prefixEnd_234017 35603911799501078847787 := by
  unfold tailWord_234017
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535301193203850766780305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5690200795469233844520203 8535301193203850766780305)
  ·
    refine ⟨6401475894902888075085229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8535301193203850766780305 6401475894902888075085229)
    ·
      refine ⟨2400553460588583028156961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6401475894902888075085229 2400553460588583028156961)
      ·
        refine ⟨1800415095441437271117721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2400553460588583028156961 1800415095441437271117721)
        ·
          refine ⟨1350311321581077953338291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800415095441437271117721 1350311321581077953338291)
          ·
            refine ⟨2025466982371616930007437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350311321581077953338291 2025466982371616930007437)
            ·
              refine ⟨759550118389356348752789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2025466982371616930007437 759550118389356348752789)
              ·
                refine ⟨35603911799501078847787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 759550118389356348752789 35603911799501078847787)
                ·
                  rfl

theorem cell20_234017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_234017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234017 prefixEnd_234017 := by exact prefixLift 234017
  have htrace : WordTrace (prefixWord ++ tailWord_234017) baseStart_234017 baseEnd_234017 := by
    simpa [prefixWord, tailWord_234017, baseEnd_234017] using wordTrace_append hprefix tailTrace_234017
  have hstable : (prefixWord ++ tailWord_234017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234017).length < 2 ^ (prefixWord ++ tailWord_234017).sum := by decide
  have hdescent : baseEnd_234017 < baseStart_234017 := by decide
  rcases family_descends (prefixWord ++ tailWord_234017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234041 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 3]
def baseStart_234041 : Nat := 118140960795 + 234041 * 2 ^ 59
def prefixEnd_234041 : Nat := 4983230072969 + 3 ^ 40 * 234041 * 2
def baseEnd_234041 : Nat := 106822689652465819743263

theorem tailTrace_234041 : CollatzResearch.WordTrace tailWord_234041 prefixEnd_234041 106822689652465819743263 := by
  unfold tailWord_234041
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536176545116902865653977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5690784363411268577102651 8536176545116902865653977)
  ·
    refine ⟨6402132408837677149240483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8536176545116902865653977 6402132408837677149240483)
    ·
      refine ⟨9603198613256515723860725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402132408837677149240483 9603198613256515723860725)
      ·
        refine ⟨900299869992798349111943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9603198613256515723860725 900299869992798349111943)
        ·
          refine ⟨1350449804989197523667915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900299869992798349111943 1350449804989197523667915)
          ·
            refine ⟨2025674707483796285501873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350449804989197523667915 2025674707483796285501873)
            ·
              refine ⟨1519256030612847214126405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025674707483796285501873 1519256030612847214126405)
              ·
                refine ⟨284860505739908852648701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1519256030612847214126405 284860505739908852648701)
                ·
                  refine ⟨106822689652465819743263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284860505739908852648701 106822689652465819743263)
                  ·
                    rfl

theorem cell20_234041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_234041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234041 prefixEnd_234041 := by exact prefixLift 234041
  have htrace : WordTrace (prefixWord ++ tailWord_234041) baseStart_234041 baseEnd_234041 := by
    simpa [prefixWord, tailWord_234041, baseEnd_234041] using wordTrace_append hprefix tailTrace_234041
  have hstable : (prefixWord ++ tailWord_234041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234041).length < 2 ^ (prefixWord ++ tailWord_234041).sum := by decide
  have hdescent : baseEnd_234041 < baseStart_234041 := by decide
  rcases family_descends (prefixWord ++ tailWord_234041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234048 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_234048 : Nat := 118140960795 + 234048 * 2 ^ 59
def prefixEnd_234048 : Nat := 4983230072969 + 3 ^ 40 * 234048 * 2
def baseEnd_234048 : Nat := 106825884643204906509901

theorem tailTrace_234048 : CollatzResearch.WordTrace tailWord_234048 prefixEnd_234048 106825884643204906509901 := by
  unfold tailWord_234048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268215928045771530579399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5690954570727695374105865 4268215928045771530579399)
  ·
    refine ⟨6402323892068657295869099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4268215928045771530579399 6402323892068657295869099)
    ·
      refine ⟨9603485838102985943803649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402323892068657295869099 9603485838102985943803649)
      ·
        refine ⟨7202614378577239457852737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9603485838102985943803649 7202614378577239457852737)
        ·
          refine ⟨5401960783932929593389553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7202614378577239457852737 5401960783932929593389553)
          ·
            refine ⟨4051470587949697195042165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401960783932929593389553 4051470587949697195042165)
            ·
              refine ⟨379825367620284112035203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4051470587949697195042165 379825367620284112035203)
              ·
                refine ⟨569738051430426168052805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379825367620284112035203 569738051430426168052805)
                ·
                  refine ⟨106825884643204906509901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 569738051430426168052805 106825884643204906509901)
                  ·
                    rfl

theorem cell20_234048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_234048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234048 prefixEnd_234048 := by exact prefixLift 234048
  have htrace : WordTrace (prefixWord ++ tailWord_234048) baseStart_234048 baseEnd_234048 := by
    simpa [prefixWord, tailWord_234048, baseEnd_234048] using wordTrace_append hprefix tailTrace_234048
  have hstable : (prefixWord ++ tailWord_234048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234048).length < 2 ^ (prefixWord ++ tailWord_234048).sum := by decide
  have hdescent : baseEnd_234048 < baseStart_234048 := by decide
  rcases family_descends (prefixWord ++ tailWord_234048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234054 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_234054 : Nat := 118140960795 + 234054 * 2 ^ 59
def prefixEnd_234054 : Nat := 4983230072969 + 3 ^ 40 * 234054 * 2
def baseEnd_234054 : Nat := 106828623206695552309877

theorem tailTrace_234054 : CollatzResearch.WordTrace tailWord_234054 prefixEnd_234054 106828623206695552309877 := by
  unfold tailWord_234054
  simp only [CollatzResearch.WordTrace]
  refine ⟨266770334189681440183663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5691100462713204057251477 266770334189681440183663)
  ·
    refine ⟨400155501284522160275495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266770334189681440183663 400155501284522160275495)
    ·
      refine ⟨600233251926783240413243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400155501284522160275495 600233251926783240413243)
      ·
        refine ⟨900349877890174860619865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600233251926783240413243 900349877890174860619865)
        ·
          refine ⟨675262408417631145464899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900349877890174860619865 675262408417631145464899)
          ·
            refine ⟨1012893612626446718197349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675262408417631145464899 1012893612626446718197349)
            ·
              refine ⟨189917552367458759662003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1012893612626446718197349 189917552367458759662003)
              ·
                refine ⟨284876328551188139493005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189917552367458759662003 284876328551188139493005)
                ·
                  refine ⟨106828623206695552309877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284876328551188139493005 106828623206695552309877)
                  ·
                    rfl

theorem cell20_234054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_234054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234054 prefixEnd_234054 := by exact prefixLift 234054
  have htrace : WordTrace (prefixWord ++ tailWord_234054) baseStart_234054 baseEnd_234054 := by
    simpa [prefixWord, tailWord_234054, baseEnd_234054] using wordTrace_append hprefix tailTrace_234054
  have hstable : (prefixWord ++ tailWord_234054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234054).length < 2 ^ (prefixWord ++ tailWord_234054).sum := by decide
  have hdescent : baseEnd_234054 < baseStart_234054 := by decide
  rcases family_descends (prefixWord ++ tailWord_234054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234055 : List Nat := [1, 1, 4, 1, 4, 1, 1, 7]
def baseStart_234055 : Nat := 118140960795 + 234055 * 2 ^ 59
def prefixEnd_234055 : Nat := 4983230072969 + 3 ^ 40 * 234055 * 2
def baseEnd_234055 : Nat := 35609693211314664425513

theorem tailTrace_234055 : CollatzResearch.WordTrace tailWord_234055 prefixEnd_234055 35609693211314664425513 := by
  unfold tailWord_234055
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536687167066183256663619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5691124778044122171109079 8536687167066183256663619)
  ·
    refine ⟨12805030750599274884995429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8536687167066183256663619 12805030750599274884995429)
    ·
      refine ⟨2400943265737364040936643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12805030750599274884995429 2400943265737364040936643)
      ·
        refine ⟨3601414898606046061404965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400943265737364040936643 3601414898606046061404965)
        ·
          refine ⟨675265293488633636513431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3601414898606046061404965 675265293488633636513431)
          ·
            refine ⟨1012897940232950454770147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675265293488633636513431 1012897940232950454770147)
            ·
              refine ⟨1519346910349425682155221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012897940232950454770147 1519346910349425682155221)
              ·
                refine ⟨35609693211314664425513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1519346910349425682155221 35609693211314664425513)
                ·
                  rfl

theorem cell20_234055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_234055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234055 prefixEnd_234055 := by exact prefixLift 234055
  have htrace : WordTrace (prefixWord ++ tailWord_234055) baseStart_234055 baseEnd_234055 := by
    simpa [prefixWord, tailWord_234055, baseEnd_234055] using wordTrace_append hprefix tailTrace_234055
  have hstable : (prefixWord ++ tailWord_234055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234055).length < 2 ^ (prefixWord ++ tailWord_234055).sum := by decide
  have hdescent : baseEnd_234055 < baseStart_234055 := by decide
  rcases family_descends (prefixWord ++ tailWord_234055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234058 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_234058 : Nat := 118140960795 + 234058 * 2 ^ 59
def prefixEnd_234058 : Nat := 4983230072969 + 3 ^ 40 * 234058 * 2
def baseEnd_234058 : Nat := 106830448915689316176527

theorem tailTrace_234058 : CollatzResearch.WordTrace tailWord_234058 prefixEnd_234058 106830448915689316176527 := by
  unfold tailWord_234058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134199146513828692255707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5691197724036876512681885 2134199146513828692255707)
  ·
    refine ⟨3201298719770743038383561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2134199146513828692255707 3201298719770743038383561)
    ·
      refine ⟨2400974039828057278787671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3201298719770743038383561 2400974039828057278787671)
      ·
        refine ⟨3601461059742085918181507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400974039828057278787671 3601461059742085918181507)
        ·
          refine ⟨5402191589613128877272261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3601461059742085918181507 5402191589613128877272261)
          ·
            refine ⟨1012910923052461664488549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5402191589613128877272261 1012910923052461664488549)
            ·
              refine ⟨189920798072336562091603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1012910923052461664488549 189920798072336562091603)
              ·
                refine ⟨284881197108504843137405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189920798072336562091603 284881197108504843137405)
                ·
                  refine ⟨106830448915689316176527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284881197108504843137405 106830448915689316176527)
                  ·
                    rfl

theorem cell20_234058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_234058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234058 prefixEnd_234058 := by exact prefixLift 234058
  have htrace : WordTrace (prefixWord ++ tailWord_234058) baseStart_234058 baseEnd_234058 := by
    simpa [prefixWord, tailWord_234058, baseEnd_234058] using wordTrace_append hprefix tailTrace_234058
  have hstable : (prefixWord ++ tailWord_234058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234058).length < 2 ^ (prefixWord ++ tailWord_234058).sum := by decide
  have hdescent : baseEnd_234058 < baseStart_234058 := by decide
  rcases family_descends (prefixWord ++ tailWord_234058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234093 : List Nat := [1, 5, 1, 1, 3, 9]
def baseStart_234093 : Nat := 118140960795 + 234093 * 2 ^ 59
def prefixEnd_234093 : Nat := 4983230072969 + 3 ^ 40 * 234093 * 2
def baseEnd_234093 : Nat := 3957274958125361111471

theorem tailTrace_234093 : CollatzResearch.WordTrace tailWord_234093 prefixEnd_234093 3957274958125361111471 := by
  unfold tailWord_234093
  simp only [CollatzResearch.WordTrace]
  refine ⟨8538073140928515746546933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5692048760619010497697955 8538073140928515746546933)
  ·
    refine ⟨800444356962048351238775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8538073140928515746546933 800444356962048351238775)
    ·
      refine ⟨1200666535443072526858163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800444356962048351238775 1200666535443072526858163)
      ·
        refine ⟨1800999803164608790287245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200666535443072526858163 1800999803164608790287245)
        ·
          refine ⟨675374926186728296357717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1800999803164608790287245 675374926186728296357717)
          ·
            refine ⟨3957274958125361111471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 675374926186728296357717 3957274958125361111471)
            ·
              rfl

theorem cell20_234093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 9].length) (baseStart_234093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234093 prefixEnd_234093 := by exact prefixLift 234093
  have htrace : WordTrace (prefixWord ++ tailWord_234093) baseStart_234093 baseEnd_234093 := by
    simpa [prefixWord, tailWord_234093, baseEnd_234093] using wordTrace_append hprefix tailTrace_234093
  have hstable : (prefixWord ++ tailWord_234093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234093).length < 2 ^ (prefixWord ++ tailWord_234093).sum := by decide
  have hdescent : baseEnd_234093 < baseStart_234093 := by decide
  rcases family_descends (prefixWord ++ tailWord_234093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234096 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_234096 : Nat := 118140960795 + 234096 * 2 ^ 59
def prefixEnd_234096 : Nat := 4983230072969 + 3 ^ 40 * 234096 * 2
def baseEnd_234096 : Nat := 106847793151130072909705

theorem tailTrace_234096 : CollatzResearch.WordTrace tailWord_234096 prefixEnd_234096 106847793151130072909705 := by
  unfold tailWord_234096
  simp only [CollatzResearch.WordTrace]
  refine ⟨4269091279958823629453071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5692121706611764839270761 4269091279958823629453071)
  ·
    refine ⟨6403636919938235444179607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4269091279958823629453071 6403636919938235444179607)
    ·
      refine ⟨9605455379907353166269411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6403636919938235444179607 9605455379907353166269411)
      ·
        refine ⟨14408183069861029749404117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9605455379907353166269411 14408183069861029749404117)
        ·
          refine ⟨337691790699867884751659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14408183069861029749404117 337691790699867884751659)
          ·
            refine ⟨506537686049801827127489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337691790699867884751659 506537686049801827127489)
            ·
              refine ⟨379903264537351370345617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506537686049801827127489 379903264537351370345617)
              ·
                refine ⟨284927448403013527759213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379903264537351370345617 284927448403013527759213)
                ·
                  refine ⟨106847793151130072909705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284927448403013527759213 106847793151130072909705)
                  ·
                    rfl

theorem cell20_234096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_234096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234096 prefixEnd_234096 := by exact prefixLift 234096
  have htrace : WordTrace (prefixWord ++ tailWord_234096) baseStart_234096 baseEnd_234096 := by
    simpa [prefixWord, tailWord_234096, baseEnd_234096] using wordTrace_append hprefix tailTrace_234096
  have hstable : (prefixWord ++ tailWord_234096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234096).length < 2 ^ (prefixWord ++ tailWord_234096).sum := by decide
  have hdescent : baseEnd_234096 < baseStart_234096 := by decide
  rcases family_descends (prefixWord ++ tailWord_234096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234117 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 3]
def baseStart_234117 : Nat := 118140960795 + 234117 * 2 ^ 59
def prefixEnd_234117 : Nat := 4983230072969 + 3 ^ 40 * 234117 * 2
def baseEnd_234117 : Nat := 106857378123347333209619

theorem tailTrace_234117 : CollatzResearch.WordTrace tailWord_234117 prefixEnd_234117 106857378123347333209619 := by
  unfold tailWord_234117
  simp only [CollatzResearch.WordTrace]
  refine ⟨8538948492841567845420605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5692632328561045230280403 8538948492841567845420605)
  ·
    refine ⟨3202105684815587942032727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8538948492841567845420605 3202105684815587942032727)
    ·
      refine ⟨4803158527223381913049091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202105684815587942032727 4803158527223381913049091)
      ·
        refine ⟨7204737790835072869573637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803158527223381913049091 7204737790835072869573637)
        ·
          refine ⟨1350888335781576163045057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7204737790835072869573637 1350888335781576163045057)
          ·
            refine ⟨1013166251836182122283793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350888335781576163045057 1013166251836182122283793)
            ·
              refine ⟨759874688877136591712845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013166251836182122283793 759874688877136591712845)
              ·
                refine ⟨284953008328926221892317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759874688877136591712845 284953008328926221892317)
                ·
                  refine ⟨106857378123347333209619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284953008328926221892317 106857378123347333209619)
                  ·
                    rfl

theorem cell20_234117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_234117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234117 prefixEnd_234117 := by exact prefixLift 234117
  have htrace : WordTrace (prefixWord ++ tailWord_234117) baseStart_234117 baseEnd_234117 := by
    simpa [prefixWord, tailWord_234117, baseEnd_234117] using wordTrace_append hprefix tailTrace_234117
  have hstable : (prefixWord ++ tailWord_234117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234117).length < 2 ^ (prefixWord ++ tailWord_234117).sum := by decide
  have hdescent : baseEnd_234117 < baseStart_234117 := by decide
  rcases family_descends (prefixWord ++ tailWord_234117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234141 : List Nat := [1, 4, 2, 1, 1, 1, 3, 5, 2]
def baseStart_234141 : Nat := 118140960795 + 234141 * 2 ^ 59
def prefixEnd_234141 : Nat := 4983230072969 + 3 ^ 40 * 234141 * 2
def baseEnd_234141 : Nat := 106868332377309916409521

theorem tailTrace_234141 : CollatzResearch.WordTrace tailWord_234141 prefixEnd_234141 106868332377309916409521 := by
  unfold tailWord_234141
  simp only [CollatzResearch.WordTrace]
  refine ⟨8539823844754619944294277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5693215896503079962862851 8539823844754619944294277)
  ·
    refine ⟨1601216970891491239555177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8539823844754619944294277 1601216970891491239555177)
    ·
      refine ⟨1200912728168618429666383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1601216970891491239555177 1200912728168618429666383)
      ·
        refine ⟨1801369092252927644499575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200912728168618429666383 1801369092252927644499575)
        ·
          refine ⟨2702053638379391466749363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801369092252927644499575 2702053638379391466749363)
          ·
            refine ⟨4053080457569087200124045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702053638379391466749363 4053080457569087200124045)
            ·
              refine ⟨1519905171588407700046517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4053080457569087200124045 1519905171588407700046517)
              ·
                refine ⟨142491109836413221879361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519905171588407700046517 142491109836413221879361)
                ·
                  refine ⟨106868332377309916409521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142491109836413221879361 106868332377309916409521)
                  ·
                    rfl

theorem cell20_234141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_234141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234141 prefixEnd_234141 := by exact prefixLift 234141
  have htrace : WordTrace (prefixWord ++ tailWord_234141) baseStart_234141 baseEnd_234141 := by
    simpa [prefixWord, tailWord_234141, baseEnd_234141] using wordTrace_append hprefix tailTrace_234141
  have hstable : (prefixWord ++ tailWord_234141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234141).length < 2 ^ (prefixWord ++ tailWord_234141).sum := by decide
  have hdescent : baseEnd_234141 < baseStart_234141 := by decide
  rcases family_descends (prefixWord ++ tailWord_234141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234158 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_234158 : Nat := 118140960795 + 234158 * 2 ^ 59
def prefixEnd_234158 : Nat := 4983230072969 + 3 ^ 40 * 234158 * 2
def baseEnd_234158 : Nat := 106876091640533412842785

theorem tailTrace_234158 : CollatzResearch.WordTrace tailWord_234158 prefixEnd_234158 106876091640533412842785 := by
  unfold tailWord_234158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067555485711628980957891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5693629257128687898442085 1067555485711628980957891)
  ·
    refine ⟨1601333228567443471436837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1067555485711628980957891 1601333228567443471436837)
    ·
      refine ⟨300249980356395650894407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1601333228567443471436837 300249980356395650894407)
      ·
        refine ⟨450374970534593476341611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300249980356395650894407 450374970534593476341611)
        ·
          refine ⟨675562455801890214512417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450374970534593476341611 675562455801890214512417)
          ·
            refine ⟨506671841851417660884313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675562455801890214512417 506671841851417660884313)
            ·
              refine ⟨380003881388563245663235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506671841851417660884313 380003881388563245663235)
              ·
                refine ⟨570005822082844868494853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380003881388563245663235 570005822082844868494853)
                ·
                  refine ⟨106876091640533412842785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570005822082844868494853 106876091640533412842785)
                  ·
                    rfl

theorem cell20_234158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_234158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234158 prefixEnd_234158 := by exact prefixLift 234158
  have htrace : WordTrace (prefixWord ++ tailWord_234158) baseStart_234158 baseEnd_234158 := by
    simpa [prefixWord, tailWord_234158, baseEnd_234158] using wordTrace_append hprefix tailTrace_234158
  have hstable : (prefixWord ++ tailWord_234158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234158).length < 2 ^ (prefixWord ++ tailWord_234158).sum := by decide
  have hdescent : baseEnd_234158 < baseStart_234158 := by decide
  rcases family_descends (prefixWord ++ tailWord_234158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234172 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_234172 : Nat := 118140960795 + 234172 * 2 ^ 59
def prefixEnd_234172 : Nat := 4983230072969 + 3 ^ 40 * 234172 * 2
def baseEnd_234172 : Nat := 106882481622011586376061

theorem tailTrace_234172 : CollatzResearch.WordTrace tailWord_234172 prefixEnd_234172 106882481622011586376061 := by
  unfold tailWord_234172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4270477253821156119336385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5693969671761541492448513 4270477253821156119336385)
  ·
    refine ⟨3202857940365867089502289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4270477253821156119336385 3202857940365867089502289)
    ·
      refine ⟨2402143455274400317126717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3202857940365867089502289 2402143455274400317126717)
      ·
        refine ⟨900803795727900118922519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2402143455274400317126717 900803795727900118922519)
        ·
          refine ⟨1351205693591850178383779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900803795727900118922519 1351205693591850178383779)
          ·
            refine ⟨2026808540387775267575669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351205693591850178383779 2026808540387775267575669)
            ·
              refine ⟨190013300661353931335219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2026808540387775267575669 190013300661353931335219)
              ·
                refine ⟨285019950992030897002829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190013300661353931335219 285019950992030897002829)
                ·
                  refine ⟨106882481622011586376061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285019950992030897002829 106882481622011586376061)
                  ·
                    rfl

theorem cell20_234172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_234172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234172 prefixEnd_234172 := by exact prefixLift 234172
  have htrace : WordTrace (prefixWord ++ tailWord_234172) baseStart_234172 baseEnd_234172 := by
    simpa [prefixWord, tailWord_234172, baseEnd_234172] using wordTrace_append hprefix tailTrace_234172
  have hstable : (prefixWord ++ tailWord_234172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234172).length < 2 ^ (prefixWord ++ tailWord_234172).sum := by decide
  have hdescent : baseEnd_234172 < baseStart_234172 := by decide
  rcases family_descends (prefixWord ++ tailWord_234172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234182 : List Nat := [6, 1, 2, 1, 2, 1, 1, 6]
def baseStart_234182 : Nat := 118140960795 + 234182 * 2 ^ 59
def prefixEnd_234182 : Nat := 4983230072969 + 3 ^ 40 * 234182 * 2
def baseEnd_234182 : Nat := 35629015298165332014229

theorem tailTrace_234182 : CollatzResearch.WordTrace tailWord_234182 prefixEnd_234182 35629015298165332014229 := by
  unfold tailWord_234182
  simp only [CollatzResearch.WordTrace]
  refine ⟨266916226175190123329275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5694212825070722631024533 266916226175190123329275)
  ·
    refine ⟨400374339262785184993913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266916226175190123329275 400374339262785184993913)
    ·
      refine ⟨300280754447088888745435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400374339262785184993913 300280754447088888745435)
      ·
        refine ⟨450421131670633333118153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300280754447088888745435 450421131670633333118153)
        ·
          refine ⟨337815848752974999838615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450421131670633333118153 337815848752974999838615)
          ·
            refine ⟨506723773129462499757923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337815848752974999838615 506723773129462499757923)
            ·
              refine ⟨760085659694193749636885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506723773129462499757923 760085659694193749636885)
              ·
                refine ⟨35629015298165332014229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 760085659694193749636885 35629015298165332014229)
                ·
                  rfl

theorem cell20_234182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_234182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234182 prefixEnd_234182 := by exact prefixLift 234182
  have htrace : WordTrace (prefixWord ++ tailWord_234182) baseStart_234182 baseEnd_234182 := by
    simpa [prefixWord, tailWord_234182, baseEnd_234182] using wordTrace_append hprefix tailTrace_234182
  have hstable : (prefixWord ++ tailWord_234182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234182).length < 2 ^ (prefixWord ++ tailWord_234182).sum := by decide
  have hdescent : baseEnd_234182 < baseStart_234182 := by decide
  rcases family_descends (prefixWord ++ tailWord_234182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234183 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_234183 : Nat := 118140960795 + 234183 * 2 ^ 59
def prefixEnd_234183 : Nat := 4983230072969 + 3 ^ 40 * 234183 * 2
def baseEnd_234183 : Nat := 106887502321744437009349

theorem tailTrace_234183 : CollatzResearch.WordTrace tailWord_234183 prefixEnd_234183 106887502321744437009349 := by
  unfold tailWord_234183
  simp only [CollatzResearch.WordTrace]
  refine ⟨8541355710602461117323203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5694237140401640744882135 8541355710602461117323203)
  ·
    refine ⟨12812033565903691675984805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8541355710602461117323203 12812033565903691675984805)
    ·
      refine ⟨2402256293606942189247151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12812033565903691675984805 2402256293606942189247151)
      ·
        refine ⟨3603384440410413283870727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402256293606942189247151 3603384440410413283870727)
        ·
          refine ⟨5405076660615619925806091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603384440410413283870727 5405076660615619925806091)
          ·
            refine ⟨8107614990923429888709137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405076660615619925806091 8107614990923429888709137)
            ·
              refine ⟨6080711243192572416531853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8107614990923429888709137 6080711243192572416531853)
              ·
                refine ⟨2280266716197214656199445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6080711243192572416531853 2280266716197214656199445)
                ·
                  refine ⟨106887502321744437009349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2280266716197214656199445 106887502321744437009349)
                  ·
                    rfl

theorem cell20_234183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_234183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234183 prefixEnd_234183 := by exact prefixLift 234183
  have htrace : WordTrace (prefixWord ++ tailWord_234183) baseStart_234183 baseEnd_234183 := by
    simpa [prefixWord, tailWord_234183, baseEnd_234183] using wordTrace_append hprefix tailTrace_234183
  have hstable : (prefixWord ++ tailWord_234183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234183).length < 2 ^ (prefixWord ++ tailWord_234183).sum := by decide
  have hdescent : baseEnd_234183 < baseStart_234183 := by decide
  rcases family_descends (prefixWord ++ tailWord_234183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234186 : List Nat := [3, 1, 2, 1, 4, 1, 4, 4]
def baseStart_234186 : Nat := 118140960795 + 234186 * 2 ^ 59
def prefixEnd_234186 : Nat := 4983230072969 + 3 ^ 40 * 234186 * 2
def baseEnd_234186 : Nat := 35629623867829919969779

theorem tailTrace_234186 : CollatzResearch.WordTrace tailWord_234186 prefixEnd_234186 35629623867829919969779 := by
  unfold tailWord_234186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135366282397898157420603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5694310086394395086454941 2135366282397898157420603)
  ·
    refine ⟨3203049423596847236130905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2135366282397898157420603 3203049423596847236130905)
    ·
      refine ⟨2402287067697635427098179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3203049423596847236130905 2402287067697635427098179)
      ·
        refine ⟨3603430601546453140647269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402287067697635427098179 3603430601546453140647269)
        ·
          refine ⟨675643237789959963871363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3603430601546453140647269 675643237789959963871363)
          ·
            refine ⟨1013464856684939945807045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675643237789959963871363 1013464856684939945807045)
            ·
              refine ⟨190024660628426239838821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1013464856684939945807045 190024660628426239838821)
              ·
                refine ⟨35629623867829919969779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190024660628426239838821 35629623867829919969779)
                ·
                  rfl

theorem cell20_234186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_234186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234186 prefixEnd_234186 := by exact prefixLift 234186
  have htrace : WordTrace (prefixWord ++ tailWord_234186) baseStart_234186 baseEnd_234186 := by
    simpa [prefixWord, tailWord_234186, baseEnd_234186] using wordTrace_append hprefix tailTrace_234186
  have hstable : (prefixWord ++ tailWord_234186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234186).length < 2 ^ (prefixWord ++ tailWord_234186).sum := by decide
  have hdescent : baseEnd_234186 < baseStart_234186 := by decide
  rcases family_descends (prefixWord ++ tailWord_234186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234207 : List Nat := [1, 1, 2, 3, 2, 5, 6]
def baseStart_234207 : Nat := 118140960795 + 234207 * 2 ^ 59
def prefixEnd_234207 : Nat := 4983230072969 + 3 ^ 40 * 234207 * 2
def baseEnd_234207 : Nat := 11877606286189668912139

theorem tailTrace_234207 : CollatzResearch.WordTrace tailWord_234207 prefixEnd_234207 11877606286189668912139 := by
  unfold tailWord_234207
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542231062515513216196875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5694820708343675477464583 8542231062515513216196875)
  ·
    refine ⟨12813346593773269824295313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8542231062515513216196875 12813346593773269824295313)
    ·
      refine ⟨9610009945329952368221485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12813346593773269824295313 9610009945329952368221485)
      ·
        refine ⟨3603753729498732138083057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9610009945329952368221485 3603753729498732138083057)
        ·
          refine ⟨2702815297124049103562293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3603753729498732138083057 2702815297124049103562293)
          ·
            refine ⟨253388934105379603458965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2702815297124049103562293 253388934105379603458965)
            ·
              refine ⟨11877606286189668912139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 253388934105379603458965 11877606286189668912139)
              ·
                rfl

theorem cell20_234207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 6].length) (baseStart_234207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234207 prefixEnd_234207 := by exact prefixLift 234207
  have htrace : WordTrace (prefixWord ++ tailWord_234207) baseStart_234207 baseEnd_234207 := by
    simpa [prefixWord, tailWord_234207, baseEnd_234207] using wordTrace_append hprefix tailTrace_234207
  have hstable : (prefixWord ++ tailWord_234207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234207).length < 2 ^ (prefixWord ++ tailWord_234207).sum := by decide
  have hdescent : baseEnd_234207 < baseStart_234207 := by decide
  rcases family_descends (prefixWord ++ tailWord_234207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234272 : List Nat := [2, 1, 1, 5, 1, 2, 4, 2, 2]
def baseStart_234272 : Nat := 118140960795 + 234272 * 2 ^ 59
def prefixEnd_234272 : Nat := 4983230072969 + 3 ^ 40 * 234272 * 2
def baseEnd_234272 : Nat := 106928124346855683042319

theorem tailTrace_234272 : CollatzResearch.WordTrace tailWord_234272 prefixEnd_234272 106928124346855683042319 := by
  unfold tailWord_234272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4272300903640014658656535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5696401204853352878208713 4272300903640014658656535)
  ·
    refine ⟨6408451355460021987984803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4272300903640014658656535 6408451355460021987984803)
    ·
      refine ⟨9612677033190032981977205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6408451355460021987984803 9612677033190032981977205)
      ·
        refine ⟨901188471861565592060363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9612677033190032981977205 901188471861565592060363)
        ·
          refine ⟨1351782707792348388090545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901188471861565592060363 1351782707792348388090545)
          ·
            refine ⟨1013837030844261291067909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351782707792348388090545 1013837030844261291067909)
            ·
              refine ⟨190094443283298992075233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1013837030844261291067909 190094443283298992075233)
              ·
                refine ⟨142570832462474244056425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190094443283298992075233 142570832462474244056425)
                ·
                  refine ⟨106928124346855683042319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142570832462474244056425 106928124346855683042319)
                  ·
                    rfl

theorem cell20_234272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_234272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234272 prefixEnd_234272 := by exact prefixLift 234272
  have htrace : WordTrace (prefixWord ++ tailWord_234272) baseStart_234272 baseEnd_234272 := by
    simpa [prefixWord, tailWord_234272, baseEnd_234272] using wordTrace_append hprefix tailTrace_234272
  have hstable : (prefixWord ++ tailWord_234272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234272).length < 2 ^ (prefixWord ++ tailWord_234272).sum := by decide
  have hdescent : baseEnd_234272 < baseStart_234272 := by decide
  rcases family_descends (prefixWord ++ tailWord_234272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234286 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_234286 : Nat := 118140960795 + 234286 * 2 ^ 59
def prefixEnd_234286 : Nat := 4983230072969 + 3 ^ 40 * 234286 * 2
def baseEnd_234286 : Nat := 106934514328333856575595

theorem tailTrace_234286 : CollatzResearch.WordTrace tailWord_234286 prefixEnd_234286 106934514328333856575595 := by
  unfold tailWord_234286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068139053653663713540339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5696741619486206472215141 1068139053653663713540339)
  ·
    refine ⟨1602208580480495570310509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068139053653663713540339 1602208580480495570310509)
    ·
      refine ⟨600828217680185838866441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1602208580480495570310509 600828217680185838866441)
      ·
        refine ⟨450621163260139379149831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600828217680185838866441 450621163260139379149831)
        ·
          refine ⟨675931744890209068724747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450621163260139379149831 675931744890209068724747)
          ·
            refine ⟨1013897617335313603087121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675931744890209068724747 1013897617335313603087121)
            ·
              refine ⟨760423213001485202315341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013897617335313603087121 760423213001485202315341)
              ·
                refine ⟨285158704875556950868253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 760423213001485202315341 285158704875556950868253)
                ·
                  refine ⟨106934514328333856575595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285158704875556950868253 106934514328333856575595)
                  ·
                    rfl

theorem cell20_234286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_234286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234286 prefixEnd_234286 := by exact prefixLift 234286
  have htrace : WordTrace (prefixWord ++ tailWord_234286) baseStart_234286 baseEnd_234286 := by
    simpa [prefixWord, tailWord_234286, baseEnd_234286] using wordTrace_append hprefix tailTrace_234286
  have hstable : (prefixWord ++ tailWord_234286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234286).length < 2 ^ (prefixWord ++ tailWord_234286).sum := by decide
  have hdescent : baseEnd_234286 < baseStart_234286 := by decide
  rcases family_descends (prefixWord ++ tailWord_234286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234304 : List Nat := [2, 1, 1, 2, 2, 1, 1, 10]
def baseStart_234304 : Nat := 118140960795 + 234304 * 2 ^ 59
def prefixEnd_234304 : Nat := 4983230072969 + 3 ^ 40 * 234304 * 2
def baseEnd_234304 : Nat := 35647576672935264658507

theorem tailTrace_234304 : CollatzResearch.WordTrace tailWord_234304 prefixEnd_234304 35647576672935264658507 := by
  unfold tailWord_234304
  simp only [CollatzResearch.WordTrace]
  refine ⟨4272884471582049391238983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5697179295442732521651977 4272884471582049391238983)
  ·
    refine ⟨6409326707373074086858475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4272884471582049391238983 6409326707373074086858475)
    ·
      refine ⟨9613990061059611130287713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6409326707373074086858475 9613990061059611130287713)
      ·
        refine ⟨7210492545794708347715785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9613990061059611130287713 7210492545794708347715785)
        ·
          refine ⟨5407869409346031260786839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7210492545794708347715785 5407869409346031260786839)
          ·
            refine ⟨8111804114019046891180259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407869409346031260786839 8111804114019046891180259)
            ·
              refine ⟨12167706171028570336770389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8111804114019046891180259 12167706171028570336770389)
              ·
                refine ⟨35647576672935264658507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12167706171028570336770389 35647576672935264658507)
                ·
                  rfl

theorem cell20_234304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_234304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234304 prefixEnd_234304 := by exact prefixLift 234304
  have htrace : WordTrace (prefixWord ++ tailWord_234304) baseStart_234304 baseEnd_234304 := by
    simpa [prefixWord, tailWord_234304, baseEnd_234304] using wordTrace_append hprefix tailTrace_234304
  have hstable : (prefixWord ++ tailWord_234304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234304).length < 2 ^ (prefixWord ++ tailWord_234304).sum := by decide
  have hdescent : baseEnd_234304 < baseStart_234304 := by decide
  rcases family_descends (prefixWord ++ tailWord_234304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234321 : List Nat := [1, 2, 2, 1, 6, 1, 7]
def baseStart_234321 : Nat := 118140960795 + 234321 * 2 ^ 59
def prefixEnd_234321 : Nat := 4983230072969 + 3 ^ 40 * 234321 * 2
def baseEnd_234321 : Nat := 11883387698003254489865

theorem tailTrace_234321 : CollatzResearch.WordTrace tailWord_234321 prefixEnd_234321 11883387698003254489865 := by
  unfold tailWord_234321
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546388984102510685846817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5697592656068340457231211 8546388984102510685846817)
  ·
    refine ⟨6409791738076883014385113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8546388984102510685846817 6409791738076883014385113)
    ·
      refine ⟨4807343803557662260788835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6409791738076883014385113 4807343803557662260788835)
      ·
        refine ⟨7211015705336493391183253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807343803557662260788835 7211015705336493391183253)
        ·
          refine ⟨338016361187648127711715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7211015705336493391183253 338016361187648127711715)
          ·
            refine ⟨507024541781472191567573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338016361187648127711715 507024541781472191567573)
            ·
              refine ⟨11883387698003254489865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 507024541781472191567573 11883387698003254489865)
              ·
                rfl

theorem cell20_234321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 7].length) (baseStart_234321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234321 prefixEnd_234321 := by exact prefixLift 234321
  have htrace : WordTrace (prefixWord ++ tailWord_234321) baseStart_234321 baseEnd_234321 := by
    simpa [prefixWord, tailWord_234321, baseEnd_234321] using wordTrace_append hprefix tailTrace_234321
  have hstable : (prefixWord ++ tailWord_234321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234321).length < 2 ^ (prefixWord ++ tailWord_234321).sum := by decide
  have hdescent : baseEnd_234321 < baseStart_234321 := by decide
  rcases family_descends (prefixWord ++ tailWord_234321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234380 : List Nat := [2, 2, 1, 2, 1, 2, 10]
def baseStart_234380 : Nat := 118140960795 + 234380 * 2 ^ 59
def prefixEnd_234380 : Nat := 4983230072969 + 3 ^ 40 * 234380 * 2
def baseEnd_234380 : Nat := 11886379832187478604653

theorem tailTrace_234380 : CollatzResearch.WordTrace tailWord_234380 prefixEnd_234380 11886379832187478604653 := by
  unfold tailWord_234380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4274270445444381881122297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5699027260592509174829729 4274270445444381881122297)
  ·
    refine ⟨3205702834083286410841723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4274270445444381881122297 3205702834083286410841723)
    ·
      refine ⟨4808554251124929616262585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205702834083286410841723 4808554251124929616262585)
      ·
        refine ⟨3606415688343697212196939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4808554251124929616262585 3606415688343697212196939)
        ·
          refine ⟨5409623532515545818295409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606415688343697212196939 5409623532515545818295409)
          ·
            refine ⟨4057217649386659363721557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5409623532515545818295409 4057217649386659363721557)
            ·
              refine ⟨11886379832187478604653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4057217649386659363721557 11886379832187478604653)
              ·
                rfl

theorem cell20_234380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 10].length) (baseStart_234380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234380 prefixEnd_234380 := by exact prefixLift 234380
  have htrace : WordTrace (prefixWord ++ tailWord_234380) baseStart_234380 baseEnd_234380 := by
    simpa [prefixWord, tailWord_234380, baseEnd_234380] using wordTrace_append hprefix tailTrace_234380
  have hstable : (prefixWord ++ tailWord_234380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234380).length < 2 ^ (prefixWord ++ tailWord_234380).sum := by decide
  have hdescent : baseEnd_234380 < baseStart_234380 := by decide
  rcases family_descends (prefixWord ++ tailWord_234380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234386 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_234386 : Nat := 118140960795 + 234386 * 2 ^ 59
def prefixEnd_234386 : Nat := 4983230072969 + 3 ^ 40 * 234386 * 2
def baseEnd_234386 : Nat := 106980157053177953241853

theorem tailTrace_234386 : CollatzResearch.WordTrace tailWord_234386 prefixEnd_234386 106980157053177953241853 := by
  unfold tailWord_234386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137189932216756696740753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5699173152578017857975341 2137189932216756696740753)
  ·
    refine ⟨1602892449162567522555565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2137189932216756696740753 1602892449162567522555565)
    ·
      refine ⟨601084668435962820958337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1602892449162567522555565 601084668435962820958337)
      ·
        refine ⟨450813501326972115718753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601084668435962820958337 450813501326972115718753)
        ·
          refine ⟨338110125995229086789065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450813501326972115718753 338110125995229086789065)
          ·
            refine ⟨253582594496421815091799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338110125995229086789065 253582594496421815091799)
            ·
              refine ⟨380373891744632722637699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253582594496421815091799 380373891744632722637699)
              ·
                refine ⟨570560837616949083956549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380373891744632722637699 570560837616949083956549)
                ·
                  refine ⟨106980157053177953241853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570560837616949083956549 106980157053177953241853)
                  ·
                    rfl

theorem cell20_234386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_234386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234386 prefixEnd_234386 := by exact prefixLift 234386
  have htrace : WordTrace (prefixWord ++ tailWord_234386) baseStart_234386 baseEnd_234386 := by
    simpa [prefixWord, tailWord_234386, baseEnd_234386] using wordTrace_append hprefix tailTrace_234386
  have hstable : (prefixWord ++ tailWord_234386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234386).length < 2 ^ (prefixWord ++ tailWord_234386).sum := by decide
  have hdescent : baseEnd_234386 < baseStart_234386 := by decide
  rcases family_descends (prefixWord ++ tailWord_234386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234396 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 3]
def baseStart_234396 : Nat := 118140960795 + 234396 * 2 ^ 59
def prefixEnd_234396 : Nat := 4983230072969 + 3 ^ 40 * 234396 * 2
def baseEnd_234396 : Nat := 106984721325662362908479

theorem tailTrace_234396 : CollatzResearch.WordTrace tailWord_234396 prefixEnd_234396 106984721325662362908479 := by
  unfold tailWord_234396
  simp only [CollatzResearch.WordTrace]
  refine ⟨4274562229415399247413521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5699416305887198996551361 4274562229415399247413521)
  ·
    refine ⟨3205921672061549435560141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4274562229415399247413521 3205921672061549435560141)
    ·
      refine ⟨1202220627023081038335053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3205921672061549435560141 1202220627023081038335053)
      ·
        refine ⟨450832735133655389375645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1202220627023081038335053 450832735133655389375645)
        ·
          refine ⟨169062275675120771015867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450832735133655389375645 169062275675120771015867)
          ·
            refine ⟨253593413512681156523801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169062275675120771015867 253593413512681156523801)
            ·
              refine ⟨190195060134510867392851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253593413512681156523801 190195060134510867392851)
              ·
                refine ⟨285292590201766301089277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190195060134510867392851 285292590201766301089277)
                ·
                  refine ⟨106984721325662362908479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285292590201766301089277 106984721325662362908479)
                  ·
                    rfl

theorem cell20_234396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_234396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234396 prefixEnd_234396 := by exact prefixLift 234396
  have htrace : WordTrace (prefixWord ++ tailWord_234396) baseStart_234396 baseEnd_234396 := by
    simpa [prefixWord, tailWord_234396, baseEnd_234396] using wordTrace_append hprefix tailTrace_234396
  have hstable : (prefixWord ++ tailWord_234396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234396).length < 2 ^ (prefixWord ++ tailWord_234396).sum := by decide
  have hdescent : baseEnd_234396 < baseStart_234396 := by decide
  rcases family_descends (prefixWord ++ tailWord_234396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234397 : List Nat := [1, 4, 2, 1, 2, 1, 4, 5]
def baseStart_234397 : Nat := 118140960795 + 234397 * 2 ^ 59
def prefixEnd_234397 : Nat := 4983230072969 + 3 ^ 40 * 234397 * 2
def baseEnd_234397 : Nat := 35661725917636934625047

theorem tailTrace_234397 : CollatzResearch.WordTrace tailWord_234397 prefixEnd_234397 35661725917636934625047 := by
  unfold tailWord_234397
  simp only [CollatzResearch.WordTrace]
  refine ⟨8549160931827175665613445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5699440621218117110408963 8549160931827175665613445)
  ·
    refine ⟨1602967674717595437302521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8549160931827175665613445 1602967674717595437302521)
    ·
      refine ⟨1202225756038196577976891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1602967674717595437302521 1202225756038196577976891)
      ·
        refine ⟨1803338634057294866965337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202225756038196577976891 1803338634057294866965337)
        ·
          refine ⟨1352503975542971150224003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1803338634057294866965337 1352503975542971150224003)
          ·
            refine ⟨2028755963314456725336005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352503975542971150224003 2028755963314456725336005)
            ·
              refine ⟨380391743121460636000501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2028755963314456725336005 380391743121460636000501)
              ·
                refine ⟨35661725917636934625047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380391743121460636000501 35661725917636934625047)
                ·
                  rfl

theorem cell20_234397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_234397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234397 prefixEnd_234397 := by exact prefixLift 234397
  have htrace : WordTrace (prefixWord ++ tailWord_234397) baseStart_234397 baseEnd_234397 := by
    simpa [prefixWord, tailWord_234397, baseEnd_234397] using wordTrace_append hprefix tailTrace_234397
  have hstable : (prefixWord ++ tailWord_234397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234397).length < 2 ^ (prefixWord ++ tailWord_234397).sum := by decide
  have hdescent : baseEnd_234397 < baseStart_234397 := by decide
  rcases family_descends (prefixWord ++ tailWord_234397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234449 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_234449 : Nat := 118140960795 + 234449 * 2 ^ 59
def prefixEnd_234449 : Nat := 4983230072969 + 3 ^ 40 * 234449 * 2
def baseEnd_234449 : Nat := 107008911969829734141595

theorem tailTrace_234449 : CollatzResearch.WordTrace tailWord_234449 prefixEnd_234449 107008911969829734141595 := by
  unfold tailWord_234449
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551057527638788546506401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5700705018425859031004267 8551057527638788546506401)
  ·
    refine ⟨6413293145729091409879801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8551057527638788546506401 6413293145729091409879801)
    ·
      refine ⟨4809969859296818557409851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6413293145729091409879801 4809969859296818557409851)
      ·
        refine ⟨7214954788945227836114777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809969859296818557409851 7214954788945227836114777)
        ·
          refine ⟨5411216091708920877086083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7214954788945227836114777 5411216091708920877086083)
          ·
            refine ⟨8116824137563381315629125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411216091708920877086083 8116824137563381315629125)
            ·
              refine ⟨1521904525793133996680461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8116824137563381315629125 1521904525793133996680461)
              ·
                refine ⟨570714197172425248755173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1521904525793133996680461 570714197172425248755173)
                ·
                  refine ⟨107008911969829734141595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570714197172425248755173 107008911969829734141595)
                  ·
                    rfl

theorem cell20_234449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_234449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234449 prefixEnd_234449 := by exact prefixLift 234449
  have htrace : WordTrace (prefixWord ++ tailWord_234449) baseStart_234449 baseEnd_234449 := by
    simpa [prefixWord, tailWord_234449, baseEnd_234449] using wordTrace_append hprefix tailTrace_234449
  have hstable : (prefixWord ++ tailWord_234449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234449).length < 2 ^ (prefixWord ++ tailWord_234449).sum := by decide
  have hdescent : baseEnd_234449 < baseStart_234449 := by decide
  rcases family_descends (prefixWord ++ tailWord_234449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234452 : List Nat := [2, 4, 1, 2, 1, 4, 1, 5]
def baseStart_234452 : Nat := 118140960795 + 234452 * 2 ^ 59
def prefixEnd_234452 : Nat := 4983230072969 + 3 ^ 40 * 234452 * 2
def baseEnd_234452 : Nat := 35670093750525019013861

theorem tailTrace_234452 : CollatzResearch.WordTrace tailWord_234452 prefixEnd_234452 35670093750525019013861 := by
  unfold tailWord_234452
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275583473313960029432805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5700777964418613372577073 4275583473313960029432805)
  ·
    refine ⟨801671901246367505518651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4275583473313960029432805 801671901246367505518651)
    ·
      refine ⟨1202507851869551258277977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801671901246367505518651 1202507851869551258277977)
      ·
        refine ⟨901880888902163443708483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1202507851869551258277977 901880888902163443708483)
        ·
          refine ⟨1352821333353245165562725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901880888902163443708483 1352821333353245165562725)
          ·
            refine ⟨253654000003733468543011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1352821333353245165562725 253654000003733468543011)
            ·
              refine ⟨380481000005600202814517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253654000003733468543011 380481000005600202814517)
              ·
                refine ⟨35670093750525019013861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380481000005600202814517 35670093750525019013861)
                ·
                  rfl

theorem cell20_234452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_234452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234452 prefixEnd_234452 := by exact prefixLift 234452
  have htrace : WordTrace (prefixWord ++ tailWord_234452) baseStart_234452 baseEnd_234452 := by
    simpa [prefixWord, tailWord_234452, baseEnd_234452] using wordTrace_append hprefix tailTrace_234452
  have hstable : (prefixWord ++ tailWord_234452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234452).length < 2 ^ (prefixWord ++ tailWord_234452).sum := by decide
  have hdescent : baseEnd_234452 < baseStart_234452 := by decide
  rcases family_descends (prefixWord ++ tailWord_234452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234469 : List Nat := [1, 3, 1, 6, 1, 1, 3, 4]
def baseStart_234469 : Nat := 118140960795 + 234469 * 2 ^ 59
def prefixEnd_234469 : Nat := 4983230072969 + 3 ^ 40 * 234469 * 2
def baseEnd_234469 : Nat := 35672680171599517824949

theorem tailTrace_234469 : CollatzResearch.WordTrace tailWord_234469 prefixEnd_234469 35672680171599517824949 := by
  unfold tailWord_234469
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551786987566331962234461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5701191325044221308156307 8551786987566331962234461)
  ·
    refine ⟨3206920120337374485837923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8551786987566331962234461 3206920120337374485837923)
    ·
      refine ⟨4810380180506061728756885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3206920120337374485837923 4810380180506061728756885)
      ·
        refine ⟨225486570961221643535479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4810380180506061728756885 225486570961221643535479)
        ·
          refine ⟨338229856441832465303219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225486570961221643535479 338229856441832465303219)
          ·
            refine ⟨507344784662748697954829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338229856441832465303219 507344784662748697954829)
            ·
              refine ⟨190254294248530761733061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507344784662748697954829 190254294248530761733061)
              ·
                refine ⟨35672680171599517824949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190254294248530761733061 35672680171599517824949)
                ·
                  rfl

theorem cell20_234469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 4].length) (baseStart_234469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234469 prefixEnd_234469 := by exact prefixLift 234469
  have htrace : WordTrace (prefixWord ++ tailWord_234469) baseStart_234469 baseEnd_234469 := by
    simpa [prefixWord, tailWord_234469, baseEnd_234469] using wordTrace_append hprefix tailTrace_234469
  have hstable : (prefixWord ++ tailWord_234469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234469).length < 2 ^ (prefixWord ++ tailWord_234469).sum := by decide
  have hdescent : baseEnd_234469 < baseStart_234469 := by decide
  rcases family_descends (prefixWord ++ tailWord_234469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234497 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 3]
def baseStart_234497 : Nat := 118140960795 + 234497 * 2 ^ 59
def prefixEnd_234497 : Nat := 4983230072969 + 3 ^ 40 * 234497 * 2
def baseEnd_234497 : Nat := 107030820477754900541399

theorem tailTrace_234497 : CollatzResearch.WordTrace tailWord_234497 prefixEnd_234497 107030820477754900541399 := by
  unfold tailWord_234497
  simp only [CollatzResearch.WordTrace]
  refine ⟨8552808231464892744253745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5701872154309928496169163 8552808231464892744253745)
  ·
    refine ⟨6414606173598669558190309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8552808231464892744253745 6414606173598669558190309)
    ·
      refine ⟨1202738657549750542160683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6414606173598669558190309 1202738657549750542160683)
      ·
        refine ⟨1804107986324625813241025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202738657549750542160683 1804107986324625813241025)
        ·
          refine ⟨1353080989743469359930769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1804107986324625813241025 1353080989743469359930769)
          ·
            refine ⟨1014810742307602019948077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353080989743469359930769 1014810742307602019948077)
            ·
              refine ⟨380554028365350757480529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1014810742307602019948077 380554028365350757480529)
              ·
                refine ⟨285415521274013068110397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380554028365350757480529 285415521274013068110397)
                ·
                  refine ⟨107030820477754900541399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285415521274013068110397 107030820477754900541399)
                  ·
                    rfl

theorem cell20_234497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_234497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234497 prefixEnd_234497 := by exact prefixLift 234497
  have htrace : WordTrace (prefixWord ++ tailWord_234497) baseStart_234497 baseEnd_234497 := by
    simpa [prefixWord, tailWord_234497, baseEnd_234497] using wordTrace_append hprefix tailTrace_234497
  have hstable : (prefixWord ++ tailWord_234497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234497).length < 2 ^ (prefixWord ++ tailWord_234497).sum := by decide
  have hdescent : baseEnd_234497 < baseStart_234497 := by decide
  rcases family_descends (prefixWord ++ tailWord_234497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234504 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_234504 : Nat := 118140960795 + 234504 * 2 ^ 59
def prefixEnd_234504 : Nat := 4983230072969 + 3 ^ 40 * 234504 * 2
def baseEnd_234504 : Nat := 107034015468493987308037

theorem tailTrace_234504 : CollatzResearch.WordTrace tailWord_234504 prefixEnd_234504 107034015468493987308037 := by
  unfold tailWord_234504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276531771219766469879283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5702042361626355293172377 4276531771219766469879283)
  ·
    refine ⟨6414797656829649704818925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4276531771219766469879283 6414797656829649704818925)
    ·
      refine ⟨2405549121311118639307097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6414797656829649704818925 2405549121311118639307097)
      ·
        refine ⟨1804161840983338979480323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2405549121311118639307097 1804161840983338979480323)
        ·
          refine ⟨2706242761475008469220485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804161840983338979480323 2706242761475008469220485)
          ·
            refine ⟨507420517776564087978841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2706242761475008469220485 507420517776564087978841)
            ·
              refine ⟨380565388332423065984131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507420517776564087978841 380565388332423065984131)
              ·
                refine ⟨570848082498634598976197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380565388332423065984131 570848082498634598976197)
                ·
                  refine ⟨107034015468493987308037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570848082498634598976197 107034015468493987308037)
                  ·
                    rfl

theorem cell20_234504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_234504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234504 prefixEnd_234504 := by exact prefixLift 234504
  have htrace : WordTrace (prefixWord ++ tailWord_234504) baseStart_234504 baseEnd_234504 := by
    simpa [prefixWord, tailWord_234504, baseEnd_234504] using wordTrace_append hprefix tailTrace_234504
  have hstable : (prefixWord ++ tailWord_234504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234504).length < 2 ^ (prefixWord ++ tailWord_234504).sum := by decide
  have hdescent : baseEnd_234504 < baseStart_234504 := by decide
  rcases family_descends (prefixWord ++ tailWord_234504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234528 : List Nat := [2, 1, 1, 7, 1, 1, 1, 6]
def baseStart_234528 : Nat := 118140960795 + 234528 * 2 ^ 59
def prefixEnd_234528 : Nat := 4983230072969 + 3 ^ 40 * 234528 * 2
def baseEnd_234528 : Nat := 35681656574152190169313

theorem tailTrace_234528 : CollatzResearch.WordTrace tailWord_234528 prefixEnd_234528 35681656574152190169313 := by
  unfold tailWord_234528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276969447176292519316119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5702625929568390025754825 4276969447176292519316119)
  ·
    refine ⟨6415454170764438778974179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4276969447176292519316119 6415454170764438778974179)
    ·
      refine ⟨9623181256146658168461269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6415454170764438778974179 9623181256146658168461269)
      ·
        refine ⟨225543310690937300823311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9623181256146658168461269 225543310690937300823311)
        ·
          refine ⟨338314966036405951234967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225543310690937300823311 338314966036405951234967)
          ·
            refine ⟨507472449054608926852451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338314966036405951234967 507472449054608926852451)
            ·
              refine ⟨761208673581913390278677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507472449054608926852451 761208673581913390278677)
              ·
                refine ⟨35681656574152190169313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 761208673581913390278677 35681656574152190169313)
                ·
                  rfl

theorem cell20_234528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_234528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234528 prefixEnd_234528 := by exact prefixLift 234528
  have htrace : WordTrace (prefixWord ++ tailWord_234528) baseStart_234528 baseEnd_234528 := by
    simpa [prefixWord, tailWord_234528, baseEnd_234528] using wordTrace_append hprefix tailTrace_234528
  have hstable : (prefixWord ++ tailWord_234528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234528).length < 2 ^ (prefixWord ++ tailWord_234528).sum := by decide
  have hdescent : baseEnd_234528 < baseStart_234528 := by decide
  rcases family_descends (prefixWord ++ tailWord_234528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234535 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 5]
def baseStart_234535 : Nat := 118140960795 + 234535 * 2 ^ 59
def prefixEnd_234535 : Nat := 4983230072969 + 3 ^ 40 * 234535 * 2
def baseEnd_234535 : Nat := 107048164713195657274577

theorem tailTrace_234535 : CollatzResearch.WordTrace tailWord_234535 prefixEnd_234535 107048164713195657274577 := by
  unfold tailWord_234535
  simp only [CollatzResearch.WordTrace]
  refine ⟨8554194205327225234137059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5702796136884816822758039 8554194205327225234137059)
  ·
    refine ⟨12831291307990837851205589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8554194205327225234137059 12831291307990837851205589)
    ·
      refine ⟨300733390031035262137631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12831291307990837851205589 300733390031035262137631)
      ·
        refine ⟨451100085046552893206447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300733390031035262137631 451100085046552893206447)
        ·
          refine ⟨676650127569829339809671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451100085046552893206447 676650127569829339809671)
          ·
            refine ⟨1014975191354744009714507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676650127569829339809671 1014975191354744009714507)
            ·
              refine ⟨1522462787032116014571761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014975191354744009714507 1522462787032116014571761)
              ·
                refine ⟨1141847090274087010928821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522462787032116014571761 1141847090274087010928821)
                ·
                  refine ⟨107048164713195657274577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1141847090274087010928821 107048164713195657274577)
                  ·
                    rfl

theorem cell20_234535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_234535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234535 prefixEnd_234535 := by exact prefixLift 234535
  have htrace : WordTrace (prefixWord ++ tailWord_234535) baseStart_234535 baseEnd_234535 := by
    simpa [prefixWord, tailWord_234535, baseEnd_234535] using wordTrace_append hprefix tailTrace_234535
  have hstable : (prefixWord ++ tailWord_234535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234535).length < 2 ^ (prefixWord ++ tailWord_234535).sum := by decide
  have hdescent : baseEnd_234535 < baseStart_234535 := by decide
  rcases family_descends (prefixWord ++ tailWord_234535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234539 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_234539 : Nat := 118140960795 + 234539 * 2 ^ 59
def prefixEnd_234539 : Nat := 4983230072969 + 3 ^ 40 * 234539 * 2
def baseEnd_234539 : Nat := 107049990422189421141227

theorem tailTrace_234539 : CollatzResearch.WordTrace tailWord_234539 prefixEnd_234539 107049990422189421141227 := by
  unfold tailWord_234539
  simp only [CollatzResearch.WordTrace]
  refine ⟨8554340097312733917282671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5702893398208489278188447 8554340097312733917282671)
  ·
    refine ⟨12831510145969100875924007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8554340097312733917282671 12831510145969100875924007)
    ·
      refine ⟨19247265218953651313886011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12831510145969100875924007 19247265218953651313886011)
      ·
        refine ⟨28870897828430476970829017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19247265218953651313886011 28870897828430476970829017)
        ·
          refine ⟨21653173371322857728121763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28870897828430476970829017 21653173371322857728121763)
          ·
            refine ⟨32479760056984286592182645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21653173371322857728121763 32479760056984286592182645)
            ·
              refine ⟨3044977505342276868017123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32479760056984286592182645 3044977505342276868017123)
              ·
                refine ⟨4567466258013415302025685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044977505342276868017123 4567466258013415302025685)
                ·
                  refine ⟨107049990422189421141227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4567466258013415302025685 107049990422189421141227)
                  ·
                    rfl

theorem cell20_234539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_234539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234539 prefixEnd_234539 := by exact prefixLift 234539
  have htrace : WordTrace (prefixWord ++ tailWord_234539) baseStart_234539 baseEnd_234539 := by
    simpa [prefixWord, tailWord_234539, baseEnd_234539] using wordTrace_append hprefix tailTrace_234539
  have hstable : (prefixWord ++ tailWord_234539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234539).length < 2 ^ (prefixWord ++ tailWord_234539).sum := by decide
  have hdescent : baseEnd_234539 < baseStart_234539 := by decide
  rcases family_descends (prefixWord ++ tailWord_234539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234556 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_234556 : Nat := 118140960795 + 234556 * 2 ^ 59
def prefixEnd_234556 : Nat := 4983230072969 + 3 ^ 40 * 234556 * 2
def baseEnd_234556 : Nat := 107057749685412917574491

theorem tailTrace_234556 : CollatzResearch.WordTrace tailWord_234556 prefixEnd_234556 107057749685412917574491 := by
  unfold tailWord_234556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277480069125572910325761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5703306758834097213767681 4277480069125572910325761)
  ·
    refine ⟨3208110051844179682744321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4277480069125572910325761 3208110051844179682744321)
    ·
      refine ⟨2406082538883134762058241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3208110051844179682744321 2406082538883134762058241)
      ·
        refine ⟨1804561904162351071543681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2406082538883134762058241 1804561904162351071543681)
        ·
          refine ⟨1353421428121763303657761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1804561904162351071543681 1353421428121763303657761)
          ·
            refine ⟨1015066071091322477743321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353421428121763303657761 1015066071091322477743321)
            ·
              refine ⟨761299553318491858307491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015066071091322477743321 761299553318491858307491)
              ·
                refine ⟨1141949329977737787461237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761299553318491858307491 1141949329977737787461237)
                ·
                  refine ⟨107057749685412917574491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1141949329977737787461237 107057749685412917574491)
                  ·
                    rfl

theorem cell20_234556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_234556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234556 prefixEnd_234556 := by exact prefixLift 234556
  have htrace : WordTrace (prefixWord ++ tailWord_234556) baseStart_234556 baseEnd_234556 := by
    simpa [prefixWord, tailWord_234556, baseEnd_234556] using wordTrace_append hprefix tailTrace_234556
  have hstable : (prefixWord ++ tailWord_234556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234556).length < 2 ^ (prefixWord ++ tailWord_234556).sum := by decide
  have hdescent : baseEnd_234556 < baseStart_234556 := by decide
  rcases family_descends (prefixWord ++ tailWord_234556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234566 : List Nat := [6, 1, 1, 1, 1, 2, 1, 7]
def baseStart_234566 : Nat := 118140960795 + 234566 * 2 ^ 59
def prefixEnd_234566 : Nat := 4983230072969 + 3 ^ 40 * 234566 * 2
def baseEnd_234566 : Nat := 35687437985965775747039

theorem tailTrace_234566 : CollatzResearch.WordTrace tailWord_234566 prefixEnd_234566 35687437985965775747039 := by
  unfold tailWord_234566
  simp only [CollatzResearch.WordTrace]
  refine ⟨267353902131716172766111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5703549912143278352343701 267353902131716172766111)
  ·
    refine ⟨401030853197574259149167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267353902131716172766111 401030853197574259149167)
    ·
      refine ⟨601546279796361388723751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401030853197574259149167 601546279796361388723751)
      ·
        refine ⟨902319419694542083085627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601546279796361388723751 902319419694542083085627)
        ·
          refine ⟨1353479129541813124628441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902319419694542083085627 1353479129541813124628441)
          ·
            refine ⟨1015109347156359843471331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353479129541813124628441 1015109347156359843471331)
            ·
              refine ⟨1522664020734539765206997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015109347156359843471331 1522664020734539765206997)
              ·
                refine ⟨35687437985965775747039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1522664020734539765206997 35687437985965775747039)
                ·
                  rfl

theorem cell20_234566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_234566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234566 prefixEnd_234566 := by exact prefixLift 234566
  have htrace : WordTrace (prefixWord ++ tailWord_234566) baseStart_234566 baseEnd_234566 := by
    simpa [prefixWord, tailWord_234566, baseEnd_234566] using wordTrace_append hprefix tailTrace_234566
  have hstable : (prefixWord ++ tailWord_234566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234566).length < 2 ^ (prefixWord ++ tailWord_234566).sum := by decide
  have hdescent : baseEnd_234566 < baseStart_234566 := by decide
  rcases family_descends (prefixWord ++ tailWord_234566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234570 : List Nat := [3, 1, 2, 1, 1, 2, 3, 7]
def baseStart_234570 : Nat := 118140960795 + 234570 * 2 ^ 59
def prefixEnd_234570 : Nat := 4983230072969 + 3 ^ 40 * 234570 * 2
def baseEnd_234570 : Nat := 35688046555630363702589

theorem tailTrace_234570 : CollatzResearch.WordTrace tailWord_234570 prefixEnd_234570 35688046555630363702589 := by
  unfold tailWord_234570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138867690050106552915291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5703647173466950807774109 2138867690050106552915291)
  ·
    refine ⟨3208301535075159829372937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2138867690050106552915291 3208301535075159829372937)
    ·
      refine ⟨2406226151306369872029703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3208301535075159829372937 2406226151306369872029703)
      ·
        refine ⟨3609339226959554808044555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406226151306369872029703 3609339226959554808044555)
        ·
          refine ⟨5414008840439332212066833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609339226959554808044555 5414008840439332212066833)
          ·
            refine ⟨4060506630329499159050125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5414008840439332212066833 4060506630329499159050125)
            ·
              refine ⟨1522689986373562184643797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4060506630329499159050125 1522689986373562184643797)
              ·
                refine ⟨35688046555630363702589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1522689986373562184643797 35688046555630363702589)
                ·
                  rfl

theorem cell20_234570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_234570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234570 prefixEnd_234570 := by exact prefixLift 234570
  have htrace : WordTrace (prefixWord ++ tailWord_234570) baseStart_234570 baseEnd_234570 := by
    simpa [prefixWord, tailWord_234570, baseEnd_234570] using wordTrace_append hprefix tailTrace_234570
  have hstable : (prefixWord ++ tailWord_234570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234570).length < 2 ^ (prefixWord ++ tailWord_234570).sum := by decide
  have hdescent : baseEnd_234570 < baseStart_234570 := by decide
  rcases family_descends (prefixWord ++ tailWord_234570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234625 : List Nat := [1, 2, 4, 2, 2, 1, 3, 5]
def baseStart_234625 : Nat := 118140960795 + 234625 * 2 ^ 59
def prefixEnd_234625 : Nat := 4983230072969 + 3 ^ 40 * 234625 * 2
def baseEnd_234625 : Nat := 35696414388518448091403

theorem tailTrace_234625 : CollatzResearch.WordTrace tailWord_234625 prefixEnd_234625 35696414388518448091403 := by
  unfold tailWord_234625
  simp only [CollatzResearch.WordTrace]
  refine ⟨8557476775001170604913329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5704984516667447069942219 8557476775001170604913329)
  ·
    refine ⟨6418107581250877953684997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8557476775001170604913329 6418107581250877953684997)
    ·
      refine ⟨1203395171484539616315937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6418107581250877953684997 1203395171484539616315937)
      ·
        refine ⟨902546378613404712236953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1203395171484539616315937 902546378613404712236953)
        ·
          refine ⟨676909783960053534177715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902546378613404712236953 676909783960053534177715)
          ·
            refine ⟨1015364675940080301266573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676909783960053534177715 1015364675940080301266573)
            ·
              refine ⟨380761753477530112974965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1015364675940080301266573 380761753477530112974965)
              ·
                refine ⟨35696414388518448091403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380761753477530112974965 35696414388518448091403)
                ·
                  rfl

theorem cell20_234625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_234625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234625 prefixEnd_234625 := by exact prefixLift 234625
  have htrace : WordTrace (prefixWord ++ tailWord_234625) baseStart_234625 baseEnd_234625 := by
    simpa [prefixWord, tailWord_234625, baseEnd_234625] using wordTrace_append hprefix tailTrace_234625
  have hstable : (prefixWord ++ tailWord_234625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234625).length < 2 ^ (prefixWord ++ tailWord_234625).sum := by decide
  have hdescent : baseEnd_234625 < baseStart_234625 := by decide
  rcases family_descends (prefixWord ++ tailWord_234625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234642 : List Nat := [3, 2, 3, 1, 1, 3, 3, 4]
def baseStart_234642 : Nat := 118140960795 + 234642 * 2 ^ 59
def prefixEnd_234642 : Nat := 4983230072969 + 3 ^ 40 * 234642 * 2
def baseEnd_234642 : Nat := 35699000809592946902491

theorem tailTrace_234642 : CollatzResearch.WordTrace tailWord_234642 prefixEnd_234642 35699000809592946902491 := by
  unfold tailWord_234642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2139524203984895627070545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5705397877293055005521453 2139524203984895627070545)
  ·
    refine ⟨1604643152988671720302909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2139524203984895627070545 1604643152988671720302909)
    ·
      refine ⟨601741182370751895113591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1604643152988671720302909 601741182370751895113591)
      ·
        refine ⟨902611773556127842670387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601741182370751895113591 902611773556127842670387)
        ·
          refine ⟨1353917660334191764005581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902611773556127842670387 1353917660334191764005581)
          ·
            refine ⟨507719122625321911502093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1353917660334191764005581 507719122625321911502093)
            ·
              refine ⟨190394670984495716813285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507719122625321911502093 190394670984495716813285)
              ·
                refine ⟨35699000809592946902491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190394670984495716813285 35699000809592946902491)
                ·
                  rfl

theorem cell20_234642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_234642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234642 prefixEnd_234642 := by exact prefixLift 234642
  have htrace : WordTrace (prefixWord ++ tailWord_234642) baseStart_234642 baseEnd_234642 := by
    simpa [prefixWord, tailWord_234642, baseEnd_234642] using wordTrace_append hprefix tailTrace_234642
  have hstable : (prefixWord ++ tailWord_234642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234642).length < 2 ^ (prefixWord ++ tailWord_234642).sum := by decide
  have hdescent : baseEnd_234642 < baseStart_234642 := by decide
  rcases family_descends (prefixWord ++ tailWord_234642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234663 : List Nat := [1, 1, 6, 2, 1, 2, 7]
def baseStart_234663 : Nat := 118140960795 + 234663 * 2 ^ 59
def prefixEnd_234663 : Nat := 4983230072969 + 3 ^ 40 * 234663 * 2
def baseEnd_234663 : Nat := 11900731933444011223043

theorem tailTrace_234663 : CollatzResearch.WordTrace tailWord_234663 prefixEnd_234663 11900731933444011223043 := by
  unfold tailWord_234663
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558862748863503094796643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5705908499242335396531095 8558862748863503094796643)
  ·
    refine ⟨12838294123295254642194965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8558862748863503094796643 12838294123295254642194965)
    ·
      refine ⟨601795037029465061352889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12838294123295254642194965 601795037029465061352889)
      ·
        refine ⟨451346277772098796014667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601795037029465061352889 451346277772098796014667)
        ·
          refine ⟨677019416658148194022001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451346277772098796014667 677019416658148194022001)
          ·
            refine ⟨507764562493611145516501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677019416658148194022001 507764562493611145516501)
            ·
              refine ⟨11900731933444011223043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 507764562493611145516501 11900731933444011223043)
              ·
                rfl

theorem cell20_234663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 7].length) (baseStart_234663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234663 prefixEnd_234663 := by exact prefixLift 234663
  have htrace : WordTrace (prefixWord ++ tailWord_234663) baseStart_234663 baseEnd_234663 := by
    simpa [prefixWord, tailWord_234663, baseEnd_234663] using wordTrace_append hprefix tailTrace_234663
  have hstable : (prefixWord ++ tailWord_234663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234663).length < 2 ^ (prefixWord ++ tailWord_234663).sum := by decide
  have hdescent : baseEnd_234663 < baseStart_234663 := by decide
  rcases family_descends (prefixWord ++ tailWord_234663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234666 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_234666 : Nat := 118140960795 + 234666 * 2 ^ 59
def prefixEnd_234666 : Nat := 4983230072969 + 3 ^ 40 * 234666 * 2
def baseEnd_234666 : Nat := 107107956682741423907375

theorem tailTrace_234666 : CollatzResearch.WordTrace tailWord_234666 prefixEnd_234666 107107956682741423907375 := by
  unfold tailWord_234666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2139743041963158651788963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5705981445235089738103901 2139743041963158651788963)
  ·
    refine ⟨3209614562944737977683445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2139743041963158651788963 3209614562944737977683445)
    ·
      refine ⟨300901365276069185407823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3209614562944737977683445 300901365276069185407823)
      ·
        refine ⟨451352047914103778111735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300901365276069185407823 451352047914103778111735)
        ·
          refine ⟨677028071871155667167603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451352047914103778111735 677028071871155667167603)
          ·
            refine ⟨1015542107806733500751405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677028071871155667167603 1015542107806733500751405)
            ·
              refine ⟨380828290427525062781777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1015542107806733500751405 380828290427525062781777)
              ·
                refine ⟨285621217820643797086333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380828290427525062781777 285621217820643797086333)
                ·
                  refine ⟨107107956682741423907375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285621217820643797086333 107107956682741423907375)
                  ·
                    rfl

theorem cell20_234666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_234666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234666 prefixEnd_234666 := by exact prefixLift 234666
  have htrace : WordTrace (prefixWord ++ tailWord_234666) baseStart_234666 baseEnd_234666 := by
    simpa [prefixWord, tailWord_234666, baseEnd_234666] using wordTrace_append hprefix tailTrace_234666
  have hstable : (prefixWord ++ tailWord_234666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234666).length < 2 ^ (prefixWord ++ tailWord_234666).sum := by decide
  have hdescent : baseEnd_234666 < baseStart_234666 := by decide
  rcases family_descends (prefixWord ++ tailWord_234666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234673 : List Nat := [1, 2, 2, 5, 1, 1, 2, 4, 2]
def baseStart_234673 : Nat := 118140960795 + 234673 * 2 ^ 59
def prefixEnd_234673 : Nat := 4983230072969 + 3 ^ 40 * 234673 * 2
def baseEnd_234673 : Nat := 107111151673480510674013

theorem tailTrace_234673 : CollatzResearch.WordTrace tailWord_234673 prefixEnd_234673 107111151673480510674013 := by
  unfold tailWord_234673
  simp only [CollatzResearch.WordTrace]
  refine ⟨8559227478827274802660673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5706151652551516535107115 8559227478827274802660673)
  ·
    refine ⟨6419420609120456101995505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8559227478827274802660673 6419420609120456101995505)
    ·
      refine ⟨4814565456840342076496629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6419420609120456101995505 4814565456840342076496629)
      ·
        refine ⟨451365511578782069671559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4814565456840342076496629 451365511578782069671559)
        ·
          refine ⟨677048267368173104507339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451365511578782069671559 677048267368173104507339)
          ·
            refine ⟨1015572401052259656761009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677048267368173104507339 1015572401052259656761009)
            ·
              refine ⟨761679300789194742570757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015572401052259656761009 761679300789194742570757)
              ·
                refine ⟨142814868897974014232017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761679300789194742570757 142814868897974014232017)
                ·
                  refine ⟨107111151673480510674013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142814868897974014232017 107111151673480510674013)
                  ·
                    rfl

theorem cell20_234673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_234673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234673 prefixEnd_234673 := by exact prefixLift 234673
  have htrace : WordTrace (prefixWord ++ tailWord_234673) baseStart_234673 baseEnd_234673 := by
    simpa [prefixWord, tailWord_234673, baseEnd_234673] using wordTrace_append hprefix tailTrace_234673
  have hstable : (prefixWord ++ tailWord_234673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234673).length < 2 ^ (prefixWord ++ tailWord_234673).sum := by decide
  have hdescent : baseEnd_234673 < baseStart_234673 := by decide
  rcases family_descends (prefixWord ++ tailWord_234673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234732 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_234732 : Nat := 118140960795 + 234732 * 2 ^ 59
def prefixEnd_234732 : Nat := 4983230072969 + 3 ^ 40 * 234732 * 2
def baseEnd_234732 : Nat := 107138080881138527707105

theorem tailTrace_234732 : CollatzResearch.WordTrace tailWord_234732 prefixEnd_234732 107138080881138527707105 := by
  unfold tailWord_234732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280689692806763939529225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5707586257075685252705633 4280689692806763939529225)
  ·
    refine ⟨3210517269605072954646919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4280689692806763939529225 3210517269605072954646919)
    ·
      refine ⟨4815775904407609431970379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3210517269605072954646919 4815775904407609431970379)
      ·
        refine ⟨7223663856611414147955569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4815775904407609431970379 7223663856611414147955569)
        ·
          refine ⟨5417747892458560610966677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7223663856611414147955569 5417747892458560610966677)
          ·
            refine ⟨253956932458995028639063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5417747892458560610966677 253956932458995028639063)
            ·
              refine ⟨380935398688492542958595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253956932458995028639063 380935398688492542958595)
              ·
                refine ⟨571403098032738814437893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380935398688492542958595 571403098032738814437893)
                ·
                  refine ⟨107138080881138527707105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571403098032738814437893 107138080881138527707105)
                  ·
                    rfl

theorem cell20_234732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_234732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234732 prefixEnd_234732 := by exact prefixLift 234732
  have htrace : WordTrace (prefixWord ++ tailWord_234732) baseStart_234732 baseEnd_234732 := by
    simpa [prefixWord, tailWord_234732, baseEnd_234732] using wordTrace_append hprefix tailTrace_234732
  have hstable : (prefixWord ++ tailWord_234732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234732).length < 2 ^ (prefixWord ++ tailWord_234732).sum := by decide
  have hdescent : baseEnd_234732 < baseStart_234732 := by decide
  rcases family_descends (prefixWord ++ tailWord_234732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234746 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_234746 : Nat := 118140960795 + 234746 * 2 ^ 59
def prefixEnd_234746 : Nat := 4983230072969 + 3 ^ 40 * 234746 * 2
def baseEnd_234746 : Nat := 107144470862616701240381

theorem tailTrace_234746 : CollatzResearch.WordTrace tailWord_234746 prefixEnd_234746 107144470862616701240381 := by
  unfold tailWord_234746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140472501890702067517023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5707926671708538846712061 2140472501890702067517023)
  ·
    refine ⟨3210708752836053101275535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2140472501890702067517023 3210708752836053101275535)
    ·
      refine ⟨4816063129254079651913303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3210708752836053101275535 4816063129254079651913303)
      ·
        refine ⟨7224094693881119477869955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816063129254079651913303 7224094693881119477869955)
        ·
          refine ⟨10836142040821679216804933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224094693881119477869955 10836142040821679216804933)
          ·
            refine ⟨2031776632654064853150925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10836142040821679216804933 2031776632654064853150925)
            ·
              refine ⟨761916237245274319931597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2031776632654064853150925 761916237245274319931597)
              ·
                refine ⟨285718588966977869974349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 761916237245274319931597 285718588966977869974349)
                ·
                  refine ⟨107144470862616701240381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285718588966977869974349 107144470862616701240381)
                  ·
                    rfl

theorem cell20_234746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_234746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234746 prefixEnd_234746 := by exact prefixLift 234746
  have htrace : WordTrace (prefixWord ++ tailWord_234746) baseStart_234746 baseEnd_234746 := by
    simpa [prefixWord, tailWord_234746, baseEnd_234746] using wordTrace_append hprefix tailTrace_234746
  have hstable : (prefixWord ++ tailWord_234746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234746).length < 2 ^ (prefixWord ++ tailWord_234746).sum := by decide
  have hdescent : baseEnd_234746 < baseStart_234746 := by decide
  rcases family_descends (prefixWord ++ tailWord_234746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234783 : List Nat := [1, 1, 2, 4, 5, 1, 2, 2, 2]
def baseStart_234783 : Nat := 118140960795 + 234783 * 2 ^ 59
def prefixEnd_234783 : Nat := 4983230072969 + 3 ^ 40 * 234783 * 2
def baseEnd_234783 : Nat := 107161358670809017006897

theorem tailTrace_234783 : CollatzResearch.WordTrace tailWord_234783 prefixEnd_234783 107161358670809017006897 := by
  unfold tailWord_234783
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563239508428763589165003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5708826338952509059443335 8563239508428763589165003)
  ·
    refine ⟨12844859262643145383747505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8563239508428763589165003 12844859262643145383747505)
    ·
      refine ⟨9633644446982359037810629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12844859262643145383747505 9633644446982359037810629)
      ·
        refine ⟨1806308333809192319589493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9633644446982359037810629 1806308333809192319589493)
        ·
          refine ⟨169341406294611779961515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1806308333809192319589493 169341406294611779961515)
          ·
            refine ⟨254012109441917669942273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169341406294611779961515 254012109441917669942273)
            ·
              refine ⟨190509082081438252456705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254012109441917669942273 190509082081438252456705)
              ·
                refine ⟨142881811561078689342529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190509082081438252456705 142881811561078689342529)
                ·
                  refine ⟨107161358670809017006897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142881811561078689342529 107161358670809017006897)
                  ·
                    rfl

theorem cell20_234783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 2].length) (baseStart_234783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234783 prefixEnd_234783 := by exact prefixLift 234783
  have htrace : WordTrace (prefixWord ++ tailWord_234783) baseStart_234783 baseEnd_234783 := by
    simpa [prefixWord, tailWord_234783, baseEnd_234783] using wordTrace_append hprefix tailTrace_234783
  have hstable : (prefixWord ++ tailWord_234783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234783).length < 2 ^ (prefixWord ++ tailWord_234783).sum := by decide
  have hdescent : baseEnd_234783 < baseStart_234783 := by decide
  rcases family_descends (prefixWord ++ tailWord_234783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234787 : List Nat := [1, 1, 1, 4, 2, 3, 4, 2, 2]
def baseStart_234787 : Nat := 118140960795 + 234787 * 2 ^ 59
def prefixEnd_234787 : Nat := 4983230072969 + 3 ^ 40 * 234787 * 2
def baseEnd_234787 : Nat := 107163184379802780873547

theorem tailTrace_234787 : CollatzResearch.WordTrace tailWord_234787 prefixEnd_234787 107163184379802780873547 := by
  unfold tailWord_234787
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563385400414272272310615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5708923600276181514873743 8563385400414272272310615)
  ·
    refine ⟨12845078100621408408465923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8563385400414272272310615 12845078100621408408465923)
    ·
      refine ⟨19267617150932112612698885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12845078100621408408465923 19267617150932112612698885)
      ·
        refine ⟨3612678215799771114881041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19267617150932112612698885 3612678215799771114881041)
        ·
          refine ⟨2709508661849828336160781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3612678215799771114881041 2709508661849828336160781)
          ·
            refine ⟨1016065748193685626060293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2709508661849828336160781 1016065748193685626060293)
            ·
              refine ⟨190512327786316054886305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1016065748193685626060293 190512327786316054886305)
              ·
                refine ⟨142884245839737041164729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190512327786316054886305 142884245839737041164729)
                ·
                  refine ⟨107163184379802780873547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142884245839737041164729 107163184379802780873547)
                  ·
                    rfl

theorem cell20_234787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 2].length) (baseStart_234787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234787 prefixEnd_234787 := by exact prefixLift 234787
  have htrace : WordTrace (prefixWord ++ tailWord_234787) baseStart_234787 baseEnd_234787 := by
    simpa [prefixWord, tailWord_234787, baseEnd_234787] using wordTrace_append hprefix tailTrace_234787
  have hstable : (prefixWord ++ tailWord_234787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234787).length < 2 ^ (prefixWord ++ tailWord_234787).sum := by decide
  have hdescent : baseEnd_234787 < baseStart_234787 := by decide
  rcases family_descends (prefixWord ++ tailWord_234787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234794 : List Nat := [3, 1, 4, 2, 1, 3, 1, 5]
def baseStart_234794 : Nat := 118140960795 + 234794 * 2 ^ 59
def prefixEnd_234794 : Nat := 4983230072969 + 3 ^ 40 * 234794 * 2
def baseEnd_234794 : Nat := 35722126456847289213395

theorem tailTrace_234794 : CollatzResearch.WordTrace tailWord_234794 prefixEnd_234794 35722126456847289213395 := by
  unfold tailWord_234794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140910177847228116953859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5709093807592608311876957 2140910177847228116953859)
  ·
    refine ⟨3211365266770842175430789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2140910177847228116953859 3211365266770842175430789)
    ·
      refine ⟨602130987519532907893273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3211365266770842175430789 602130987519532907893273)
      ·
        refine ⟨451598240639649680919955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602130987519532907893273 451598240639649680919955)
        ·
          refine ⟨677397360959474521379933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451598240639649680919955 677397360959474521379933)
          ·
            refine ⟨254024010359802945517475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677397360959474521379933 254024010359802945517475)
            ·
              refine ⟨381036015539704418276213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254024010359802945517475 381036015539704418276213)
              ·
                refine ⟨35722126456847289213395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381036015539704418276213 35722126456847289213395)
                ·
                  rfl

theorem cell20_234794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_234794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234794 prefixEnd_234794 := by exact prefixLift 234794
  have htrace : WordTrace (prefixWord ++ tailWord_234794) baseStart_234794 baseEnd_234794 := by
    simpa [prefixWord, tailWord_234794, baseEnd_234794] using wordTrace_append hprefix tailTrace_234794
  have hstable : (prefixWord ++ tailWord_234794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234794).length < 2 ^ (prefixWord ++ tailWord_234794).sum := by decide
  have hdescent : baseEnd_234794 < baseStart_234794 := by decide
  rcases family_descends (prefixWord ++ tailWord_234794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234815 : List Nat := [1, 1, 2, 2, 4, 3, 3, 4]
def baseStart_234815 : Nat := 118140960795 + 234815 * 2 ^ 59
def prefixEnd_234815 : Nat := 4983230072969 + 3 ^ 40 * 234815 * 2
def baseEnd_234815 : Nat := 35725321447586375980033

theorem tailTrace_234815 : CollatzResearch.WordTrace tailWord_234815 prefixEnd_234815 35725321447586375980033 := by
  unfold tailWord_234815
  simp only [CollatzResearch.WordTrace]
  refine ⟨8564406644312833054329899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5709604429541888702886599 8564406644312833054329899)
  ·
    refine ⟨12846609966469249581494849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8564406644312833054329899 12846609966469249581494849)
    ·
      refine ⟨9634957474851937186121137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12846609966469249581494849 9634957474851937186121137)
      ·
        refine ⟨7226218106138952889590853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9634957474851937186121137 7226218106138952889590853)
        ·
          refine ⟨1354915894901053666798285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7226218106138952889590853 1354915894901053666798285)
          ·
            refine ⟨508093460587895125049357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1354915894901053666798285 508093460587895125049357)
            ·
              refine ⟨190535047720460671893509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508093460587895125049357 190535047720460671893509)
              ·
                refine ⟨35725321447586375980033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190535047720460671893509 35725321447586375980033)
                ·
                  rfl

theorem cell20_234815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 4].length) (baseStart_234815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234815 prefixEnd_234815 := by exact prefixLift 234815
  have htrace : WordTrace (prefixWord ++ tailWord_234815) baseStart_234815 baseEnd_234815 := by
    simpa [prefixWord, tailWord_234815, baseEnd_234815] using wordTrace_append hprefix tailTrace_234815
  have hstable : (prefixWord ++ tailWord_234815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234815).length < 2 ^ (prefixWord ++ tailWord_234815).sum := by decide
  have hdescent : baseEnd_234815 < baseStart_234815 := by decide
  rcases family_descends (prefixWord ++ tailWord_234815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234836 : List Nat := [2, 4, 1, 1, 2, 1, 9]
def baseStart_234836 : Nat := 118140960795 + 234836 * 2 ^ 59
def prefixEnd_234836 : Nat := 4983230072969 + 3 ^ 40 * 234836 * 2
def baseEnd_234836 : Nat := 11909505479441820915557

theorem tailTrace_234836 : CollatzResearch.WordTrace tailWord_234836 prefixEnd_234836 11909505479441820915557 := by
  unfold tailWord_234836
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282586288618376820422181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5710115051491169093896241 4282586288618376820422181)
  ·
    refine ⟨802984929115945653829159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4282586288618376820422181 802984929115945653829159)
    ·
      refine ⟨1204477393673918480743739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802984929115945653829159 1204477393673918480743739)
      ·
        refine ⟨1806716090510877721115609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204477393673918480743739 1806716090510877721115609)
        ·
          refine ⟨1355037067883158290836707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1806716090510877721115609 1355037067883158290836707)
          ·
            refine ⟨2032555601824737436255061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355037067883158290836707 2032555601824737436255061)
            ·
              refine ⟨11909505479441820915557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2032555601824737436255061 11909505479441820915557)
              ·
                rfl

theorem cell20_234836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 9].length) (baseStart_234836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234836 prefixEnd_234836 := by exact prefixLift 234836
  have htrace : WordTrace (prefixWord ++ tailWord_234836) baseStart_234836 baseEnd_234836 := by
    simpa [prefixWord, tailWord_234836, baseEnd_234836] using wordTrace_append hprefix tailTrace_234836
  have hstable : (prefixWord ++ tailWord_234836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234836).length < 2 ^ (prefixWord ++ tailWord_234836).sum := by decide
  have hdescent : baseEnd_234836 < baseStart_234836 := by decide
  rcases family_descends (prefixWord ++ tailWord_234836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234839 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 3]
def baseStart_234839 : Nat := 118140960795 + 234839 * 2 ^ 59
def prefixEnd_234839 : Nat := 4983230072969 + 3 ^ 40 * 234839 * 2
def baseEnd_234839 : Nat := 107186918596721711140001

theorem tailTrace_234839 : CollatzResearch.WordTrace tailWord_234839 prefixEnd_234839 107186918596721711140001 := by
  unfold tailWord_234839
  simp only [CollatzResearch.WordTrace]
  refine ⟨8565281996225885153203571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5710187997483923435469047 8565281996225885153203571)
  ·
    refine ⟨12847922994338827729805357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8565281996225885153203571 12847922994338827729805357)
    ·
      refine ⟨4817971122877060398677009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12847922994338827729805357 4817971122877060398677009)
      ·
        refine ⟨3613478342157795299007757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4817971122877060398677009 3613478342157795299007757)
        ·
          refine ⟨1355054378309173237127909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3613478342157795299007757 1355054378309173237127909)
          ·
            refine ⟨254072695932969981961483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1355054378309173237127909 254072695932969981961483)
            ·
              refine ⟨381109043899454972942225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254072695932969981961483 381109043899454972942225)
              ·
                refine ⟨285831782924591229706669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381109043899454972942225 285831782924591229706669)
                ·
                  refine ⟨107186918596721711140001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285831782924591229706669 107186918596721711140001)
                  ·
                    rfl

theorem cell20_234839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 3].length) (baseStart_234839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234839 prefixEnd_234839 := by exact prefixLift 234839
  have htrace : WordTrace (prefixWord ++ tailWord_234839) baseStart_234839 baseEnd_234839 := by
    simpa [prefixWord, tailWord_234839, baseEnd_234839] using wordTrace_append hprefix tailTrace_234839
  have hstable : (prefixWord ++ tailWord_234839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234839).length < 2 ^ (prefixWord ++ tailWord_234839).sum := by decide
  have hdescent : baseEnd_234839 < baseStart_234839 := by decide
  rcases family_descends (prefixWord ++ tailWord_234839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234856 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_234856 : Nat := 118140960795 + 234856 * 2 ^ 59
def prefixEnd_234856 : Nat := 4983230072969 + 3 ^ 40 * 234856 * 2
def baseEnd_234856 : Nat := 107194677859945207573265

theorem tailTrace_234856 : CollatzResearch.WordTrace tailWord_234856 prefixEnd_234856 107194677859945207573265 := by
  unfold tailWord_234856
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282951018582148528286211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5710601358109531371048281 4282951018582148528286211)
  ·
    refine ⟨6424426527873222792429317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4282951018582148528286211 6424426527873222792429317)
    ·
      refine ⟨1204579973976229273580497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6424426527873222792429317 1204579973976229273580497)
      ·
        refine ⟨903434980482171955185373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204579973976229273580497 903434980482171955185373)
        ·
          refine ⟨338788117680814483194515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 903434980482171955185373 338788117680814483194515)
          ·
            refine ⟨508182176521221724791773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338788117680814483194515 508182176521221724791773)
            ·
              refine ⟨190568316195458146796915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508182176521221724791773 190568316195458146796915)
              ·
                refine ⟨285852474293187220195373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190568316195458146796915 285852474293187220195373)
                ·
                  refine ⟨107194677859945207573265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285852474293187220195373 107194677859945207573265)
                  ·
                    rfl

theorem cell20_234856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_234856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234856 prefixEnd_234856 := by exact prefixLift 234856
  have htrace : WordTrace (prefixWord ++ tailWord_234856) baseStart_234856 baseEnd_234856 := by
    simpa [prefixWord, tailWord_234856, baseEnd_234856] using wordTrace_append hprefix tailTrace_234856
  have hstable : (prefixWord ++ tailWord_234856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234856).length < 2 ^ (prefixWord ++ tailWord_234856).sum := by decide
  have hdescent : baseEnd_234856 < baseStart_234856 := by decide
  rcases family_descends (prefixWord ++ tailWord_234856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234905 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_234905 : Nat := 118140960795 + 234905 * 2 ^ 59
def prefixEnd_234905 : Nat := 4983230072969 + 3 ^ 40 * 234905 * 2
def baseEnd_234905 : Nat := 107217042795118814939731

theorem tailTrace_234905 : CollatzResearch.WordTrace tailWord_234905 prefixEnd_234905 107217042795118814939731 := by
  unfold tailWord_234905
  simp only [CollatzResearch.WordTrace]
  refine ⟨8567689213986778425106169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5711792809324518950070779 8567689213986778425106169)
  ·
    refine ⟨6425766910490083818829627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8567689213986778425106169 6425766910490083818829627)
    ·
      refine ⟨9638650365735125728244441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6425766910490083818829627 9638650365735125728244441)
      ·
        refine ⟨7228987774301344296183331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9638650365735125728244441 7228987774301344296183331)
        ·
          refine ⟨10843481661452016444274997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7228987774301344296183331 10843481661452016444274997)
          ·
            refine ⟨1016576405761126541650781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10843481661452016444274997 1016576405761126541650781)
            ·
              refine ⟨381216152160422453119043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1016576405761126541650781 381216152160422453119043)
              ·
                refine ⟨571824228240633679678565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381216152160422453119043 571824228240633679678565)
                ·
                  refine ⟨107217042795118814939731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571824228240633679678565 107217042795118814939731)
                  ·
                    rfl

theorem cell20_234905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_234905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234905 prefixEnd_234905 := by exact prefixLift 234905
  have htrace : WordTrace (prefixWord ++ tailWord_234905) baseStart_234905 baseEnd_234905 := by
    simpa [prefixWord, tailWord_234905, baseEnd_234905] using wordTrace_append hprefix tailTrace_234905
  have hstable : (prefixWord ++ tailWord_234905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234905).length < 2 ^ (prefixWord ++ tailWord_234905).sum := by decide
  have hdescent : baseEnd_234905 < baseStart_234905 := by decide
  rcases family_descends (prefixWord ++ tailWord_234905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234908 : List Nat := [2, 2, 3, 4, 1, 1, 2, 5]
def baseStart_234908 : Nat := 118140960795 + 234908 * 2 ^ 59
def prefixEnd_234908 : Nat := 4983230072969 + 3 ^ 40 * 234908 * 2
def baseEnd_234908 : Nat := 35739470692288045946573

theorem tailTrace_234908 : CollatzResearch.WordTrace tailWord_234908 prefixEnd_234908 35739470692288045946573 := by
  unfold tailWord_234908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4283899316487954968732689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5711865755317273291643585 4283899316487954968732689)
  ·
    refine ⟨3212924487365966226549517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4283899316487954968732689 3212924487365966226549517)
    ·
      refine ⟨1204846682762237334956069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3212924487365966226549517 1204846682762237334956069)
      ·
        refine ⟨225908753017919500304263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1204846682762237334956069 225908753017919500304263)
        ·
          refine ⟨338863129526879250456395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225908753017919500304263 338863129526879250456395)
          ·
            refine ⟨508294694290318875684593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338863129526879250456395 508294694290318875684593)
            ·
              refine ⟨381221020717739156763445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508294694290318875684593 381221020717739156763445)
              ·
                refine ⟨35739470692288045946573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381221020717739156763445 35739470692288045946573)
                ·
                  rfl

theorem cell20_234908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_234908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234908 prefixEnd_234908 := by exact prefixLift 234908
  have htrace : WordTrace (prefixWord ++ tailWord_234908) baseStart_234908 baseEnd_234908 := by
    simpa [prefixWord, tailWord_234908, baseEnd_234908] using wordTrace_append hprefix tailTrace_234908
  have hstable : (prefixWord ++ tailWord_234908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234908).length < 2 ^ (prefixWord ++ tailWord_234908).sum := by decide
  have hdescent : baseEnd_234908 < baseStart_234908 := by decide
  rcases family_descends (prefixWord ++ tailWord_234908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234912 : List Nat := [2, 1, 1, 4, 1, 2, 4, 5]
def baseStart_234912 : Nat := 118140960795 + 234912 * 2 ^ 59
def prefixEnd_234912 : Nat := 4983230072969 + 3 ^ 40 * 234912 * 2
def baseEnd_234912 : Nat := 35740079261952633902123

theorem tailTrace_234912 : CollatzResearch.WordTrace tailWord_234912 prefixEnd_234912 35740079261952633902123 := by
  unfold tailWord_234912
  simp only [CollatzResearch.WordTrace]
  refine ⟨4283972262480709310305495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5711963016640945747073993 4283972262480709310305495)
  ·
    refine ⟨6425958393721063965458243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4283972262480709310305495 6425958393721063965458243)
    ·
      refine ⟨9638937590581595948187365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6425958393721063965458243 9638937590581595948187365)
      ·
        refine ⟨1807300798234049240285131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9638937590581595948187365 1807300798234049240285131)
        ·
          refine ⟨2710951197351073860427697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807300798234049240285131 2710951197351073860427697)
          ·
            refine ⟨2033213398013305395320773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2710951197351073860427697 2033213398013305395320773)
            ·
              refine ⟨381227512127494761622645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2033213398013305395320773 381227512127494761622645)
              ·
                refine ⟨35740079261952633902123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381227512127494761622645 35740079261952633902123)
                ·
                  rfl

theorem cell20_234912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_234912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234912 prefixEnd_234912 := by exact prefixLift 234912
  have htrace : WordTrace (prefixWord ++ tailWord_234912) baseStart_234912 baseEnd_234912 := by
    simpa [prefixWord, tailWord_234912, baseEnd_234912] using wordTrace_append hprefix tailTrace_234912
  have hstable : (prefixWord ++ tailWord_234912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234912).length < 2 ^ (prefixWord ++ tailWord_234912).sum := by decide
  have hdescent : baseEnd_234912 < baseStart_234912 := by decide
  rcases family_descends (prefixWord ++ tailWord_234912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234956 : List Nat := [2, 2, 1, 4, 2, 3, 2, 2, 2]
def baseStart_234956 : Nat := 118140960795 + 234956 * 2 ^ 59
def prefixEnd_234956 : Nat := 4983230072969 + 3 ^ 40 * 234956 * 2
def baseEnd_234956 : Nat := 107240320584789304239523

theorem tailTrace_234956 : CollatzResearch.WordTrace tailWord_234956 prefixEnd_234956 107240320584789304239523 := by
  unfold tailWord_234956
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284774668401007067606361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5713032891201342756808481 4284774668401007067606361)
  ·
    refine ⟨3213581001300755300704771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4284774668401007067606361 3213581001300755300704771)
    ·
      refine ⟨4820371501951132951057157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3213581001300755300704771 4820371501951132951057157)
      ·
        refine ⟨903819656615837428323217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4820371501951132951057157 903819656615837428323217)
        ·
          refine ⟨677864742461878071242413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903819656615837428323217 677864742461878071242413)
          ·
            refine ⟨254199278423204276715905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677864742461878071242413 254199278423204276715905)
            ·
              refine ⟨190649458817403207536929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254199278423204276715905 190649458817403207536929)
              ·
                refine ⟨142987094113052405652697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190649458817403207536929 142987094113052405652697)
                ·
                  refine ⟨107240320584789304239523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142987094113052405652697 107240320584789304239523)
                  ·
                    rfl

theorem cell20_234956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_234956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234956 prefixEnd_234956 := by exact prefixLift 234956
  have htrace : WordTrace (prefixWord ++ tailWord_234956) baseStart_234956 baseEnd_234956 := by
    simpa [prefixWord, tailWord_234956, baseEnd_234956] using wordTrace_append hprefix tailTrace_234956
  have hstable : (prefixWord ++ tailWord_234956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234956).length < 2 ^ (prefixWord ++ tailWord_234956).sum := by decide
  have hdescent : baseEnd_234956 < baseStart_234956 := by decide
  rcases family_descends (prefixWord ++ tailWord_234956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234981 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_234981 : Nat := 118140960795 + 234981 * 2 ^ 59
def prefixEnd_234981 : Nat := 4983230072969 + 3 ^ 40 * 234981 * 2
def baseEnd_234981 : Nat := 107251731266000328406087

theorem tailTrace_234981 : CollatzResearch.WordTrace tailWord_234981 prefixEnd_234981 107251731266000328406087 := by
  unfold tailWord_234981
  simp only [CollatzResearch.WordTrace]
  refine ⟨8570461161711443404872797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5713640774474295603248531 8570461161711443404872797)
  ·
    refine ⟨3213922935641791276827299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8570461161711443404872797 3213922935641791276827299)
    ·
      refine ⟨4820884403462686915240949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3213922935641791276827299 4820884403462686915240949)
      ·
        refine ⟨451957912824626898303839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4820884403462686915240949 451957912824626898303839)
        ·
          refine ⟨677936869236940347455759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451957912824626898303839 677936869236940347455759)
          ·
            refine ⟨1016905303855410521183639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677936869236940347455759 1016905303855410521183639)
            ·
              refine ⟨1525357955783115781775459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016905303855410521183639 1525357955783115781775459)
              ·
                refine ⟨2288036933674673672663189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525357955783115781775459 2288036933674673672663189)
                ·
                  refine ⟨107251731266000328406087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2288036933674673672663189 107251731266000328406087)
                  ·
                    rfl

theorem cell20_234981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_234981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_234981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_234981 prefixEnd_234981 := by exact prefixLift 234981
  have htrace : WordTrace (prefixWord ++ tailWord_234981) baseStart_234981 baseEnd_234981 := by
    simpa [prefixWord, tailWord_234981, baseEnd_234981] using wordTrace_append hprefix tailTrace_234981
  have hstable : (prefixWord ++ tailWord_234981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234981).length < 2 ^ (prefixWord ++ tailWord_234981).sum := by decide
  have hdescent : baseEnd_234981 < baseStart_234981 := by decide
  rcases family_descends (prefixWord ++ tailWord_234981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235002 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_235002 : Nat := 118140960795 + 235002 * 2 ^ 59
def prefixEnd_235002 : Nat := 4983230072969 + 3 ^ 40 * 235002 * 2
def baseEnd_235002 : Nat := 107261316238217588706001

theorem tailTrace_235002 : CollatzResearch.WordTrace tailWord_235002 prefixEnd_235002 107261316238217588706001 := by
  unfold tailWord_235002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142806773658840997846815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5714151396423575994258173 2142806773658840997846815)
  ·
    refine ⟨3214210160488261496770223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2142806773658840997846815 3214210160488261496770223)
    ·
      refine ⟨4821315240732392245155335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214210160488261496770223 4821315240732392245155335)
      ·
        refine ⟨7231972861098588367733003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821315240732392245155335 7231972861098588367733003)
        ·
          refine ⟨10847959291647882551599505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7231972861098588367733003 10847959291647882551599505)
          ·
            refine ⟨8135969468735911913699629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10847959291647882551599505 8135969468735911913699629)
            ·
              refine ⟨3050988550775966967637361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8135969468735911913699629 3050988550775966967637361)
              ·
                refine ⟨2288241413081975225728021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050988550775966967637361 2288241413081975225728021)
                ·
                  refine ⟨107261316238217588706001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2288241413081975225728021 107261316238217588706001)
                  ·
                    rfl

theorem cell20_235002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_235002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235002 prefixEnd_235002 := by exact prefixLift 235002
  have htrace : WordTrace (prefixWord ++ tailWord_235002) baseStart_235002 baseEnd_235002 := by
    simpa [prefixWord, tailWord_235002, baseEnd_235002] using wordTrace_append hprefix tailTrace_235002
  have hstable : (prefixWord ++ tailWord_235002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235002).length < 2 ^ (prefixWord ++ tailWord_235002).sum := by decide
  have hdescent : baseEnd_235002 < baseStart_235002 := by decide
  rcases family_descends (prefixWord ++ tailWord_235002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235029 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 3]
def baseStart_235029 : Nat := 118140960795 + 235029 * 2 ^ 59
def prefixEnd_235029 : Nat := 4983230072969 + 3 ^ 40 * 235029 * 2
def baseEnd_235029 : Nat := 107273639773925494805891

theorem tailTrace_235029 : CollatzResearch.WordTrace tailWord_235029 prefixEnd_235029 107273639773925494805891 := by
  unfold tailWord_235029
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572211865537547602620141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5714807910358365068413427 8572211865537547602620141)
  ·
    refine ⟨3214579449576580350982553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8572211865537547602620141 3214579449576580350982553)
    ·
      refine ⟨2410934587182435263236915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3214579449576580350982553 2410934587182435263236915)
      ·
        refine ⟨3616401880773652894855373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410934587182435263236915 3616401880773652894855373)
        ·
          refine ⟨1356150705290119835570765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3616401880773652894855373 1356150705290119835570765)
          ·
            refine ⟨508556514483794938339037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1356150705290119835570765 508556514483794938339037)
            ·
              refine ⟨190708692931423101877139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508556514483794938339037 190708692931423101877139)
              ·
                refine ⟨286063039397134652815709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190708692931423101877139 286063039397134652815709)
                ·
                  refine ⟨107273639773925494805891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286063039397134652815709 107273639773925494805891)
                  ·
                    rfl

theorem cell20_235029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_235029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235029 prefixEnd_235029 := by exact prefixLift 235029
  have htrace : WordTrace (prefixWord ++ tailWord_235029) baseStart_235029 baseEnd_235029 := by
    simpa [prefixWord, tailWord_235029, baseEnd_235029] using wordTrace_append hprefix tailTrace_235029
  have hstable : (prefixWord ++ tailWord_235029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235029).length < 2 ^ (prefixWord ++ tailWord_235029).sum := by decide
  have hdescent : baseEnd_235029 < baseStart_235029 := by decide
  rcases family_descends (prefixWord ++ tailWord_235029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235064 : List Nat := [2, 1, 2, 1, 4, 4, 6]
def baseStart_235064 : Nat := 118140960795 + 235064 * 2 ^ 59
def prefixEnd_235064 : Nat := 4983230072969 + 3 ^ 40 * 235064 * 2
def baseEnd_235064 : Nat := 11921068303068992071009

theorem tailTrace_235064 : CollatzResearch.WordTrace tailWord_235064 prefixEnd_235064 11921068303068992071009 := by
  unfold tailWord_235064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286744210205374290072123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5715658946940499053429497 4286744210205374290072123)
  ·
    refine ⟨6430116315308061435108185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4286744210205374290072123 6430116315308061435108185)
    ·
      refine ⟨4822587236481046076331139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6430116315308061435108185 4822587236481046076331139)
      ·
        refine ⟨7233880854721569114496709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822587236481046076331139 7233880854721569114496709)
        ·
          refine ⟨1356352660260294208968133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7233880854721569114496709 1356352660260294208968133)
          ·
            refine ⟨254316123798805164181525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1356352660260294208968133 254316123798805164181525)
            ·
              refine ⟨11921068303068992071009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 254316123798805164181525 11921068303068992071009)
              ·
                rfl

theorem cell20_235064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 6].length) (baseStart_235064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235064 prefixEnd_235064 := by exact prefixLift 235064
  have htrace : WordTrace (prefixWord ++ tailWord_235064) baseStart_235064 baseEnd_235064 := by
    simpa [prefixWord, tailWord_235064, baseEnd_235064] using wordTrace_append hprefix tailTrace_235064
  have hstable : (prefixWord ++ tailWord_235064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235064).length < 2 ^ (prefixWord ++ tailWord_235064).sum := by decide
  have hdescent : baseEnd_235064 < baseStart_235064 := by decide
  rcases family_descends (prefixWord ++ tailWord_235064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235071 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_235071 : Nat := 118140960795 + 235071 * 2 ^ 59
def prefixEnd_235071 : Nat := 4983230072969 + 3 ^ 40 * 235071 * 2
def baseEnd_235071 : Nat := 107292809718360015405719

theorem tailTrace_235071 : CollatzResearch.WordTrace tailWord_235071 prefixEnd_235071 107292809718360015405719 := by
  unfold tailWord_235071
  simp only [CollatzResearch.WordTrace]
  refine ⟨8573743731385388775649067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5715829154256925850432711 8573743731385388775649067)
  ·
    refine ⟨12860615597078083163473601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8573743731385388775649067 12860615597078083163473601)
    ·
      refine ⟨9645461697808562372605201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12860615597078083163473601 9645461697808562372605201)
      ·
        refine ⟨7234096273356421779453901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9645461697808562372605201 7234096273356421779453901)
        ·
          refine ⟨2712786102508658167295213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7234096273356421779453901 2712786102508658167295213)
          ·
            refine ⟨1017294788440746812735705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2712786102508658167295213 1017294788440746812735705)
            ·
              refine ⟨762971091330560109551779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017294788440746812735705 762971091330560109551779)
              ·
                refine ⟨1144456636995840164327669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762971091330560109551779 1144456636995840164327669)
                ·
                  refine ⟨107292809718360015405719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1144456636995840164327669 107292809718360015405719)
                  ·
                    rfl

theorem cell20_235071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_235071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235071 prefixEnd_235071 := by exact prefixLift 235071
  have htrace : WordTrace (prefixWord ++ tailWord_235071) baseStart_235071 baseEnd_235071 := by
    simpa [prefixWord, tailWord_235071, baseEnd_235071] using wordTrace_append hprefix tailTrace_235071
  have hstable : (prefixWord ++ tailWord_235071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235071).length < 2 ^ (prefixWord ++ tailWord_235071).sum := by decide
  have hdescent : baseEnd_235071 < baseStart_235071 := by decide
  rcases family_descends (prefixWord ++ tailWord_235071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235147 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 3]
def baseStart_235147 : Nat := 118140960795 + 235147 * 2 ^ 59
def prefixEnd_235147 : Nat := 4983230072969 + 3 ^ 40 * 235147 * 2
def baseEnd_235147 : Nat := 107327498189241528872075

theorem tailTrace_235147 : CollatzResearch.WordTrace tailWord_235147 prefixEnd_235147 107327498189241528872075 := by
  unfold tailWord_235147
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576515679110053755415695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5717677119406702503610463 8576515679110053755415695)
  ·
    refine ⟨12864773518665080633123543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8576515679110053755415695 12864773518665080633123543)
    ·
      refine ⟨19297160277997620949685315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12864773518665080633123543 19297160277997620949685315)
      ·
        refine ⟨28945740416996431424527973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19297160277997620949685315 28945740416996431424527973)
        ·
          refine ⟨5427326328186830892098995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28945740416996431424527973 5427326328186830892098995)
          ·
            refine ⟨8140989492280246338148493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427326328186830892098995 8140989492280246338148493)
            ·
              refine ⟨3052871059605092376805685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8140989492280246338148493 3052871059605092376805685)
              ·
                refine ⟨286206661837977410325533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3052871059605092376805685 286206661837977410325533)
                ·
                  refine ⟨107327498189241528872075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286206661837977410325533 107327498189241528872075)
                  ·
                    rfl

theorem cell20_235147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_235147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235147 prefixEnd_235147 := by exact prefixLift 235147
  have htrace : WordTrace (prefixWord ++ tailWord_235147) baseStart_235147 baseEnd_235147 := by
    simpa [prefixWord, tailWord_235147, baseEnd_235147] using wordTrace_append hprefix tailTrace_235147
  have hstable : (prefixWord ++ tailWord_235147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235147).length < 2 ^ (prefixWord ++ tailWord_235147).sum := by decide
  have hdescent : baseEnd_235147 < baseStart_235147 := by decide
  rcases family_descends (prefixWord ++ tailWord_235147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235199 : List Nat := [1, 1, 2, 2, 2, 3, 2, 7]
def baseStart_235199 : Nat := 118140960795 + 235199 * 2 ^ 59
def prefixEnd_235199 : Nat := 4983230072969 + 3 ^ 40 * 235199 * 2
def baseEnd_235199 : Nat := 35783744135386819712843

theorem tailTrace_235199 : CollatzResearch.WordTrace tailWord_235199 prefixEnd_235199 35783744135386819712843 := by
  unfold tailWord_235199
  simp only [CollatzResearch.WordTrace]
  refine ⟨8578412274921666636308651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5718941516614444424205767 8578412274921666636308651)
  ·
    refine ⟨12867618412382499954462977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8578412274921666636308651 12867618412382499954462977)
    ·
      refine ⟨9650713809286874965847233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12867618412382499954462977 9650713809286874965847233)
      ·
        refine ⟨7238035356965156224385425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9650713809286874965847233 7238035356965156224385425)
        ·
          refine ⟨5428526517723867168289069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7238035356965156224385425 5428526517723867168289069)
          ·
            refine ⟨2035697444146450188108401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5428526517723867168289069 2035697444146450188108401)
            ·
              refine ⟨1526773083109837641081301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035697444146450188108401 1526773083109837641081301)
              ·
                refine ⟨35783744135386819712843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1526773083109837641081301 35783744135386819712843)
                ·
                  rfl

theorem cell20_235199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_235199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235199 prefixEnd_235199 := by exact prefixLift 235199
  have htrace : WordTrace (prefixWord ++ tailWord_235199) baseStart_235199 baseEnd_235199 := by
    simpa [prefixWord, tailWord_235199, baseEnd_235199] using wordTrace_append hprefix tailTrace_235199
  have hstable : (prefixWord ++ tailWord_235199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235199).length < 2 ^ (prefixWord ++ tailWord_235199).sum := by decide
  have hdescent : baseEnd_235199 < baseStart_235199 := by decide
  rcases family_descends (prefixWord ++ tailWord_235199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235212 : List Nat := [2, 2, 1, 5, 2, 2, 2, 4]
def baseStart_235212 : Nat := 118140960795 + 235212 * 2 ^ 59
def prefixEnd_235212 : Nat := 4983230072969 + 3 ^ 40 * 235212 * 2
def baseEnd_235212 : Nat := 35785721986796730568381

theorem tailTrace_235212 : CollatzResearch.WordTrace tailWord_235212 prefixEnd_235212 35785721986796730568381 := by
  unfold tailWord_235212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4289443211937284928265945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5719257615916379904354593 4289443211937284928265945)
  ·
    refine ⟨3217082408952963696199459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4289443211937284928265945 3217082408952963696199459)
    ·
      refine ⟨4825623613429445544299189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3217082408952963696199459 4825623613429445544299189)
      ·
        refine ⟨452402213759010519778049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4825623613429445544299189 452402213759010519778049)
        ·
          refine ⟨339301660319257889833537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452402213759010519778049 339301660319257889833537)
          ·
            refine ⟨254476245239443417375153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339301660319257889833537 254476245239443417375153)
            ·
              refine ⟨190857183929582563031365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254476245239443417375153 190857183929582563031365)
              ·
                refine ⟨35785721986796730568381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190857183929582563031365 35785721986796730568381)
                ·
                  rfl

theorem cell20_235212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_235212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235212 prefixEnd_235212 := by exact prefixLift 235212
  have htrace : WordTrace (prefixWord ++ tailWord_235212) baseStart_235212 baseEnd_235212 := by
    simpa [prefixWord, tailWord_235212, baseEnd_235212] using wordTrace_append hprefix tailTrace_235212
  have hstable : (prefixWord ++ tailWord_235212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235212).length < 2 ^ (prefixWord ++ tailWord_235212).sum := by decide
  have hdescent : baseEnd_235212 < baseStart_235212 := by decide
  rcases family_descends (prefixWord ++ tailWord_235212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235226 : List Nat := [3, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_235226 : Nat := 118140960795 + 235226 * 2 ^ 59
def prefixEnd_235226 : Nat := 4983230072969 + 3 ^ 40 * 235226 * 2
def baseEnd_235226 : Nat := 107363555941868365238419

theorem tailTrace_235226 : CollatzResearch.WordTrace tailWord_235226 prefixEnd_235226 107363555941868365238419 := by
  unfold tailWord_235226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144849261455962561885383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5719598030549233498361021 2144849261455962561885383)
  ·
    refine ⟨3217273892183943842828075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2144849261455962561885383 3217273892183943842828075)
    ·
      refine ⟨4825910838275915764242113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3217273892183943842828075 4825910838275915764242113)
      ·
        refine ⟨3619433128706936823181585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4825910838275915764242113 3619433128706936823181585)
        ·
          refine ⟨2714574846530202617386189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3619433128706936823181585 2714574846530202617386189)
          ·
            refine ⟨1017965567448825981519821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2714574846530202617386189 1017965567448825981519821)
            ·
              refine ⟨381737087793309743069933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1017965567448825981519821 381737087793309743069933)
              ·
                refine ⟨143151407922491153651225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381737087793309743069933 143151407922491153651225)
                ·
                  refine ⟨107363555941868365238419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143151407922491153651225 107363555941868365238419)
                  ·
                    rfl

theorem cell20_235226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_235226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235226 prefixEnd_235226 := by exact prefixLift 235226
  have htrace : WordTrace (prefixWord ++ tailWord_235226) baseStart_235226 baseEnd_235226 := by
    simpa [prefixWord, tailWord_235226, baseEnd_235226] using wordTrace_append hprefix tailTrace_235226
  have hstable : (prefixWord ++ tailWord_235226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235226).length < 2 ^ (prefixWord ++ tailWord_235226).sum := by decide
  have hdescent : baseEnd_235226 < baseStart_235226 := by decide
  rcases family_descends (prefixWord ++ tailWord_235226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235233 : List Nat := [1, 2, 3, 1, 6, 1, 6]
def baseStart_235233 : Nat := 118140960795 + 235233 * 2 ^ 59
def prefixEnd_235233 : Nat := 4983230072969 + 3 ^ 40 * 235233 * 2
def baseEnd_235233 : Nat := 11929638992511939111673

theorem tailTrace_235233 : CollatzResearch.WordTrace tailWord_235233 prefixEnd_235233 11929638992511939111673 := by
  unfold tailWord_235233
  simp only [CollatzResearch.WordTrace]
  refine ⟨8579652356798490443046353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5719768237865660295364235 8579652356798490443046353)
  ·
    refine ⟨6434739267598867832284765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8579652356798490443046353 6434739267598867832284765)
    ·
      refine ⟨2413027225349575437106787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6434739267598867832284765 2413027225349575437106787)
      ·
        refine ⟨3619540838024363155660181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413027225349575437106787 3619540838024363155660181)
        ·
          refine ⟨169665976782392022921571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3619540838024363155660181 169665976782392022921571)
          ·
            refine ⟨254498965173588034382357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169665976782392022921571 254498965173588034382357)
            ·
              refine ⟨11929638992511939111673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 254498965173588034382357 11929638992511939111673)
              ·
                rfl

theorem cell20_235233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 6].length) (baseStart_235233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235233 prefixEnd_235233 := by exact prefixLift 235233
  have htrace : WordTrace (prefixWord ++ tailWord_235233) baseStart_235233 baseEnd_235233 := by
    simpa [prefixWord, tailWord_235233, baseEnd_235233] using wordTrace_append hprefix tailTrace_235233
  have hstable : (prefixWord ++ tailWord_235233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235233).length < 2 ^ (prefixWord ++ tailWord_235233).sum := by decide
  have hdescent : baseEnd_235233 < baseStart_235233 := by decide
  rcases family_descends (prefixWord ++ tailWord_235233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235254 : List Nat := [5, 1, 1, 1, 1, 3, 1, 7]
def baseStart_235254 : Nat := 118140960795 + 235254 * 2 ^ 59
def prefixEnd_235254 : Nat := 4983230072969 + 3 ^ 40 * 235254 * 2
def baseEnd_235254 : Nat := 35792111968274904101657

theorem tailTrace_235254 : CollatzResearch.WordTrace tailWord_235254 prefixEnd_235254 35792111968274904101657 := by
  unfold tailWord_235254
  simp only [CollatzResearch.WordTrace]
  refine ⟨536276143107650689347551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5720278859814940686373877 536276143107650689347551)
  ·
    refine ⟨804414214661476034021327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536276143107650689347551 804414214661476034021327)
    ·
      refine ⟨1206621321992214051031991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804414214661476034021327 1206621321992214051031991)
      ·
        refine ⟨1809931982988321076547987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206621321992214051031991 1809931982988321076547987)
        ·
          refine ⟨2714897974482481614821981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809931982988321076547987 2714897974482481614821981)
          ·
            refine ⟨1018086740430930605558243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2714897974482481614821981 1018086740430930605558243)
            ·
              refine ⟨1527130110646395908337365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018086740430930605558243 1527130110646395908337365)
              ·
                refine ⟨35792111968274904101657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1527130110646395908337365 35792111968274904101657)
                ·
                  rfl

theorem cell20_235254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_235254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235254 prefixEnd_235254 := by exact prefixLift 235254
  have htrace : WordTrace (prefixWord ++ tailWord_235254) baseStart_235254 baseEnd_235254 := by
    simpa [prefixWord, tailWord_235254, baseEnd_235254] using wordTrace_append hprefix tailTrace_235254
  have hstable : (prefixWord ++ tailWord_235254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235254).length < 2 ^ (prefixWord ++ tailWord_235254).sum := by decide
  have hdescent : baseEnd_235254 < baseStart_235254 := by decide
  rcases family_descends (prefixWord ++ tailWord_235254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235275 : List Nat := [1, 1, 1, 1, 5, 1, 4, 6]
def baseStart_235275 : Nat := 118140960795 + 235275 * 2 ^ 59
def prefixEnd_235275 : Nat := 4983230072969 + 3 ^ 40 * 235275 * 2
def baseEnd_235275 : Nat := 35795306959013990868295

theorem tailTrace_235275 : CollatzResearch.WordTrace tailWord_235275 prefixEnd_235275 35795306959013990868295 := by
  unfold tailWord_235275
  simp only [CollatzResearch.WordTrace]
  refine ⟨8581184222646331616075279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5720789481764221077383519 8581184222646331616075279)
  ·
    refine ⟨12871776333969497424112919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8581184222646331616075279 12871776333969497424112919)
    ·
      refine ⟨19307664500954246136169379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12871776333969497424112919 19307664500954246136169379)
      ·
        refine ⟨28961496751431369204254069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19307664500954246136169379 28961496751431369204254069)
        ·
          refine ⟨2715140320446690862898819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28961496751431369204254069 2715140320446690862898819)
          ·
            refine ⟨4072710480670036294348229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715140320446690862898819 4072710480670036294348229)
            ·
              refine ⟨763633215125631805190293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4072710480670036294348229 763633215125631805190293)
              ·
                refine ⟨35795306959013990868295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 763633215125631805190293 35795306959013990868295)
                ·
                  rfl

theorem cell20_235275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_235275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235275 prefixEnd_235275 := by exact prefixLift 235275
  have htrace : WordTrace (prefixWord ++ tailWord_235275) baseStart_235275 baseEnd_235275 := by
    simpa [prefixWord, tailWord_235275, baseEnd_235275] using wordTrace_append hprefix tailTrace_235275
  have hstable : (prefixWord ++ tailWord_235275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235275).length < 2 ^ (prefixWord ++ tailWord_235275).sum := by decide
  have hdescent : baseEnd_235275 < baseStart_235275 := by decide
  rcases family_descends (prefixWord ++ tailWord_235275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235294 : List Nat := [4, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_235294 : Nat := 118140960795 + 235294 * 2 ^ 59
def prefixEnd_235294 : Nat := 4983230072969 + 3 ^ 40 * 235294 * 2
def baseEnd_235294 : Nat := 107394592994762350971475

theorem tailTrace_235294 : CollatzResearch.WordTrace tailWord_235294 prefixEnd_235294 107394592994762350971475 := by
  unfold tailWord_235294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072734651197187232627117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5721251473051665240677957 1072734651197187232627117)
  ·
    refine ⟨402275494198945212235169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1072734651197187232627117 402275494198945212235169)
    ·
      refine ⟨301706620649208909176377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402275494198945212235169 301706620649208909176377)
      ·
        refine ⟨226279965486906681882283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301706620649208909176377 226279965486906681882283)
        ·
          refine ⟨339419948230360022823425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226279965486906681882283 339419948230360022823425)
          ·
            refine ⟨254564961172770017117569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339419948230360022823425 254564961172770017117569)
            ·
              refine ⟨190923720879577512838177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254564961172770017117569 190923720879577512838177)
              ·
                refine ⟨143192790659683134628633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190923720879577512838177 143192790659683134628633)
                ·
                  refine ⟨107394592994762350971475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143192790659683134628633 107394592994762350971475)
                  ·
                    rfl

theorem cell20_235294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_235294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235294 prefixEnd_235294 := by exact prefixLift 235294
  have htrace : WordTrace (prefixWord ++ tailWord_235294) baseStart_235294 baseEnd_235294 := by
    simpa [prefixWord, tailWord_235294, baseEnd_235294] using wordTrace_append hprefix tailTrace_235294
  have hstable : (prefixWord ++ tailWord_235294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235294).length < 2 ^ (prefixWord ++ tailWord_235294).sum := by decide
  have hdescent : baseEnd_235294 < baseStart_235294 := by decide
  rcases family_descends (prefixWord ++ tailWord_235294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235299 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 3]
def baseStart_235299 : Nat := 118140960795 + 235299 * 2 ^ 59
def prefixEnd_235299 : Nat := 4983230072969 + 3 ^ 40 * 235299 * 2
def baseEnd_235299 : Nat := 107396875131004555804787

theorem tailTrace_235299 : CollatzResearch.WordTrace tailWord_235299 prefixEnd_235299 107396875131004555804787 := by
  unfold tailWord_235299
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582059574559383714948951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5721373049706255809965967 8582059574559383714948951)
  ·
    refine ⟨12873089361839075572423427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8582059574559383714948951 12873089361839075572423427)
    ·
      refine ⟨19309634042758613358635141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12873089361839075572423427 19309634042758613358635141)
      ·
        refine ⟨3620556383017240004744089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19309634042758613358635141 3620556383017240004744089)
        ·
          refine ⟨2715417287262930003558067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620556383017240004744089 2715417287262930003558067)
          ·
            refine ⟨4073125930894395005337101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715417287262930003558067 4073125930894395005337101)
            ·
              refine ⟨1527422224085398127001413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4073125930894395005337101 1527422224085398127001413)
              ·
                refine ⟨286391667016012148812765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1527422224085398127001413 286391667016012148812765)
                ·
                  refine ⟨107396875131004555804787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286391667016012148812765 107396875131004555804787)
                  ·
                    rfl

theorem cell20_235299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_235299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235299 prefixEnd_235299 := by exact prefixLift 235299
  have htrace : WordTrace (prefixWord ++ tailWord_235299) baseStart_235299 baseEnd_235299 := by
    simpa [prefixWord, tailWord_235299, baseEnd_235299] using wordTrace_append hprefix tailTrace_235299
  have hstable : (prefixWord ++ tailWord_235299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235299).length < 2 ^ (prefixWord ++ tailWord_235299).sum := by decide
  have hdescent : baseEnd_235299 < baseStart_235299 := by decide
  rcases family_descends (prefixWord ++ tailWord_235299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235361 : List Nat := [1, 2, 3, 1, 1, 1, 3, 6, 2]
def baseStart_235361 : Nat := 118140960795 + 235361 * 2 ^ 59
def prefixEnd_235361 : Nat := 4983230072969 + 3 ^ 40 * 235361 * 2
def baseEnd_235361 : Nat := 107425173620407895737867

theorem tailTrace_235361 : CollatzResearch.WordTrace tailWord_235361 prefixEnd_235361 107425173620407895737867 := by
  unfold tailWord_235361
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584320900334768303705937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5722880600223178869137291 8584320900334768303705937)
  ·
    refine ⟨6438240675251076227779453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8584320900334768303705937 6438240675251076227779453)
    ·
      refine ⟨2414340253219153585417295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6438240675251076227779453 2414340253219153585417295)
      ·
        refine ⟨3621510379828730378125943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414340253219153585417295 3621510379828730378125943)
        ·
          refine ⟨5432265569743095567188915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621510379828730378125943 5432265569743095567188915)
          ·
            refine ⟨8148398354614643350783373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432265569743095567188915 8148398354614643350783373)
            ·
              refine ⟨3055649382980491256543765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8148398354614643350783373 3055649382980491256543765)
              ·
                refine ⟨143233564827210527650489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3055649382980491256543765 143233564827210527650489)
                ·
                  refine ⟨107425173620407895737867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143233564827210527650489 107425173620407895737867)
                  ·
                    rfl

theorem cell20_235361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_235361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235361 prefixEnd_235361 := by exact prefixLift 235361
  have htrace : WordTrace (prefixWord ++ tailWord_235361) baseStart_235361 baseEnd_235361 := by
    simpa [prefixWord, tailWord_235361, baseEnd_235361] using wordTrace_append hprefix tailTrace_235361
  have hstable : (prefixWord ++ tailWord_235361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235361).length < 2 ^ (prefixWord ++ tailWord_235361).sum := by decide
  have hdescent : baseEnd_235361 < baseStart_235361 := by decide
  rcases family_descends (prefixWord ++ tailWord_235361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235413 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 3]
def baseStart_235413 : Nat := 118140960795 + 235413 * 2 ^ 59
def prefixEnd_235413 : Nat := 4983230072969 + 3 ^ 40 * 235413 * 2
def baseEnd_235413 : Nat := 107448907837326826004321

theorem tailTrace_235413 : CollatzResearch.WordTrace tailWord_235413 prefixEnd_235413 107448907837326826004321 := by
  unfold tailWord_235413
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586217496146381184598893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5724144997430920789732595 8586217496146381184598893)
  ·
    refine ⟨3219831561054892944224585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8586217496146381184598893 3219831561054892944224585)
    ·
      refine ⟨2414873670791169708168439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3219831561054892944224585 2414873670791169708168439)
      ·
        refine ⟨3622310506186754562252659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414873670791169708168439 3622310506186754562252659)
        ·
          refine ⟨5433465759280131843378989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622310506186754562252659 5433465759280131843378989)
          ·
            refine ⟨2037549659730049441267121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5433465759280131843378989 2037549659730049441267121)
            ·
              refine ⟨1528162244797537080950341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037549659730049441267121 1528162244797537080950341)
              ·
                refine ⟨286530420899538202678189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1528162244797537080950341 286530420899538202678189)
                ·
                  refine ⟨107448907837326826004321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286530420899538202678189 107448907837326826004321)
                  ·
                    rfl

theorem cell20_235413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_235413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235413 prefixEnd_235413 := by exact prefixLift 235413
  have htrace : WordTrace (prefixWord ++ tailWord_235413) baseStart_235413 baseEnd_235413 := by
    simpa [prefixWord, tailWord_235413, baseEnd_235413] using wordTrace_append hprefix tailTrace_235413
  have hstable : (prefixWord ++ tailWord_235413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235413).length < 2 ^ (prefixWord ++ tailWord_235413).sum := by decide
  have hdescent : baseEnd_235413 < baseStart_235413 := by decide
  rcases family_descends (prefixWord ++ tailWord_235413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235422 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_235422 : Nat := 118140960795 + 235422 * 2 ^ 59
def prefixEnd_235422 : Nat := 4983230072969 + 3 ^ 40 * 235422 * 2
def baseEnd_235422 : Nat := 107453015682562794704285

theorem tailTrace_235422 : CollatzResearch.WordTrace tailWord_235422 prefixEnd_235422 107453015682562794704285 := by
  unfold tailWord_235422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1073318219139221965209565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5724363835409183814451013 1073318219139221965209565)
  ·
    refine ⟨402494332177208236953587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1073318219139221965209565 402494332177208236953587)
    ·
      refine ⟨603741498265812355430381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402494332177208236953587 603741498265812355430381)
      ·
        refine ⟨226403061849679633286393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 603741498265812355430381 226403061849679633286393)
        ·
          refine ⟨169802296387259724964795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226403061849679633286393 169802296387259724964795)
          ·
            refine ⟨254703444580889587447193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169802296387259724964795 254703444580889587447193)
            ·
              refine ⟨191027583435667190585395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254703444580889587447193 191027583435667190585395)
              ·
                refine ⟨286541375153500785878093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191027583435667190585395 286541375153500785878093)
                ·
                  refine ⟨107453015682562794704285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286541375153500785878093 107453015682562794704285)
                  ·
                    rfl

theorem cell20_235422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_235422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235422 prefixEnd_235422 := by exact prefixLift 235422
  have htrace : WordTrace (prefixWord ++ tailWord_235422) baseStart_235422 baseEnd_235422 := by
    simpa [prefixWord, tailWord_235422, baseEnd_235422] using wordTrace_append hprefix tailTrace_235422
  have hstable : (prefixWord ++ tailWord_235422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235422).length < 2 ^ (prefixWord ++ tailWord_235422).sum := by decide
  have hdescent : baseEnd_235422 < baseStart_235422 := by decide
  rcases family_descends (prefixWord ++ tailWord_235422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235426 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_235426 : Nat := 118140960795 + 235426 * 2 ^ 59
def prefixEnd_235426 : Nat := 4983230072969 + 3 ^ 40 * 235426 * 2
def baseEnd_235426 : Nat := 107454841391556558570935

theorem tailTrace_235426 : CollatzResearch.WordTrace tailWord_235426 prefixEnd_235426 107454841391556558570935 := by
  unfold tailWord_235426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2146672911274821101205533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5724461096732856269881421 2146672911274821101205533)
  ·
    refine ⟨805002341728057912952075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2146672911274821101205533 805002341728057912952075)
    ·
      refine ⟨1207503512592086869428113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805002341728057912952075 1207503512592086869428113)
      ·
        refine ⟨905627634444065152071085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1207503512592086869428113 905627634444065152071085)
        ·
          refine ⟨339610362916524432026657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 905627634444065152071085 339610362916524432026657)
          ·
            refine ⟨254707772187393324019993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339610362916524432026657 254707772187393324019993)
            ·
              refine ⟨191030829140544993014995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254707772187393324019993 191030829140544993014995)
              ·
                refine ⟨286546243710817489522493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191030829140544993014995 286546243710817489522493)
                ·
                  refine ⟨107454841391556558570935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286546243710817489522493 107454841391556558570935)
                  ·
                    rfl

theorem cell20_235426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_235426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235426 prefixEnd_235426 := by exact prefixLift 235426
  have htrace : WordTrace (prefixWord ++ tailWord_235426) baseStart_235426 baseEnd_235426 := by
    simpa [prefixWord, tailWord_235426, baseEnd_235426] using wordTrace_append hprefix tailTrace_235426
  have hstable : (prefixWord ++ tailWord_235426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235426).length < 2 ^ (prefixWord ++ tailWord_235426).sum := by decide
  have hdescent : baseEnd_235426 < baseStart_235426 := by decide
  rcases family_descends (prefixWord ++ tailWord_235426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235468 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_235468 : Nat := 118140960795 + 235468 * 2 ^ 59
def prefixEnd_235468 : Nat := 4983230072969 + 3 ^ 40 * 235468 * 2
def baseEnd_235468 : Nat := 107474011335991079170763

theorem tailTrace_235468 : CollatzResearch.WordTrace tailWord_235468 prefixEnd_235468 107474011335991079170763 := by
  unfold tailWord_235468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294111755473562788925529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5725482340631417051900705 4294111755473562788925529)
  ·
    refine ⟨3220583816605172091694147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4294111755473562788925529 3220583816605172091694147)
    ·
      refine ⟨4830875724907758137541221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3220583816605172091694147 4830875724907758137541221)
      ·
        refine ⟨905789198420204650788979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4830875724907758137541221 905789198420204650788979)
        ·
          refine ⟨1358683797630306976183469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905789198420204650788979 1358683797630306976183469)
          ·
            refine ⟨509506424111365116068801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1358683797630306976183469 509506424111365116068801)
            ·
              refine ⟨382129818083523837051601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509506424111365116068801 382129818083523837051601)
              ·
                refine ⟨286597363562642877788701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382129818083523837051601 286597363562642877788701)
                ·
                  refine ⟨107474011335991079170763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286597363562642877788701 107474011335991079170763)
                  ·
                    rfl

theorem cell20_235468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_235468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235468 prefixEnd_235468 := by exact prefixLift 235468
  have htrace : WordTrace (prefixWord ++ tailWord_235468) baseStart_235468 baseEnd_235468 := by
    simpa [prefixWord, tailWord_235468, baseEnd_235468] using wordTrace_append hprefix tailTrace_235468
  have hstable : (prefixWord ++ tailWord_235468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235468).length < 2 ^ (prefixWord ++ tailWord_235468).sum := by decide
  have hdescent : baseEnd_235468 < baseStart_235468 := by decide
  rcases family_descends (prefixWord ++ tailWord_235468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235472 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_235472 : Nat := 118140960795 + 235472 * 2 ^ 59
def prefixEnd_235472 : Nat := 4983230072969 + 3 ^ 40 * 235472 * 2
def baseEnd_235472 : Nat := 107475837044984843037413

theorem tailTrace_235472 : CollatzResearch.WordTrace tailWord_235472 prefixEnd_235472 107475837044984843037413 := by
  unfold tailWord_235472
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294184701466317130498335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5725579601955089507331113 4294184701466317130498335)
  ·
    refine ⟨6441277052199475695747503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294184701466317130498335 6441277052199475695747503)
    ·
      refine ⟨9661915578299213543621255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441277052199475695747503 9661915578299213543621255)
      ·
        refine ⟨14492873367448820315431883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9661915578299213543621255 14492873367448820315431883)
        ·
          refine ⟨21739310051173230473147825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14492873367448820315431883 21739310051173230473147825)
          ·
            refine ⟨16304482538379922854860869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21739310051173230473147825 16304482538379922854860869)
            ·
              refine ⟨3057090475946235535286413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16304482538379922854860869 3057090475946235535286413)
              ·
                refine ⟨1146408928479838325732405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3057090475946235535286413 1146408928479838325732405)
                ·
                  refine ⟨107475837044984843037413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1146408928479838325732405 107475837044984843037413)
                  ·
                    rfl

theorem cell20_235472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_235472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235472 prefixEnd_235472 := by exact prefixLift 235472
  have htrace : WordTrace (prefixWord ++ tailWord_235472) baseStart_235472 baseEnd_235472 := by
    simpa [prefixWord, tailWord_235472, baseEnd_235472] using wordTrace_append hprefix tailTrace_235472
  have hstable : (prefixWord ++ tailWord_235472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235472).length < 2 ^ (prefixWord ++ tailWord_235472).sum := by decide
  have hdescent : baseEnd_235472 < baseStart_235472 := by decide
  rcases family_descends (prefixWord ++ tailWord_235472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235478 : List Nat := [5, 2, 1, 1, 3, 2, 1, 5]
def baseStart_235478 : Nat := 118140960795 + 235478 * 2 ^ 59
def prefixEnd_235478 : Nat := 4983230072969 + 3 ^ 40 * 235478 * 2
def baseEnd_235478 : Nat := 35826191869491829612463

theorem tailTrace_235478 : CollatzResearch.WordTrace tailWord_235478 prefixEnd_235478 35826191869491829612463 := by
  unfold tailWord_235478
  simp only [CollatzResearch.WordTrace]
  refine ⟨536786765056931080357193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5725725493940598190476725 536786765056931080357193)
  ·
    refine ⟨402590073792698310267895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 536786765056931080357193 402590073792698310267895)
    ·
      refine ⟨603885110689047465401843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402590073792698310267895 603885110689047465401843)
      ·
        refine ⟨905827666033571198102765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603885110689047465401843 905827666033571198102765)
        ·
          refine ⟨339685374762589199288537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 905827666033571198102765 339685374762589199288537)
          ·
            refine ⟨254764031071941899466403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339685374762589199288537 254764031071941899466403)
            ·
              refine ⟨382146046607912849199605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254764031071941899466403 382146046607912849199605)
              ·
                refine ⟨35826191869491829612463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 382146046607912849199605 35826191869491829612463)
                ·
                  rfl

theorem cell20_235478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_235478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235478 prefixEnd_235478 := by exact prefixLift 235478
  have htrace : WordTrace (prefixWord ++ tailWord_235478) baseStart_235478 baseEnd_235478 := by
    simpa [prefixWord, tailWord_235478, baseEnd_235478] using wordTrace_append hprefix tailTrace_235478
  have hstable : (prefixWord ++ tailWord_235478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235478).length < 2 ^ (prefixWord ++ tailWord_235478).sum := by decide
  have hdescent : baseEnd_235478 < baseStart_235478 := by decide
  rcases family_descends (prefixWord ++ tailWord_235478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235489 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 3]
def baseStart_235489 : Nat := 118140960795 + 235489 * 2 ^ 59
def prefixEnd_235489 : Nat := 4983230072969 + 3 ^ 40 * 235489 * 2
def baseEnd_235489 : Nat := 107483596308208339470677

theorem tailTrace_235489 : CollatzResearch.WordTrace tailWord_235489 prefixEnd_235489 107483596308208339470677 := by
  unfold tailWord_235489
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588989443871046164365521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5725992962580697442910347 8588989443871046164365521)
  ·
    refine ⟨6441742082903284623274141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8588989443871046164365521 6441742082903284623274141)
    ·
      refine ⟨2415653281088731733727803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6441742082903284623274141 2415653281088731733727803)
      ·
        refine ⟨3623479921633097600591705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415653281088731733727803 3623479921633097600591705)
        ·
          refine ⟨2717609941224823200443779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3623479921633097600591705 2717609941224823200443779)
          ·
            refine ⟨4076414911837234800665669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717609941224823200443779 4076414911837234800665669)
            ·
              refine ⟨764327795969481525124813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4076414911837234800665669 764327795969481525124813)
              ·
                refine ⟨286622923488555571921805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 764327795969481525124813 286622923488555571921805)
                ·
                  refine ⟨107483596308208339470677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286622923488555571921805 107483596308208339470677)
                  ·
                    rfl

theorem cell20_235489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_235489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235489 prefixEnd_235489 := by exact prefixLift 235489
  have htrace : WordTrace (prefixWord ++ tailWord_235489) baseStart_235489 baseEnd_235489 := by
    simpa [prefixWord, tailWord_235489, baseEnd_235489] using wordTrace_append hprefix tailTrace_235489
  have hstable : (prefixWord ++ tailWord_235489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235489).length < 2 ^ (prefixWord ++ tailWord_235489).sum := by decide
  have hdescent : baseEnd_235489 < baseStart_235489 := by decide
  rcases family_descends (prefixWord ++ tailWord_235489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235513 : List Nat := [1, 2, 1, 3, 1, 4, 1, 5, 2]
def baseStart_235513 : Nat := 118140960795 + 235513 * 2 ^ 59
def prefixEnd_235513 : Nat := 4983230072969 + 3 ^ 40 * 235513 * 2
def baseEnd_235513 : Nat := 107494550562170922670579

theorem tailTrace_235513 : CollatzResearch.WordTrace tailWord_235513 prefixEnd_235513 107494550562170922670579 := by
  unfold tailWord_235513
  simp only [CollatzResearch.WordTrace]
  refine ⟨8589864795784098263239193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5726576530522732175492795 8589864795784098263239193)
  ·
    refine ⟨6442398596838073697429395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8589864795784098263239193 6442398596838073697429395)
    ·
      refine ⟨9663597895257110546144093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6442398596838073697429395 9663597895257110546144093)
      ·
        refine ⟨3623849210721416454804035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9663597895257110546144093 3623849210721416454804035)
        ·
          refine ⟨5435773816082124682206053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623849210721416454804035 5435773816082124682206053)
          ·
            refine ⟨1019207590515398377913635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5435773816082124682206053 1019207590515398377913635)
            ·
              refine ⟨1528811385773097566870453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019207590515398377913635 1528811385773097566870453)
              ·
                refine ⟨143326067416227896894105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1528811385773097566870453 143326067416227896894105)
                ·
                  refine ⟨107494550562170922670579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143326067416227896894105 107494550562170922670579)
                  ·
                    rfl

theorem cell20_235513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_235513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235513 prefixEnd_235513 := by exact prefixLift 235513
  have htrace : WordTrace (prefixWord ++ tailWord_235513) baseStart_235513 baseEnd_235513 := by
    simpa [prefixWord, tailWord_235513, baseEnd_235513] using wordTrace_append hprefix tailTrace_235513
  have hstable : (prefixWord ++ tailWord_235513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235513).length < 2 ^ (prefixWord ++ tailWord_235513).sum := by decide
  have hdescent : baseEnd_235513 < baseStart_235513 := by decide
  rcases family_descends (prefixWord ++ tailWord_235513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235527 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_235527 : Nat := 118140960795 + 235527 * 2 ^ 59
def prefixEnd_235527 : Nat := 4983230072969 + 3 ^ 40 * 235527 * 2
def baseEnd_235527 : Nat := 107500940543649096203855

theorem tailTrace_235527 : CollatzResearch.WordTrace tailWord_235527 prefixEnd_235527 107500940543649096203855 := by
  unfold tailWord_235527
  simp only [CollatzResearch.WordTrace]
  refine ⟨8590375417733378654248835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5726916945155585769499223 8590375417733378654248835)
  ·
    refine ⟨12885563126600067981373253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8590375417733378654248835 12885563126600067981373253)
    ·
      refine ⟨2416043086237512746507485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12885563126600067981373253 2416043086237512746507485)
      ·
        refine ⟨906016157339067279940307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2416043086237512746507485 906016157339067279940307)
        ·
          refine ⟨1359024236008600919910461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906016157339067279940307 1359024236008600919910461)
          ·
            refine ⟨509634088503225344966423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1359024236008600919910461 509634088503225344966423)
            ·
              refine ⟨764451132754838017449635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509634088503225344966423 764451132754838017449635)
              ·
                refine ⟨1146676699132257026174453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764451132754838017449635 1146676699132257026174453)
                ·
                  refine ⟨107500940543649096203855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1146676699132257026174453 107500940543649096203855)
                  ·
                    rfl

theorem cell20_235527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_235527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235527 prefixEnd_235527 := by exact prefixLift 235527
  have htrace : WordTrace (prefixWord ++ tailWord_235527) baseStart_235527 baseEnd_235527 := by
    simpa [prefixWord, tailWord_235527, baseEnd_235527] using wordTrace_append hprefix tailTrace_235527
  have hstable : (prefixWord ++ tailWord_235527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235527).length < 2 ^ (prefixWord ++ tailWord_235527).sum := by decide
  have hdescent : baseEnd_235527 < baseStart_235527 := by decide
  rcases family_descends (prefixWord ++ tailWord_235527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235544 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_235544 : Nat := 118140960795 + 235544 * 2 ^ 59
def prefixEnd_235544 : Nat := 4983230072969 + 3 ^ 40 * 235544 * 2
def baseEnd_235544 : Nat := 107508699806872592637119

theorem tailTrace_235544 : CollatzResearch.WordTrace tailWord_235544 prefixEnd_235544 107508699806872592637119 := by
  unfold tailWord_235544
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295497729335895278808843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5727330305781193705078457 4295497729335895278808843)
  ·
    refine ⟨6443246594003842918213265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295497729335895278808843 6443246594003842918213265)
    ·
      refine ⟨4832434945502882188659949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6443246594003842918213265 4832434945502882188659949)
      ·
        refine ⟨1812163104563580820747481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4832434945502882188659949 1812163104563580820747481)
        ·
          refine ⟨1359122328422685615560611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812163104563580820747481 1359122328422685615560611)
          ·
            refine ⟨2038683492634028423340917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359122328422685615560611 2038683492634028423340917)
            ·
              refine ⟨191126577434440164688211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2038683492634028423340917 191126577434440164688211)
              ·
                refine ⟨286689866151660247032317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191126577434440164688211 286689866151660247032317)
                ·
                  refine ⟨107508699806872592637119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286689866151660247032317 107508699806872592637119)
                  ·
                    rfl

theorem cell20_235544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_235544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235544 prefixEnd_235544 := by exact prefixLift 235544
  have htrace : WordTrace (prefixWord ++ tailWord_235544) baseStart_235544 baseEnd_235544 := by
    simpa [prefixWord, tailWord_235544, baseEnd_235544] using wordTrace_append hprefix tailTrace_235544
  have hstable : (prefixWord ++ tailWord_235544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235544).length < 2 ^ (prefixWord ++ tailWord_235544).sum := by decide
  have hdescent : baseEnd_235544 < baseStart_235544 := by decide
  rcases family_descends (prefixWord ++ tailWord_235544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235568 : List Nat := [2, 1, 1, 1, 2, 7, 1, 3, 2]
def baseStart_235568 : Nat := 118140960795 + 235568 * 2 ^ 59
def prefixEnd_235568 : Nat := 4983230072969 + 3 ^ 40 * 235568 * 2
def baseEnd_235568 : Nat := 107519654060835175837021

theorem tailTrace_235568 : CollatzResearch.WordTrace tailWord_235568 prefixEnd_235568 107519654060835175837021 := by
  unfold tailWord_235568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295935405292421328245679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5727913873723228437660905 4295935405292421328245679)
  ·
    refine ⟨6443903107938631992368519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295935405292421328245679 6443903107938631992368519)
    ·
      refine ⟨9665854661907947988552779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6443903107938631992368519 9665854661907947988552779)
      ·
        refine ⟨14498781992861921982829169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665854661907947988552779 14498781992861921982829169)
        ·
          refine ⟨10874086494646441487121877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14498781992861921982829169 10874086494646441487121877)
          ·
            refine ⟨254861402218275972354419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10874086494646441487121877 254861402218275972354419)
            ·
              refine ⟨382292103327413958531629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254861402218275972354419 382292103327413958531629)
              ·
                refine ⟨143359538747780234449361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382292103327413958531629 143359538747780234449361)
                ·
                  refine ⟨107519654060835175837021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143359538747780234449361 107519654060835175837021)
                  ·
                    rfl

theorem cell20_235568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_235568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235568 prefixEnd_235568 := by exact prefixLift 235568
  have htrace : WordTrace (prefixWord ++ tailWord_235568) baseStart_235568 baseEnd_235568 := by
    simpa [prefixWord, tailWord_235568, baseEnd_235568] using wordTrace_append hprefix tailTrace_235568
  have hstable : (prefixWord ++ tailWord_235568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235568).length < 2 ^ (prefixWord ++ tailWord_235568).sum := by decide
  have hdescent : baseEnd_235568 < baseStart_235568 := by decide
  rcases family_descends (prefixWord ++ tailWord_235568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235585 : List Nat := [1, 2, 5, 1, 2, 2, 3, 2, 2]
def baseStart_235585 : Nat := 118140960795 + 235585 * 2 ^ 59
def prefixEnd_235585 : Nat := 4983230072969 + 3 ^ 40 * 235585 * 2
def baseEnd_235585 : Nat := 107527413324058672270285

theorem tailTrace_235585 : CollatzResearch.WordTrace tailWord_235585 prefixEnd_235585 107527413324058672270285 := by
  unfold tailWord_235585
  simp only [CollatzResearch.WordTrace]
  refine ⟨8592490851523254559860209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5728327234348836373240139 8592490851523254559860209)
  ·
    refine ⟨6444368138642440919895157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8592490851523254559860209 6444368138642440919895157)
    ·
      refine ⟨604159512997728836240171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6444368138642440919895157 604159512997728836240171)
      ·
        refine ⟨906239269496593254360257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604159512997728836240171 906239269496593254360257)
        ·
          refine ⟨679679452122444940770193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906239269496593254360257 679679452122444940770193)
          ·
            refine ⟨509759589091833705577645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679679452122444940770193 509759589091833705577645)
            ·
              refine ⟨191159845909437639591617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509759589091833705577645 191159845909437639591617)
              ·
                refine ⟨143369884432078229693713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191159845909437639591617 143369884432078229693713)
                ·
                  refine ⟨107527413324058672270285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143369884432078229693713 107527413324058672270285)
                  ·
                    rfl

theorem cell20_235585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_235585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235585 prefixEnd_235585 := by exact prefixLift 235585
  have htrace : WordTrace (prefixWord ++ tailWord_235585) baseStart_235585 baseEnd_235585 := by
    simpa [prefixWord, tailWord_235585, baseEnd_235585] using wordTrace_append hprefix tailTrace_235585
  have hstable : (prefixWord ++ tailWord_235585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235585).length < 2 ^ (prefixWord ++ tailWord_235585).sum := by decide
  have hdescent : baseEnd_235585 < baseStart_235585 := by decide
  rcases family_descends (prefixWord ++ tailWord_235585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235641 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 3]
def baseStart_235641 : Nat := 118140960795 + 235641 * 2 ^ 59
def prefixEnd_235641 : Nat := 4983230072969 + 3 ^ 40 * 235641 * 2
def baseEnd_235641 : Nat := 107552973249971366403389

theorem tailTrace_235641 : CollatzResearch.WordTrace tailWord_235641 prefixEnd_235641 107552973249971366403389 := by
  unfold tailWord_235641
  simp only [CollatzResearch.WordTrace]
  refine ⟨8594533339320376123898777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5729688892880250749265851 8594533339320376123898777)
  ·
    refine ⟨6445900004490282092924083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8594533339320376123898777 6445900004490282092924083)
    ·
      refine ⟨9668850006735423139386125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6445900004490282092924083 9668850006735423139386125)
      ·
        refine ⟨3625818752525783677269797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9668850006735423139386125 3625818752525783677269797)
        ·
          refine ⟨679841016098584439488087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3625818752525783677269797 679841016098584439488087)
          ·
            refine ⟨1019761524147876659232131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679841016098584439488087 1019761524147876659232131)
            ·
              refine ⟨1529642286221814988848197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019761524147876659232131 1529642286221814988848197)
              ·
                refine ⟨286807928666590310409037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1529642286221814988848197 286807928666590310409037)
                ·
                  refine ⟨107552973249971366403389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286807928666590310409037 107552973249971366403389)
                  ·
                    rfl

theorem cell20_235641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_235641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235641 prefixEnd_235641 := by exact prefixLift 235641
  have htrace : WordTrace (prefixWord ++ tailWord_235641) baseStart_235641 baseEnd_235641 := by
    simpa [prefixWord, tailWord_235641, baseEnd_235641] using wordTrace_append hprefix tailTrace_235641
  have hstable : (prefixWord ++ tailWord_235641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235641).length < 2 ^ (prefixWord ++ tailWord_235641).sum := by decide
  have hdescent : baseEnd_235641 < baseStart_235641 := by decide
  rcases family_descends (prefixWord ++ tailWord_235641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235644 : List Nat := [2, 2, 2, 1, 1, 4, 4, 2, 2]
def baseStart_235644 : Nat := 118140960795 + 235644 * 2 ^ 59
def prefixEnd_235644 : Nat := 4983230072969 + 3 ^ 40 * 235644 * 2
def baseEnd_235644 : Nat := 107554342531716689303377

theorem tailTrace_235644 : CollatzResearch.WordTrace tailWord_235644 prefixEnd_235644 107554342531716689303377 := by
  unfold tailWord_235644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297321379154753818128993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5729761838873005090838657 4297321379154753818128993)
  ·
    refine ⟨3222991034366065363596745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4297321379154753818128993 3222991034366065363596745)
    ·
      refine ⟨2417243275774549022697559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3222991034366065363596745 2417243275774549022697559)
      ·
        refine ⟨3625864913661823534046339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417243275774549022697559 3625864913661823534046339)
        ·
          refine ⟨5438797370492735301069509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625864913661823534046339 5438797370492735301069509)
          ·
            refine ⟨1019774506967387868950533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5438797370492735301069509 1019774506967387868950533)
            ·
              refine ⟨191207720056385225428225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1019774506967387868950533 191207720056385225428225)
              ·
                refine ⟨143405790042288919071169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191207720056385225428225 143405790042288919071169)
                ·
                  refine ⟨107554342531716689303377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143405790042288919071169 107554342531716689303377)
                  ·
                    rfl

theorem cell20_235644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_235644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235644 prefixEnd_235644 := by exact prefixLift 235644
  have htrace : WordTrace (prefixWord ++ tailWord_235644) baseStart_235644 baseEnd_235644 := by
    simpa [prefixWord, tailWord_235644, baseEnd_235644] using wordTrace_append hprefix tailTrace_235644
  have hstable : (prefixWord ++ tailWord_235644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235644).length < 2 ^ (prefixWord ++ tailWord_235644).sum := by decide
  have hdescent : baseEnd_235644 < baseStart_235644 := by decide
  rcases family_descends (prefixWord ++ tailWord_235644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235655 : List Nat := [1, 1, 4, 2, 1, 1, 5, 5]
def baseStart_235655 : Nat := 118140960795 + 235655 * 2 ^ 59
def prefixEnd_235655 : Nat := 4983230072969 + 3 ^ 40 * 235655 * 2
def baseEnd_235655 : Nat := 35853121077149846645555

theorem tailTrace_235655 : CollatzResearch.WordTrace tailWord_235655 prefixEnd_235655 35853121077149846645555 := by
  unfold tailWord_235655
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595043961269656514908419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5730029307513104343272279 8595043961269656514908419)
  ·
    refine ⟨12892565941904484772362629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8595043961269656514908419 12892565941904484772362629)
    ·
      refine ⟨2417356114107090894817993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12892565941904484772362629 2417356114107090894817993)
      ·
        refine ⟨1813017085580318171113495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2417356114107090894817993 1813017085580318171113495)
        ·
          refine ⟨2719525628370477256670243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813017085580318171113495 2719525628370477256670243)
          ·
            refine ⟨4079288442555715885005365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719525628370477256670243 4079288442555715885005365)
            ·
              refine ⟨382433291489598364219253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4079288442555715885005365 382433291489598364219253)
              ·
                refine ⟨35853121077149846645555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 382433291489598364219253 35853121077149846645555)
                ·
                  rfl

theorem cell20_235655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_235655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235655 prefixEnd_235655 := by exact prefixLift 235655
  have htrace : WordTrace (prefixWord ++ tailWord_235655) baseStart_235655 baseEnd_235655 := by
    simpa [prefixWord, tailWord_235655, baseEnd_235655] using wordTrace_append hprefix tailTrace_235655
  have hstable : (prefixWord ++ tailWord_235655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235655).length < 2 ^ (prefixWord ++ tailWord_235655).sum := by decide
  have hdescent : baseEnd_235655 < baseStart_235655 := by decide
  rcases family_descends (prefixWord ++ tailWord_235655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235668 : List Nat := [2, 4, 2, 3, 1, 1, 3, 4]
def baseStart_235668 : Nat := 118140960795 + 235668 * 2 ^ 59
def prefixEnd_235668 : Nat := 4983230072969 + 3 ^ 40 * 235668 * 2
def baseEnd_235668 : Nat := 35855098928559757501093

theorem tailTrace_235668 : CollatzResearch.WordTrace tailWord_235668 prefixEnd_235668 35855098928559757501093 := by
  unfold tailWord_235668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297759055111279867565829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5730345406815039823421105 4297759055111279867565829)
  ·
    refine ⟨805829822833364975168593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4297759055111279867565829 805829822833364975168593)
    ·
      refine ⟨604372367125023731376445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 805829822833364975168593 604372367125023731376445)
      ·
        refine ⟨226639637671883899266167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 604372367125023731376445 226639637671883899266167)
        ·
          refine ⟨339959456507825848899251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226639637671883899266167 339959456507825848899251)
          ·
            refine ⟨509939184761738773348877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339959456507825848899251 509939184761738773348877)
            ·
              refine ⟨191227194285652040005829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509939184761738773348877 191227194285652040005829)
              ·
                refine ⟨35855098928559757501093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191227194285652040005829 35855098928559757501093)
                ·
                  rfl

theorem cell20_235668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_235668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235668 prefixEnd_235668 := by exact prefixLift 235668
  have htrace : WordTrace (prefixWord ++ tailWord_235668) baseStart_235668 baseEnd_235668 := by
    simpa [prefixWord, tailWord_235668, baseEnd_235668] using wordTrace_append hprefix tailTrace_235668
  have hstable : (prefixWord ++ tailWord_235668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235668).length < 2 ^ (prefixWord ++ tailWord_235668).sum := by decide
  have hdescent : baseEnd_235668 < baseStart_235668 := by decide
  rcases family_descends (prefixWord ++ tailWord_235668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235682 : List Nat := [3, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_235682 : Nat := 118140960795 + 235682 * 2 ^ 59
def prefixEnd_235682 : Nat := 4983230072969 + 3 ^ 40 * 235682 * 2
def baseEnd_235682 : Nat := 107571686767157446036555

theorem tailTrace_235682 : CollatzResearch.WordTrace tailWord_235682 prefixEnd_235682 107571686767157446036555 := by
  unfold tailWord_235682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149007183042960031535325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5730685821447893417427533 2149007183042960031535325)
  ·
    refine ⟨805877693641110011825747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2149007183042960031535325 805877693641110011825747)
    ·
      refine ⟨1208816540461665017738621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805877693641110011825747 1208816540461665017738621)
      ·
        refine ⟨453306202673124381651983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1208816540461665017738621 453306202673124381651983)
        ·
          refine ⟨679959304009686572477975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453306202673124381651983 679959304009686572477975)
          ·
            refine ⟨1019938956014529858716963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679959304009686572477975 1019938956014529858716963)
            ·
              refine ⟨1529908434021794788075445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019938956014529858716963 1529908434021794788075445)
              ·
                refine ⟨143428915689543261382073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1529908434021794788075445 143428915689543261382073)
                ·
                  refine ⟨107571686767157446036555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143428915689543261382073 107571686767157446036555)
                  ·
                    rfl

theorem cell20_235682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_235682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235682 prefixEnd_235682 := by exact prefixLift 235682
  have htrace : WordTrace (prefixWord ++ tailWord_235682) baseStart_235682 baseEnd_235682 := by
    simpa [prefixWord, tailWord_235682, baseEnd_235682] using wordTrace_append hprefix tailTrace_235682
  have hstable : (prefixWord ++ tailWord_235682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235682).length < 2 ^ (prefixWord ++ tailWord_235682).sum := by decide
  have hdescent : baseEnd_235682 < baseStart_235682 := by decide
  rcases family_descends (prefixWord ++ tailWord_235682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235703 : List Nat := [1, 1, 3, 1, 4, 2, 2, 4, 2]
def baseStart_235703 : Nat := 118140960795 + 235703 * 2 ^ 59
def prefixEnd_235703 : Nat := 4983230072969 + 3 ^ 40 * 235703 * 2
def baseEnd_235703 : Nat := 107581271739374706336469

theorem tailTrace_235703 : CollatzResearch.WordTrace tailWord_235703 prefixEnd_235703 107581271739374706336469 := by
  unfold tailWord_235703
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596794665095760712655763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5731196443397173808437175 8596794665095760712655763)
  ·
    refine ⟨12895191997643641068983645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8596794665095760712655763 12895191997643641068983645)
    ·
      refine ⟨4835696999116365400868867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12895191997643641068983645 4835696999116365400868867)
      ·
        refine ⟨7253545498674548101303301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4835696999116365400868867 7253545498674548101303301)
        ·
          refine ⟨1360039781001477768994369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7253545498674548101303301 1360039781001477768994369)
          ·
            refine ⟨1020029835751108326745777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360039781001477768994369 1020029835751108326745777)
            ·
              refine ⟨765022376813331245059333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020029835751108326745777 765022376813331245059333)
              ·
                refine ⟨143441695652499608448625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765022376813331245059333 143441695652499608448625)
                ·
                  refine ⟨107581271739374706336469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143441695652499608448625 107581271739374706336469)
                  ·
                    rfl

theorem cell20_235703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 2].length) (baseStart_235703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235703 prefixEnd_235703 := by exact prefixLift 235703
  have htrace : WordTrace (prefixWord ++ tailWord_235703) baseStart_235703 baseEnd_235703 := by
    simpa [prefixWord, tailWord_235703, baseEnd_235703] using wordTrace_append hprefix tailTrace_235703
  have hstable : (prefixWord ++ tailWord_235703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235703).length < 2 ^ (prefixWord ++ tailWord_235703).sum := by decide
  have hdescent : baseEnd_235703 < baseStart_235703 := by decide
  rcases family_descends (prefixWord ++ tailWord_235703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235734 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_235734 : Nat := 118140960795 + 235734 * 2 ^ 59
def prefixEnd_235734 : Nat := 4983230072969 + 3 ^ 40 * 235734 * 2
def baseEnd_235734 : Nat := 107595420984076376303009

theorem tailTrace_235734 : CollatzResearch.WordTrace tailWord_235734 prefixEnd_235734 107595420984076376303009 := by
  unfold tailWord_235734
  simp only [CollatzResearch.WordTrace]
  refine ⟨537370332998965812939641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5731950218655635338022837 537370332998965812939641)
  ·
    refine ⟨403027749749224359704731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 537370332998965812939641 403027749749224359704731)
    ·
      refine ⟨604541624623836539557097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403027749749224359704731 604541624623836539557097)
      ·
        refine ⟨453406218467877404667823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604541624623836539557097 453406218467877404667823)
        ·
          refine ⟨680109327701816107001735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453406218467877404667823 680109327701816107001735)
          ·
            refine ⟨1020163991552724160502603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680109327701816107001735 1020163991552724160502603)
            ·
              refine ⟨1530245987329086240753905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020163991552724160502603 1530245987329086240753905)
              ·
                refine ⟨1147684490496814680565429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530245987329086240753905 1147684490496814680565429)
                ·
                  refine ⟨107595420984076376303009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1147684490496814680565429 107595420984076376303009)
                  ·
                    rfl

theorem cell20_235734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_235734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235734 prefixEnd_235734 := by exact prefixLift 235734
  have htrace : WordTrace (prefixWord ++ tailWord_235734) baseStart_235734 baseEnd_235734 := by
    simpa [prefixWord, tailWord_235734, baseEnd_235734] using wordTrace_append hprefix tailTrace_235734
  have hstable : (prefixWord ++ tailWord_235734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235734).length < 2 ^ (prefixWord ++ tailWord_235734).sum := by decide
  have hdescent : baseEnd_235734 < baseStart_235734 := by decide
  rcases family_descends (prefixWord ++ tailWord_235734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235738 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_235738 : Nat := 118140960795 + 235738 * 2 ^ 59
def prefixEnd_235738 : Nat := 4983230072969 + 3 ^ 40 * 235738 * 2
def baseEnd_235738 : Nat := 107597246693070140169659

theorem tailTrace_235738 : CollatzResearch.WordTrace tailWord_235738 prefixEnd_235738 107597246693070140169659 := by
  unfold tailWord_235738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149517804992240422544967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5732047479979307793453245 2149517804992240422544967)
  ·
    refine ⟨3224276707488360633817451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149517804992240422544967 3224276707488360633817451)
    ·
      refine ⟨4836415061232540950726177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224276707488360633817451 4836415061232540950726177)
      ·
        refine ⟨3627311295924405713044633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4836415061232540950726177 3627311295924405713044633)
        ·
          refine ⟨2720483471943304284783475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3627311295924405713044633 2720483471943304284783475)
          ·
            refine ⟨4080725207914956427175213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720483471943304284783475 4080725207914956427175213)
            ·
              refine ⟨1530271952968108660190705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4080725207914956427175213 1530271952968108660190705)
              ·
                refine ⟨1147703964726081495143029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530271952968108660190705 1147703964726081495143029)
                ·
                  refine ⟨107597246693070140169659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1147703964726081495143029 107597246693070140169659)
                  ·
                    rfl

theorem cell20_235738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_235738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235738 prefixEnd_235738 := by exact prefixLift 235738
  have htrace : WordTrace (prefixWord ++ tailWord_235738) baseStart_235738 baseEnd_235738 := by
    simpa [prefixWord, tailWord_235738, baseEnd_235738] using wordTrace_append hprefix tailTrace_235738
  have hstable : (prefixWord ++ tailWord_235738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235738).length < 2 ^ (prefixWord ++ tailWord_235738).sum := by decide
  have hdescent : baseEnd_235738 < baseStart_235738 := by decide
  rcases family_descends (prefixWord ++ tailWord_235738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235772 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_235772 : Nat := 118140960795 + 235772 * 2 ^ 59
def prefixEnd_235772 : Nat := 4983230072969 + 3 ^ 40 * 235772 * 2
def baseEnd_235772 : Nat := 107612765219517133036187

theorem tailTrace_235772 : CollatzResearch.WordTrace tailWord_235772 prefixEnd_235772 107612765219517133036187 := by
  unfold tailWord_235772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299655650922892748458785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5732874201230523664611713 4299655650922892748458785)
  ·
    refine ⟨3224741738192169561344089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4299655650922892748458785 3224741738192169561344089)
    ·
      refine ⟨2418556303644127171008067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3224741738192169561344089 2418556303644127171008067)
      ·
        refine ⟨3627834455466190756512101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418556303644127171008067 3627834455466190756512101)
        ·
          refine ⟨680218960399910766846019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3627834455466190756512101 680218960399910766846019)
          ·
            refine ⟨1020328440599866150269029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680218960399910766846019 1020328440599866150269029)
            ·
              refine ⟨191311582612474903175443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1020328440599866150269029 191311582612474903175443)
              ·
                refine ⟨286967373918712354763165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191311582612474903175443 286967373918712354763165)
                ·
                  refine ⟨107612765219517133036187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286967373918712354763165 107612765219517133036187)
                  ·
                    rfl

theorem cell20_235772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_235772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235772 prefixEnd_235772 := by exact prefixLift 235772
  have htrace : WordTrace (prefixWord ++ tailWord_235772) baseStart_235772 baseEnd_235772 := by
    simpa [prefixWord, tailWord_235772, baseEnd_235772] using wordTrace_append hprefix tailTrace_235772
  have hstable : (prefixWord ++ tailWord_235772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235772).length < 2 ^ (prefixWord ++ tailWord_235772).sum := by decide
  have hdescent : baseEnd_235772 < baseStart_235772 := by decide
  rcases family_descends (prefixWord ++ tailWord_235772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235810 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_235810 : Nat := 118140960795 + 235810 * 2 ^ 59
def prefixEnd_235810 : Nat := 4983230072969 + 3 ^ 40 * 235810 * 2
def baseEnd_235810 : Nat := 107630109454957889769365

theorem tailTrace_235810 : CollatzResearch.WordTrace tailWord_235810 prefixEnd_235810 107630109454957889769365 := by
  unfold tailWord_235810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150174318927029496700221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5733798183805411991200589 2150174318927029496700221)
  ·
    refine ⟨806315369597636061262583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2150174318927029496700221 806315369597636061262583)
    ·
      refine ⟨1209473054396454091893875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806315369597636061262583 1209473054396454091893875)
      ·
        refine ⟨1814209581594681137840813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209473054396454091893875 1814209581594681137840813)
        ·
          refine ⟨680328593098005426690305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1814209581594681137840813 680328593098005426690305)
          ·
            refine ⟨510246444823504070017729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680328593098005426690305 510246444823504070017729)
            ·
              refine ⟨382684833617628052513297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510246444823504070017729 382684833617628052513297)
              ·
                refine ⟨287013625213221039384973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382684833617628052513297 287013625213221039384973)
                ·
                  refine ⟨107630109454957889769365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287013625213221039384973 107630109454957889769365)
                  ·
                    rfl

theorem cell20_235810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_235810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235810 prefixEnd_235810 := by exact prefixLift 235810
  have htrace : WordTrace (prefixWord ++ tailWord_235810) baseStart_235810 baseEnd_235810 := by
    simpa [prefixWord, tailWord_235810, baseEnd_235810] using wordTrace_append hprefix tailTrace_235810
  have hstable : (prefixWord ++ tailWord_235810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235810).length < 2 ^ (prefixWord ++ tailWord_235810).sum := by decide
  have hdescent : baseEnd_235810 < baseStart_235810 := by decide
  rcases family_descends (prefixWord ++ tailWord_235810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235813 : List Nat := [1, 3, 1, 2, 5, 2, 2, 2, 2]
def baseStart_235813 : Nat := 118140960795 + 235813 * 2 ^ 59
def prefixEnd_235813 : Nat := 4983230072969 + 3 ^ 40 * 235813 * 2
def baseEnd_235813 : Nat := 107631478736703212669353

theorem tailTrace_235813 : CollatzResearch.WordTrace tailWord_235813 prefixEnd_235813 107631478736703212669353 := by
  unfold tailWord_235813
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600806694697249499160093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5733871129798166332773395 8600806694697249499160093)
  ·
    refine ⟨3225302510511468562185035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8600806694697249499160093 3225302510511468562185035)
    ·
      refine ⟨4837953765767202843277553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3225302510511468562185035 4837953765767202843277553)
      ·
        refine ⟨3628465324325402132458165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4837953765767202843277553 3628465324325402132458165)
        ·
          refine ⟨340168624155506449917953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3628465324325402132458165 340168624155506449917953)
          ·
            refine ⟨255126468116629837438465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340168624155506449917953 255126468116629837438465)
            ·
              refine ⟨191344851087472378078849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255126468116629837438465 191344851087472378078849)
              ·
                refine ⟨143508638315604283559137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191344851087472378078849 143508638315604283559137)
                ·
                  refine ⟨107631478736703212669353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143508638315604283559137 107631478736703212669353)
                  ·
                    rfl

theorem cell20_235813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_235813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235813 prefixEnd_235813 := by exact prefixLift 235813
  have htrace : WordTrace (prefixWord ++ tailWord_235813) baseStart_235813 baseEnd_235813 := by
    simpa [prefixWord, tailWord_235813, baseEnd_235813] using wordTrace_append hprefix tailTrace_235813
  have hstable : (prefixWord ++ tailWord_235813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235813).length < 2 ^ (prefixWord ++ tailWord_235813).sum := by decide
  have hdescent : baseEnd_235813 < baseStart_235813 := by decide
  rcases family_descends (prefixWord ++ tailWord_235813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235838 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_235838 : Nat := 118140960795 + 235838 * 2 ^ 59
def prefixEnd_235838 : Nat := 4983230072969 + 3 ^ 40 * 235838 * 2
def baseEnd_235838 : Nat := 107642889417914236835917

theorem tailTrace_235838 : CollatzResearch.WordTrace tailWord_235838 prefixEnd_235838 107642889417914236835917 := by
  unfold tailWord_235838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1075214814950834846102521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5734479013071119179213445 1075214814950834846102521)
  ·
    refine ⟨806411111213126134576891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1075214814950834846102521 806411111213126134576891)
    ·
      refine ⟨1209616666819689201865337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806411111213126134576891 1209616666819689201865337)
      ·
        refine ⟨907212500114766901399003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1209616666819689201865337 907212500114766901399003)
        ·
          refine ⟨1360818750172150352098505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907212500114766901399003 1360818750172150352098505)
          ·
            refine ⟨1020614062629112764073879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360818750172150352098505 1020614062629112764073879)
            ·
              refine ⟨1530921093943669146110819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020614062629112764073879 1530921093943669146110819)
              ·
                refine ⟨2296381640915503719166229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530921093943669146110819 2296381640915503719166229)
                ·
                  refine ⟨107642889417914236835917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2296381640915503719166229 107642889417914236835917)
                  ·
                    rfl

theorem cell20_235838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_235838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235838 prefixEnd_235838 := by exact prefixLift 235838
  have htrace : WordTrace (prefixWord ++ tailWord_235838) baseStart_235838 baseEnd_235838 := by
    simpa [prefixWord, tailWord_235838, baseEnd_235838] using wordTrace_append hprefix tailTrace_235838
  have hstable : (prefixWord ++ tailWord_235838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235838).length < 2 ^ (prefixWord ++ tailWord_235838).sum := by decide
  have hdescent : baseEnd_235838 < baseStart_235838 := by decide
  rcases family_descends (prefixWord ++ tailWord_235838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235841 : List Nat := [1, 2, 5, 2, 2, 1, 3, 4]
def baseStart_235841 : Nat := 118140960795 + 235841 * 2 ^ 59
def prefixEnd_235841 : Nat := 4983230072969 + 3 ^ 40 * 235841 * 2
def baseEnd_235841 : Nat := 35881419566553186578635

theorem tailTrace_235841 : CollatzResearch.WordTrace tailWord_235841 prefixEnd_235841 35881419566553186578635 := by
  unfold tailWord_235841
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601827938595810281179377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5734551959063873520786251 8601827938595810281179377)
  ·
    refine ⟨6451370953946857710884533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8601827938595810281179377 6451370953946857710884533)
    ·
      refine ⟨604816026932517910395425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6451370953946857710884533 604816026932517910395425)
      ·
        refine ⟨453612020199388432796569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604816026932517910395425 453612020199388432796569)
        ·
          refine ⟨340209015149541324597427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453612020199388432796569 340209015149541324597427)
          ·
            refine ⟨510313522724311986896141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340209015149541324597427 510313522724311986896141)
            ·
              refine ⟨191367571021616995086053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510313522724311986896141 191367571021616995086053)
              ·
                refine ⟨35881419566553186578635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191367571021616995086053 35881419566553186578635)
                ·
                  rfl

theorem cell20_235841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 4].length) (baseStart_235841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235841 prefixEnd_235841 := by exact prefixLift 235841
  have htrace : WordTrace (prefixWord ++ tailWord_235841) baseStart_235841 baseEnd_235841 := by
    simpa [prefixWord, tailWord_235841, baseEnd_235841] using wordTrace_append hprefix tailTrace_235841
  have hstable : (prefixWord ++ tailWord_235841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235841).length < 2 ^ (prefixWord ++ tailWord_235841).sum := by decide
  have hdescent : baseEnd_235841 < baseStart_235841 := by decide
  rcases family_descends (prefixWord ++ tailWord_235841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235852 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_235852 : Nat := 118140960795 + 235852 * 2 ^ 59
def prefixEnd_235852 : Nat := 4983230072969 + 3 ^ 40 * 235852 * 2
def baseEnd_235852 : Nat := 107649279399392410369193

theorem tailTrace_235852 : CollatzResearch.WordTrace tailWord_235852 prefixEnd_235852 107649279399392410369193 := by
  unfold tailWord_235852
  simp only [CollatzResearch.WordTrace]
  refine ⟨4301114570777979579914905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5734819427703972773219873 4301114570777979579914905)
  ·
    refine ⟨3225835928083484684936179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4301114570777979579914905 3225835928083484684936179)
    ·
      refine ⟨4838753892125227027404269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3225835928083484684936179 4838753892125227027404269)
      ·
        refine ⟨1814532709546960135276601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4838753892125227027404269 1814532709546960135276601)
        ·
          refine ⟨1360899532160220101457451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1814532709546960135276601 1360899532160220101457451)
          ·
            refine ⟨2041349298240330152186177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360899532160220101457451 2041349298240330152186177)
            ·
              refine ⟨1531011973680247614139633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041349298240330152186177 1531011973680247614139633)
              ·
                refine ⟨1148258980260185710604725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531011973680247614139633 1148258980260185710604725)
                ·
                  refine ⟨107649279399392410369193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1148258980260185710604725 107649279399392410369193)
                  ·
                    rfl

theorem cell20_235852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_235852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235852 prefixEnd_235852 := by exact prefixLift 235852
  have htrace : WordTrace (prefixWord ++ tailWord_235852) baseStart_235852 baseEnd_235852 := by
    simpa [prefixWord, tailWord_235852, baseEnd_235852] using wordTrace_append hprefix tailTrace_235852
  have hstable : (prefixWord ++ tailWord_235852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235852).length < 2 ^ (prefixWord ++ tailWord_235852).sum := by decide
  have hdescent : baseEnd_235852 < baseStart_235852 := by decide
  rcases family_descends (prefixWord ++ tailWord_235852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235876 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_235876 : Nat := 118140960795 + 235876 * 2 ^ 59
def prefixEnd_235876 : Nat := 4983230072969 + 3 ^ 40 * 235876 * 2
def baseEnd_235876 : Nat := 107660233653354993569095

theorem tailTrace_235876 : CollatzResearch.WordTrace tailWord_235876 prefixEnd_235876 107660233653354993569095 := by
  unfold tailWord_235876
  simp only [CollatzResearch.WordTrace]
  refine ⟨4301552246734505629351741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5735402995646007505802321 4301552246734505629351741)
  ·
    refine ⟨1613082092525439611006903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4301552246734505629351741 1613082092525439611006903)
    ·
      refine ⟨2419623138788159416510355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1613082092525439611006903 2419623138788159416510355)
      ·
        refine ⟨3629434708182239124765533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419623138788159416510355 3629434708182239124765533)
        ·
          refine ⟨1361038015568339671787075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3629434708182239124765533 1361038015568339671787075)
          ·
            refine ⟨2041557023352509507680613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361038015568339671787075 2041557023352509507680613)
            ·
              refine ⟨382791941878595532690115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2041557023352509507680613 382791941878595532690115)
              ·
                refine ⟨574187912817893299035173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382791941878595532690115 574187912817893299035173)
                ·
                  refine ⟨107660233653354993569095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574187912817893299035173 107660233653354993569095)
                  ·
                    rfl

theorem cell20_235876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_235876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235876 prefixEnd_235876 := by exact prefixLift 235876
  have htrace : WordTrace (prefixWord ++ tailWord_235876) baseStart_235876 baseEnd_235876 := by
    simpa [prefixWord, tailWord_235876, baseEnd_235876] using wordTrace_append hprefix tailTrace_235876
  have hstable : (prefixWord ++ tailWord_235876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235876).length < 2 ^ (prefixWord ++ tailWord_235876).sum := by decide
  have hdescent : baseEnd_235876 < baseStart_235876 := by decide
  rcases family_descends (prefixWord ++ tailWord_235876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235906 : List Nat := [3, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_235906 : Nat := 118140960795 + 235906 * 2 ^ 59
def prefixEnd_235906 : Nat := 4983230072969 + 3 ^ 40 * 235906 * 2
def baseEnd_235906 : Nat := 107673926470808222568973

theorem tailTrace_235906 : CollatzResearch.WordTrace tailWord_235906 prefixEnd_235906 107673926470808222568973 := by
  unfold tailWord_235906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151049670840081595573893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5736132455573550921530381 2151049670840081595573893)
  ·
    refine ⟨403321813282515299170105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2151049670840081595573893 403321813282515299170105)
    ·
      refine ⟨302491359961886474377579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 403321813282515299170105 302491359961886474377579)
      ·
        refine ⟨453737039942829711566369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302491359961886474377579 453737039942829711566369)
        ·
          refine ⟨340302779957122283674777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453737039942829711566369 340302779957122283674777)
          ·
            refine ⟨255227084967841712756083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340302779957122283674777 255227084967841712756083)
            ·
              refine ⟨382840627451762569134125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255227084967841712756083 382840627451762569134125)
              ·
                refine ⟨143565235294410963425297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382840627451762569134125 143565235294410963425297)
                ·
                  refine ⟨107673926470808222568973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143565235294410963425297 107673926470808222568973)
                  ·
                    rfl

theorem cell20_235906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_235906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235906 prefixEnd_235906 := by exact prefixLift 235906
  have htrace : WordTrace (prefixWord ++ tailWord_235906) baseStart_235906 baseEnd_235906 := by
    simpa [prefixWord, tailWord_235906, baseEnd_235906] using wordTrace_append hprefix tailTrace_235906
  have hstable : (prefixWord ++ tailWord_235906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235906).length < 2 ^ (prefixWord ++ tailWord_235906).sum := by decide
  have hdescent : baseEnd_235906 < baseStart_235906 := by decide
  rcases family_descends (prefixWord ++ tailWord_235906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235966 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_235966 : Nat := 118140960795 + 235966 * 2 ^ 59
def prefixEnd_235966 : Nat := 4983230072969 + 3 ^ 40 * 235966 * 2
def baseEnd_235966 : Nat := 107701312105714680568727

theorem tailTrace_235966 : CollatzResearch.WordTrace tailWord_235966 prefixEnd_235966 107701312105714680568727 := by
  unfold tailWord_235966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1075798382892869578684969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5737591375428637752986501 1075798382892869578684969)
  ·
    refine ⟨806848787169652184013727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1075798382892869578684969 806848787169652184013727)
    ·
      refine ⟨1210273180754478276020591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806848787169652184013727 1210273180754478276020591)
      ·
        refine ⟨1815409771131717414030887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210273180754478276020591 1815409771131717414030887)
        ·
          refine ⟨2723114656697576121046331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815409771131717414030887 2723114656697576121046331)
          ·
            refine ⟨4084671985046364181569497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723114656697576121046331 4084671985046364181569497)
            ·
              refine ⟨3063503988784773136177123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4084671985046364181569497 3063503988784773136177123)
              ·
                refine ⟨4595255983177159704265685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063503988784773136177123 4595255983177159704265685)
                ·
                  refine ⟨107701312105714680568727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4595255983177159704265685 107701312105714680568727)
                  ·
                    rfl

theorem cell20_235966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_235966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235966 prefixEnd_235966 := by exact prefixLift 235966
  have htrace : WordTrace (prefixWord ++ tailWord_235966) baseStart_235966 baseEnd_235966 := by
    simpa [prefixWord, tailWord_235966, baseEnd_235966] using wordTrace_append hprefix tailTrace_235966
  have hstable : (prefixWord ++ tailWord_235966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235966).length < 2 ^ (prefixWord ++ tailWord_235966).sum := by decide
  have hdescent : baseEnd_235966 < baseStart_235966 := by decide
  rcases family_descends (prefixWord ++ tailWord_235966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235980 : List Nat := [2, 2, 1, 4, 11]
def baseStart_235980 : Nat := 118140960795 + 235980 * 2 ^ 59
def prefixEnd_235980 : Nat := 4983230072969 + 3 ^ 40 * 235980 * 2
def baseEnd_235980 : Nat := 1329724717125837704963

theorem tailTrace_235980 : CollatzResearch.WordTrace tailWord_235980 prefixEnd_235980 1329724717125837704963 := by
  unfold tailWord_235980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303448842546118510244697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5737931790061491346992929 4303448842546118510244697)
  ·
    refine ⟨3227586631909588882683523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4303448842546118510244697 3227586631909588882683523)
    ·
      refine ⟨4841379947864383324025285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3227586631909588882683523 4841379947864383324025285)
      ·
        refine ⟨907758740224571873254741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4841379947864383324025285 907758740224571873254741)
        ·
          refine ⟨1329724717125837704963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 907758740224571873254741 1329724717125837704963)
          ·
            rfl

theorem cell20_235980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 11].length) (baseStart_235980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235980 prefixEnd_235980 := by exact prefixLift 235980
  have htrace : WordTrace (prefixWord ++ tailWord_235980) baseStart_235980 baseEnd_235980 := by
    simpa [prefixWord, tailWord_235980, baseEnd_235980] using wordTrace_append hprefix tailTrace_235980
  have hstable : (prefixWord ++ tailWord_235980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235980).length < 2 ^ (prefixWord ++ tailWord_235980).sum := by decide
  have hdescent : baseEnd_235980 < baseStart_235980 := by decide
  rcases family_descends (prefixWord ++ tailWord_235980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235987 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_235987 : Nat := 118140960795 + 235987 * 2 ^ 59
def prefixEnd_235987 : Nat := 4983230072969 + 3 ^ 40 * 235987 * 2
def baseEnd_235987 : Nat := 107710897077931940868641

theorem tailTrace_235987 : CollatzResearch.WordTrace tailWord_235987 prefixEnd_235987 107710897077931940868641 := by
  unfold tailWord_235987
  simp only [CollatzResearch.WordTrace]
  refine ⟨8607152996066877215994215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5738101997377918143996143 8607152996066877215994215)
  ·
    refine ⟨12910729494100315823991323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8607152996066877215994215 12910729494100315823991323)
    ·
      refine ⟨19366094241150473735986985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12910729494100315823991323 19366094241150473735986985)
      ·
        refine ⟨14524570680862855301990239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19366094241150473735986985 14524570680862855301990239)
        ·
          refine ⟨21786856021294282952985359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524570680862855301990239 21786856021294282952985359)
          ·
            refine ⟨32680284031941424429478039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21786856021294282952985359 32680284031941424429478039)
            ·
              refine ⟨49020426047912136644217059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32680284031941424429478039 49020426047912136644217059)
              ·
                refine ⟨73530639071868204966325589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49020426047912136644217059 73530639071868204966325589)
                ·
                  refine ⟨107710897077931940868641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 73530639071868204966325589 107710897077931940868641)
                  ·
                    rfl

theorem cell20_235987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_235987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_235987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_235987 prefixEnd_235987 := by exact prefixLift 235987
  have htrace : WordTrace (prefixWord ++ tailWord_235987) baseStart_235987 baseEnd_235987 := by
    simpa [prefixWord, tailWord_235987, baseEnd_235987] using wordTrace_append hprefix tailTrace_235987
  have hstable : (prefixWord ++ tailWord_235987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235987).length < 2 ^ (prefixWord ++ tailWord_235987).sum := by decide
  have hdescent : baseEnd_235987 < baseStart_235987 := by decide
  rcases family_descends (prefixWord ++ tailWord_235987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236011 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_236011 : Nat := 118140960795 + 236011 * 2 ^ 59
def prefixEnd_236011 : Nat := 4983230072969 + 3 ^ 40 * 236011 * 2
def baseEnd_236011 : Nat := 107721851331894524068543

theorem tailTrace_236011 : CollatzResearch.WordTrace tailWord_236011 prefixEnd_236011 107721851331894524068543 := by
  unfold tailWord_236011
  simp only [CollatzResearch.WordTrace]
  refine ⟨8608028347979929314867887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5738685565319952876578591 8608028347979929314867887)
  ·
    refine ⟨12912042521969893972301831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8608028347979929314867887 12912042521969893972301831)
    ·
      refine ⟨19368063782954840958452747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12912042521969893972301831 19368063782954840958452747)
      ·
        refine ⟨29052095674432261437679121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19368063782954840958452747 29052095674432261437679121)
        ·
          refine ⟨21789071755824196078259341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29052095674432261437679121 21789071755824196078259341)
          ·
            refine ⟨8170901908434073529347253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21789071755824196078259341 8170901908434073529347253)
            ·
              refine ⟨766022053915694393376305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8170901908434073529347253 766022053915694393376305)
              ·
                refine ⟨574516540436770795032229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766022053915694393376305 574516540436770795032229)
                ·
                  refine ⟨107721851331894524068543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574516540436770795032229 107721851331894524068543)
                  ·
                    rfl

theorem cell20_236011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_236011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236011 prefixEnd_236011 := by exact prefixLift 236011
  have htrace : WordTrace (prefixWord ++ tailWord_236011) baseStart_236011 baseEnd_236011 := by
    simpa [prefixWord, tailWord_236011, baseEnd_236011] using wordTrace_append hprefix tailTrace_236011
  have hstable : (prefixWord ++ tailWord_236011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236011).length < 2 ^ (prefixWord ++ tailWord_236011).sum := by decide
  have hdescent : baseEnd_236011 < baseStart_236011 := by decide
  rcases family_descends (prefixWord ++ tailWord_236011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236014 : List Nat := [4, 1, 2, 1, 2, 3, 3, 4]
def baseStart_236014 : Nat := 118140960795 + 236014 * 2 ^ 59
def prefixEnd_236014 : Nat := 4983230072969 + 3 ^ 40 * 236014 * 2
def baseEnd_236014 : Nat := 35907740204546615656177

theorem tailTrace_236014 : CollatzResearch.WordTrace tailWord_236014 prefixEnd_236014 35907740204546615656177 := by
  unfold tailWord_236014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076017220871132603403387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5738758511312707218151397 1076017220871132603403387)
  ·
    refine ⟨1614025831306698905105081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076017220871132603403387 1614025831306698905105081)
    ·
      refine ⟨1210519373480024178828811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1614025831306698905105081 1210519373480024178828811)
      ·
        refine ⟨1815779060220036268243217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210519373480024178828811 1815779060220036268243217)
        ·
          refine ⟨1361834295165027201182413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1815779060220036268243217 1361834295165027201182413)
          ·
            refine ⟨510687860686885200443405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1361834295165027201182413 510687860686885200443405)
            ·
              refine ⟨191507947757581950166277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510687860686885200443405 191507947757581950166277)
              ·
                refine ⟨35907740204546615656177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191507947757581950166277 35907740204546615656177)
                ·
                  rfl

theorem cell20_236014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_236014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236014 prefixEnd_236014 := by exact prefixLift 236014
  have htrace : WordTrace (prefixWord ++ tailWord_236014) baseStart_236014 baseEnd_236014 := by
    simpa [prefixWord, tailWord_236014, baseEnd_236014] using wordTrace_append hprefix tailTrace_236014
  have hstable : (prefixWord ++ tailWord_236014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236014).length < 2 ^ (prefixWord ++ tailWord_236014).sum := by decide
  have hdescent : baseEnd_236014 < baseStart_236014 := by decide
  rcases family_descends (prefixWord ++ tailWord_236014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236034 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_236034 : Nat := 118140960795 + 236034 * 2 ^ 59
def prefixEnd_236034 : Nat := 4983230072969 + 3 ^ 40 * 236034 * 2
def baseEnd_236034 : Nat := 107732349158608666301783

theorem tailTrace_236034 : CollatzResearch.WordTrace tailWord_236034 prefixEnd_236034 107732349158608666301783 := by
  unfold tailWord_236034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152216806724151060738789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5739244817931069495303437 2152216806724151060738789)
  ·
    refine ⟨403540651260778323888523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2152216806724151060738789 403540651260778323888523)
    ·
      refine ⟨605310976891167485832785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403540651260778323888523 605310976891167485832785)
      ·
        refine ⟨453983232668375614374589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605310976891167485832785 453983232668375614374589)
        ·
          refine ⟨170243712250640855390471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453983232668375614374589 170243712250640855390471)
          ·
            refine ⟨255365568375961283085707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170243712250640855390471 255365568375961283085707)
            ·
              refine ⟨383048352563941924628561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255365568375961283085707 383048352563941924628561)
              ·
                refine ⟨287286264422956443471421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383048352563941924628561 287286264422956443471421)
                ·
                  refine ⟨107732349158608666301783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287286264422956443471421 107732349158608666301783)
                  ·
                    rfl

theorem cell20_236034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_236034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236034 prefixEnd_236034 := by exact prefixLift 236034
  have htrace : WordTrace (prefixWord ++ tailWord_236034) baseStart_236034 baseEnd_236034 := by
    simpa [prefixWord, tailWord_236034, baseEnd_236034] using wordTrace_append hprefix tailTrace_236034
  have hstable : (prefixWord ++ tailWord_236034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236034).length < 2 ^ (prefixWord ++ tailWord_236034).sum := by decide
  have hdescent : baseEnd_236034 < baseStart_236034 := by decide
  rcases family_descends (prefixWord ++ tailWord_236034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236042 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_236042 : Nat := 118140960795 + 236042 * 2 ^ 59
def prefixEnd_236042 : Nat := 4983230072969 + 3 ^ 40 * 236042 * 2
def baseEnd_236042 : Nat := 107736000576596194035083

theorem tailTrace_236042 : CollatzResearch.WordTrace tailWord_236042 prefixEnd_236042 107736000576596194035083 := by
  unfold tailWord_236042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152289752716905402311595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5739439340578414406164253 2152289752716905402311595)
  ·
    refine ⟨3228434629075358103467393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2152289752716905402311595 3228434629075358103467393)
    ·
      refine ⟨2421325971806518577600545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3228434629075358103467393 2421325971806518577600545)
      ·
        refine ⟨1815994478854888933200409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2421325971806518577600545 1815994478854888933200409)
        ·
          refine ⟨1361995859141166699900307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1815994478854888933200409 1361995859141166699900307)
          ·
            refine ⟨2042993788711750049850461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361995859141166699900307 2042993788711750049850461)
            ·
              refine ⟨766122670766906268693923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2042993788711750049850461 766122670766906268693923)
              ·
                refine ⟨1149184006150359403040885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766122670766906268693923 1149184006150359403040885)
                ·
                  refine ⟨107736000576596194035083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1149184006150359403040885 107736000576596194035083)
                  ·
                    rfl

theorem cell20_236042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_236042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236042 prefixEnd_236042 := by exact prefixLift 236042
  have htrace : WordTrace (prefixWord ++ tailWord_236042) baseStart_236042 baseEnd_236042 := by
    simpa [prefixWord, tailWord_236042, baseEnd_236042] using wordTrace_append hprefix tailTrace_236042
  have hstable : (prefixWord ++ tailWord_236042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236042).length < 2 ^ (prefixWord ++ tailWord_236042).sum := by decide
  have hdescent : baseEnd_236042 < baseStart_236042 := by decide
  rcases family_descends (prefixWord ++ tailWord_236042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236055 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 3]
def baseStart_236055 : Nat := 118140960795 + 236055 * 2 ^ 59
def prefixEnd_236055 : Nat := 4983230072969 + 3 ^ 40 * 236055 * 2
def baseEnd_236055 : Nat := 107741934130825926601697

theorem tailTrace_236055 : CollatzResearch.WordTrace tailWord_236055 prefixEnd_236055 107741934130825926601697 := by
  unfold tailWord_236055
  simp only [CollatzResearch.WordTrace]
  refine ⟨8609633159820524829469619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5739755439880349886313079 8609633159820524829469619)
  ·
    refine ⟨12914449739730787244204429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8609633159820524829469619 12914449739730787244204429)
    ·
      refine ⟨4842918652399045216576661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12914449739730787244204429 4842918652399045216576661)
      ·
        refine ⟨227011811831205244527031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4842918652399045216576661 227011811831205244527031)
        ·
          refine ⟨340517717746807866790547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227011811831205244527031 340517717746807866790547)
          ·
            refine ⟨510776576620211800185821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340517717746807866790547 510776576620211800185821)
            ·
              refine ⟨191541216232579425069683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510776576620211800185821 191541216232579425069683)
              ·
                refine ⟨287311824348869137604525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191541216232579425069683 287311824348869137604525)
                ·
                  refine ⟨107741934130825926601697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287311824348869137604525 107741934130825926601697)
                  ·
                    rfl

theorem cell20_236055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 3].length) (baseStart_236055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236055 prefixEnd_236055 := by exact prefixLift 236055
  have htrace : WordTrace (prefixWord ++ tailWord_236055) baseStart_236055 baseEnd_236055 := by
    simpa [prefixWord, tailWord_236055, baseEnd_236055] using wordTrace_append hprefix tailTrace_236055
  have hstable : (prefixWord ++ tailWord_236055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236055).length < 2 ^ (prefixWord ++ tailWord_236055).sum := by decide
  have hdescent : baseEnd_236055 < baseStart_236055 := by decide
  rcases family_descends (prefixWord ++ tailWord_236055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236104 : List Nat := [2, 1, 3, 1, 1, 1, 1, 8, 2]
def baseStart_236104 : Nat := 118140960795 + 236104 * 2 ^ 59
def prefixEnd_236104 : Nat := 4983230072969 + 3 ^ 40 * 236104 * 2
def baseEnd_236104 : Nat := 107764299065999533968163

theorem tailTrace_236104 : CollatzResearch.WordTrace tailWord_236104 prefixEnd_236104 107764299065999533968163 := by
  unfold tailWord_236104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4305710168321503099001683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5740946891095337465335577 4305710168321503099001683)
  ·
    refine ⟨6458565252482254648502525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4305710168321503099001683 6458565252482254648502525)
    ·
      refine ⟨2421961969680845493188447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6458565252482254648502525 2421961969680845493188447)
      ·
        refine ⟨3632942954521268239782671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421961969680845493188447 3632942954521268239782671)
        ·
          refine ⟨5449414431781902359674007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632942954521268239782671 5449414431781902359674007)
          ·
            refine ⟨8174121647672853539511011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449414431781902359674007 8174121647672853539511011)
            ·
              refine ⟨12261182471509280309266517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8174121647672853539511011 12261182471509280309266517)
              ·
                refine ⟨143685732087999378624217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12261182471509280309266517 143685732087999378624217)
                ·
                  refine ⟨107764299065999533968163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143685732087999378624217 107764299065999533968163)
                  ·
                    rfl

theorem cell20_236104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_236104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236104 prefixEnd_236104 := by exact prefixLift 236104
  have htrace : WordTrace (prefixWord ++ tailWord_236104) baseStart_236104 baseEnd_236104 := by
    simpa [prefixWord, tailWord_236104, baseEnd_236104] using wordTrace_append hprefix tailTrace_236104
  have hstable : (prefixWord ++ tailWord_236104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236104).length < 2 ^ (prefixWord ++ tailWord_236104).sum := by decide
  have hdescent : baseEnd_236104 < baseStart_236104 := by decide
  rcases family_descends (prefixWord ++ tailWord_236104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236132 : List Nat := [2, 3, 1, 1, 2, 2, 1, 8]
def baseStart_236132 : Nat := 118140960795 + 236132 * 2 ^ 59
def prefixEnd_236132 : Nat := 4983230072969 + 3 ^ 40 * 236132 * 2
def baseEnd_236132 : Nat := 35925693009651960344905

theorem tailTrace_236132 : CollatzResearch.WordTrace tailWord_236132 prefixEnd_236132 35925693009651960344905 := by
  unfold tailWord_236132
  simp only [CollatzResearch.WordTrace]
  refine ⟨4306220790270783490011325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5741627720361044653348433 4306220790270783490011325)
  ·
    refine ⟨1614832796351543808754247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4306220790270783490011325 1614832796351543808754247)
    ·
      refine ⟨2422249194527315713131371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614832796351543808754247 2422249194527315713131371)
      ·
        refine ⟨3633373791790973569697057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2422249194527315713131371 3633373791790973569697057)
        ·
          refine ⟨2725030343843230177272793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3633373791790973569697057 2725030343843230177272793)
          ·
            refine ⟨2043772757882422632954595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725030343843230177272793 2043772757882422632954595)
            ·
              refine ⟨3065659136823633949431893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043772757882422632954595 3065659136823633949431893)
              ·
                refine ⟨35925693009651960344905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3065659136823633949431893 35925693009651960344905)
                ·
                  rfl

theorem cell20_236132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_236132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236132 prefixEnd_236132 := by exact prefixLift 236132
  have htrace : WordTrace (prefixWord ++ tailWord_236132) baseStart_236132 baseEnd_236132 := by
    simpa [prefixWord, tailWord_236132, baseEnd_236132] using wordTrace_append hprefix tailTrace_236132
  have hstable : (prefixWord ++ tailWord_236132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236132).length < 2 ^ (prefixWord ++ tailWord_236132).sum := by decide
  have hdescent : baseEnd_236132 < baseStart_236132 := by decide
  rcases family_descends (prefixWord ++ tailWord_236132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236139 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_236139 : Nat := 118140960795 + 236139 * 2 ^ 59
def prefixEnd_236139 : Nat := 4983230072969 + 3 ^ 40 * 236139 * 2
def baseEnd_236139 : Nat := 107780274019694967801353

theorem tailTrace_236139 : CollatzResearch.WordTrace tailWord_236139 prefixEnd_236139 107780274019694967801353 := by
  unfold tailWord_236139
  simp only [CollatzResearch.WordTrace]
  refine ⟨8612696891516207175527471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5741797927677471450351647 8612696891516207175527471)
  ·
    refine ⟨12919045337274310763291207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8612696891516207175527471 12919045337274310763291207)
    ·
      refine ⟨19378568005911466144936811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12919045337274310763291207 19378568005911466144936811)
      ·
        refine ⟨29067852008867199217405217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19378568005911466144936811 29067852008867199217405217)
        ·
          refine ⟨21800889006650399413053913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29067852008867199217405217 21800889006650399413053913)
          ·
            refine ⟨16350666754987799559790435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21800889006650399413053913 16350666754987799559790435)
            ·
              refine ⟨24526000132481699339685653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16350666754987799559790435 24526000132481699339685653)
              ·
                refine ⟨1149656256210079656547765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24526000132481699339685653 1149656256210079656547765)
                ·
                  refine ⟨107780274019694967801353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1149656256210079656547765 107780274019694967801353)
                  ·
                    rfl

theorem cell20_236139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_236139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236139 prefixEnd_236139 := by exact prefixLift 236139
  have htrace : WordTrace (prefixWord ++ tailWord_236139) baseStart_236139 baseEnd_236139 := by
    simpa [prefixWord, tailWord_236139, baseEnd_236139] using wordTrace_append hprefix tailTrace_236139
  have hstable : (prefixWord ++ tailWord_236139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236139).length < 2 ^ (prefixWord ++ tailWord_236139).sum := by decide
  have hdescent : baseEnd_236139 < baseStart_236139 := by decide
  rcases family_descends (prefixWord ++ tailWord_236139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236149 : List Nat := [1, 3, 4, 2, 2, 8]
def baseStart_236149 : Nat := 118140960795 + 236149 * 2 ^ 59
def prefixEnd_236149 : Nat := 4983230072969 + 3 ^ 40 * 236149 * 2
def baseEnd_236149 : Nat := 3992031047858495461777

theorem tailTrace_236149 : CollatzResearch.WordTrace tailWord_236149 prefixEnd_236149 3992031047858495461777 := by
  unfold tailWord_236149
  simp only [CollatzResearch.WordTrace]
  refine ⟨8613061621479978883391501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5742041080986652588927667 8613061621479978883391501)
  ·
    refine ⟨3229898108054992081271813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8613061621479978883391501 3229898108054992081271813)
    ·
      refine ⟨605605895260311015238465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3229898108054992081271813 605605895260311015238465)
      ·
        refine ⟨454204421445233261428849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605605895260311015238465 454204421445233261428849)
        ·
          refine ⟨340653316083924946071637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454204421445233261428849 340653316083924946071637)
          ·
            refine ⟨3992031047858495461777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 340653316083924946071637 3992031047858495461777)
            ·
              rfl

theorem cell20_236149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 8].length) (baseStart_236149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236149 prefixEnd_236149 := by exact prefixLift 236149
  have htrace : WordTrace (prefixWord ++ tailWord_236149) baseStart_236149 baseEnd_236149 := by
    simpa [prefixWord, tailWord_236149, baseEnd_236149] using wordTrace_append hprefix tailTrace_236149
  have hstable : (prefixWord ++ tailWord_236149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236149).length < 2 ^ (prefixWord ++ tailWord_236149).sum := by decide
  have hdescent : baseEnd_236149 < baseStart_236149 := by decide
  rcases family_descends (prefixWord ++ tailWord_236149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236156 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_236156 : Nat := 118140960795 + 236156 * 2 ^ 59
def prefixEnd_236156 : Nat := 4983230072969 + 3 ^ 40 * 236156 * 2
def baseEnd_236156 : Nat := 107788033282918464234617

theorem tailTrace_236156 : CollatzResearch.WordTrace tailWord_236156 prefixEnd_236156 107788033282918464234617 := by
  unfold tailWord_236156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4306658466227309539448161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5742211288303079385930881 4306658466227309539448161)
  ·
    refine ⟨3229993849670482154586121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4306658466227309539448161 3229993849670482154586121)
    ·
      refine ⟨2422495387252861615939591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3229993849670482154586121 2422495387252861615939591)
      ·
        refine ⟨3633743080879292423909387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2422495387252861615939591 3633743080879292423909387)
        ·
          refine ⟨5450614621318938635864081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633743080879292423909387 5450614621318938635864081)
          ·
            refine ⟨4087960965989203976898061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5450614621318938635864081 4087960965989203976898061)
            ·
              refine ⟨1532985362245951491336773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4087960965989203976898061 1532985362245951491336773)
              ·
                refine ⟨287434755421115904625645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1532985362245951491336773 287434755421115904625645)
                ·
                  refine ⟨107788033282918464234617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287434755421115904625645 107788033282918464234617)
                  ·
                    rfl

theorem cell20_236156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_236156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236156 prefixEnd_236156 := by exact prefixLift 236156
  have htrace : WordTrace (prefixWord ++ tailWord_236156) baseStart_236156 baseEnd_236156 := by
    simpa [prefixWord, tailWord_236156, baseEnd_236156] using wordTrace_append hprefix tailTrace_236156
  have hstable : (prefixWord ++ tailWord_236156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236156).length < 2 ^ (prefixWord ++ tailWord_236156).sum := by decide
  have hdescent : baseEnd_236156 < baseStart_236156 := by decide
  rcases family_descends (prefixWord ++ tailWord_236156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236180 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_236180 : Nat := 118140960795 + 236180 * 2 ^ 59
def prefixEnd_236180 : Nat := 4983230072969 + 3 ^ 40 * 236180 * 2
def baseEnd_236180 : Nat := 107798987536881047434519

theorem tailTrace_236180 : CollatzResearch.WordTrace tailWord_236180 prefixEnd_236180 107798987536881047434519 := by
  unfold tailWord_236180
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307096142183835588884997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5742794856245114118513329 4307096142183835588884997)
  ·
    refine ⟨807580526659469172915937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4307096142183835588884997 807580526659469172915937)
    ·
      refine ⟨605685394994601879686953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 807580526659469172915937 605685394994601879686953)
      ·
        refine ⟨454264046245951409765215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605685394994601879686953 454264046245951409765215)
        ·
          refine ⟨681396069368927114647823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454264046245951409765215 681396069368927114647823)
          ·
            refine ⟨1022094104053390671971735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681396069368927114647823 1022094104053390671971735)
            ·
              refine ⟨1533141156080086007957603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022094104053390671971735 1533141156080086007957603)
              ·
                refine ⟨2299711734120129011936405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533141156080086007957603 2299711734120129011936405)
                ·
                  refine ⟨107798987536881047434519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2299711734120129011936405 107798987536881047434519)
                  ·
                    rfl

theorem cell20_236180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_236180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236180 prefixEnd_236180 := by exact prefixLift 236180
  have htrace : WordTrace (prefixWord ++ tailWord_236180) baseStart_236180 baseEnd_236180 := by
    simpa [prefixWord, tailWord_236180, baseEnd_236180] using wordTrace_append hprefix tailTrace_236180
  have hstable : (prefixWord ++ tailWord_236180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236180).length < 2 ^ (prefixWord ++ tailWord_236180).sum := by decide
  have hdescent : baseEnd_236180 < baseStart_236180 := by decide
  rcases family_descends (prefixWord ++ tailWord_236180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236211 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 3]
def baseStart_236211 : Nat := 118140960795 + 236211 * 2 ^ 59
def prefixEnd_236211 : Nat := 4983230072969 + 3 ^ 40 * 236211 * 2
def baseEnd_236211 : Nat := 107813136781582717401059

theorem tailTrace_236211 : CollatzResearch.WordTrace tailWord_236211 prefixEnd_236211 107813136781582717401059 := by
  unfold tailWord_236211
  simp only [CollatzResearch.WordTrace]
  refine ⟨8615322947255363472148487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5743548631503575648098991 8615322947255363472148487)
  ·
    refine ⟨12922984420883045208222731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8615322947255363472148487 12922984420883045208222731)
    ·
      refine ⟨19384476631324567812334097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12922984420883045208222731 19384476631324567812334097)
      ·
        refine ⟨14538357473493425859250573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19384476631324567812334097 14538357473493425859250573)
        ·
          refine ⟨5451884052560034697218965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14538357473493425859250573 5451884052560034697218965)
          ·
            refine ⟨255557064963751626432139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5451884052560034697218965 255557064963751626432139)
            ·
              refine ⟨383335597445627439648209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255557064963751626432139 383335597445627439648209)
              ·
                refine ⟨287501698084220579736157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383335597445627439648209 287501698084220579736157)
                ·
                  refine ⟨107813136781582717401059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287501698084220579736157 107813136781582717401059)
                  ·
                    rfl

theorem cell20_236211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 3].length) (baseStart_236211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236211 prefixEnd_236211 := by exact prefixLift 236211
  have htrace : WordTrace (prefixWord ++ tailWord_236211) baseStart_236211 baseEnd_236211 := by
    simpa [prefixWord, tailWord_236211, baseEnd_236211] using wordTrace_append hprefix tailTrace_236211
  have hstable : (prefixWord ++ tailWord_236211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236211).length < 2 ^ (prefixWord ++ tailWord_236211).sum := by decide
  have hdescent : baseEnd_236211 < baseStart_236211 := by decide
  rcases family_descends (prefixWord ++ tailWord_236211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236214 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_236214 : Nat := 118140960795 + 236214 * 2 ^ 59
def prefixEnd_236214 : Nat := 4983230072969 + 3 ^ 40 * 236214 * 2
def baseEnd_236214 : Nat := 107814506063328040301047

theorem tailTrace_236214 : CollatzResearch.WordTrace tailWord_236214 prefixEnd_236214 107814506063328040301047 := by
  unfold tailWord_236214
  simp only [CollatzResearch.WordTrace]
  refine ⟨538464522890280936531731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5743621577496329989671797 538464522890280936531731)
  ·
    refine ⟨807696784335421404797597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 538464522890280936531731 807696784335421404797597)
    ·
      refine ⟨302886294125783026799099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 807696784335421404797597 302886294125783026799099)
      ·
        refine ⟨454329441188674540198649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302886294125783026799099 454329441188674540198649)
        ·
          refine ⟨340747080891505905148987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454329441188674540198649 340747080891505905148987)
          ·
            refine ⟨511120621337258857723481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340747080891505905148987 511120621337258857723481)
            ·
              refine ⟨383340466002944143292611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511120621337258857723481 383340466002944143292611)
              ·
                refine ⟨575010699004416214938917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383340466002944143292611 575010699004416214938917)
                ·
                  refine ⟨107814506063328040301047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575010699004416214938917 107814506063328040301047)
                  ·
                    rfl

theorem cell20_236214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_236214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236214 prefixEnd_236214 := by exact prefixLift 236214
  have htrace : WordTrace (prefixWord ++ tailWord_236214) baseStart_236214 baseEnd_236214 := by
    simpa [prefixWord, tailWord_236214, baseEnd_236214] using wordTrace_append hprefix tailTrace_236214
  have hstable : (prefixWord ++ tailWord_236214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236214).length < 2 ^ (prefixWord ++ tailWord_236214).sum := by decide
  have hdescent : baseEnd_236214 < baseStart_236214 := by decide
  rcases family_descends (prefixWord ++ tailWord_236214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236218 : List Nat := [3, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_236218 : Nat := 118140960795 + 236218 * 2 ^ 59
def prefixEnd_236218 : Nat := 4983230072969 + 3 ^ 40 * 236218 * 2
def baseEnd_236218 : Nat := 107816331772321804167697

theorem tailTrace_236218 : CollatzResearch.WordTrace tailWord_236218 prefixEnd_236218 107816331772321804167697 := by
  unfold tailWord_236218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2153894564557500916913327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5743718838820002445102205 2153894564557500916913327)
  ·
    refine ⟨3230841846836251375369991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2153894564557500916913327 3230841846836251375369991)
    ·
      refine ⟨4846262770254377063054987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230841846836251375369991 4846262770254377063054987)
      ·
        refine ⟨7269394155381565594582481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4846262770254377063054987 7269394155381565594582481)
        ·
          refine ⟨5452045616536174195936861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7269394155381565594582481 5452045616536174195936861)
          ·
            refine ⟨2044517106201065323476323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5452045616536174195936861 2044517106201065323476323)
            ·
              refine ⟨3066775659301597985214485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044517106201065323476323 3066775659301597985214485)
              ·
                refine ⟨143755109029762405556929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3066775659301597985214485 143755109029762405556929)
                ·
                  refine ⟨107816331772321804167697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143755109029762405556929 107816331772321804167697)
                  ·
                    rfl

theorem cell20_236218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_236218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236218 prefixEnd_236218 := by exact prefixLift 236218
  have htrace : WordTrace (prefixWord ++ tailWord_236218) baseStart_236218 baseEnd_236218 := by
    simpa [prefixWord, tailWord_236218, baseEnd_236218] using wordTrace_append hprefix tailTrace_236218
  have hstable : (prefixWord ++ tailWord_236218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236218).length < 2 ^ (prefixWord ++ tailWord_236218).sum := by decide
  have hdescent : baseEnd_236218 < baseStart_236218 := by decide
  rcases family_descends (prefixWord ++ tailWord_236218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236228 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_236228 : Nat := 118140960795 + 236228 * 2 ^ 59
def prefixEnd_236228 : Nat := 4983230072969 + 3 ^ 40 * 236228 * 2
def baseEnd_236228 : Nat := 107820896044806213834323

theorem tailTrace_236228 : CollatzResearch.WordTrace tailWord_236228 prefixEnd_236228 107820896044806213834323 := by
  unfold tailWord_236228
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307971494096887687758669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5743961992129183583678225 4307971494096887687758669)
  ·
    refine ⟨1615489310286332882909501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4307971494096887687758669 1615489310286332882909501)
    ·
      refine ⟨605808491357374831091063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1615489310286332882909501 605808491357374831091063)
      ·
        refine ⟨908712737036062246636595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605808491357374831091063 908712737036062246636595)
        ·
          refine ⟨1363069105554093369954893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908712737036062246636595 1363069105554093369954893)
          ·
            refine ⟨511150914582785013733085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1363069105554093369954893 511150914582785013733085)
            ·
              refine ⟨191681592968544380149907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511150914582785013733085 191681592968544380149907)
              ·
                refine ⟨287522389452816570224861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191681592968544380149907 287522389452816570224861)
                ·
                  refine ⟨107820896044806213834323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287522389452816570224861 107820896044806213834323)
                  ·
                    rfl

theorem cell20_236228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_236228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236228 prefixEnd_236228 := by exact prefixLift 236228
  have htrace : WordTrace (prefixWord ++ tailWord_236228) baseStart_236228 baseEnd_236228 := by
    simpa [prefixWord, tailWord_236228, baseEnd_236228] using wordTrace_append hprefix tailTrace_236228
  have hstable : (prefixWord ++ tailWord_236228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236228).length < 2 ^ (prefixWord ++ tailWord_236228).sum := by decide
  have hdescent : baseEnd_236228 < baseStart_236228 := by decide
  rcases family_descends (prefixWord ++ tailWord_236228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236252 : List Nat := [2, 2, 5, 1, 1, 1, 3, 3, 2]
def baseStart_236252 : Nat := 118140960795 + 236252 * 2 ^ 59
def prefixEnd_236252 : Nat := 4983230072969 + 3 ^ 40 * 236252 * 2
def baseEnd_236252 : Nat := 107831850298768797034225

theorem tailTrace_236252 : CollatzResearch.WordTrace tailWord_236252 prefixEnd_236252 107831850298768797034225 := by
  unfold tailWord_236252
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308409170053413737195505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5744545560071218316260673 4308409170053413737195505)
  ·
    refine ⟨3231306877540060302896629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4308409170053413737195505 3231306877540060302896629)
    ·
      refine ⟨302935019769380653396559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3231306877540060302896629 302935019769380653396559)
      ·
        refine ⟨454402529654070980094839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302935019769380653396559 454402529654070980094839)
        ·
          refine ⟨681603794481106470142259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454402529654070980094839 681603794481106470142259)
          ·
            refine ⟨1022405691721659705213389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681603794481106470142259 1022405691721659705213389)
            ·
              refine ⟨383402134395622389455021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1022405691721659705213389 383402134395622389455021)
              ·
                refine ⟨143775800398358396045633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383402134395622389455021 143775800398358396045633)
                ·
                  refine ⟨107831850298768797034225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143775800398358396045633 107831850298768797034225)
                  ·
                    rfl

theorem cell20_236252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_236252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236252 prefixEnd_236252 := by exact prefixLift 236252
  have htrace : WordTrace (prefixWord ++ tailWord_236252) baseStart_236252 baseEnd_236252 := by
    simpa [prefixWord, tailWord_236252, baseEnd_236252] using wordTrace_append hprefix tailTrace_236252
  have hstable : (prefixWord ++ tailWord_236252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236252).length < 2 ^ (prefixWord ++ tailWord_236252).sum := by decide
  have hdescent : baseEnd_236252 < baseStart_236252 := by decide
  rcases family_descends (prefixWord ++ tailWord_236252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236270 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_236270 : Nat := 118140960795 + 236270 * 2 ^ 59
def prefixEnd_236270 : Nat := 4983230072969 + 3 ^ 40 * 236270 * 2
def baseEnd_236270 : Nat := 107840065989240734434151

theorem tailTrace_236270 : CollatzResearch.WordTrace tailWord_236270 prefixEnd_236270 107840065989240734434151 := by
  unfold tailWord_236270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077184356755202068568283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5744983236027744365697509 1077184356755202068568283)
  ·
    refine ⟨1615776535132803102852425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1077184356755202068568283 1615776535132803102852425)
    ·
      refine ⟨1211832401349602327139319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1615776535132803102852425 1211832401349602327139319)
      ·
        refine ⟨1817748602024403490708979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211832401349602327139319 1817748602024403490708979)
        ·
          refine ⟨2726622903036605236063469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817748602024403490708979 2726622903036605236063469)
          ·
            refine ⟨1022483588638726963523801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2726622903036605236063469 1022483588638726963523801)
            ·
              refine ⟨766862691479045222642851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022483588638726963523801 766862691479045222642851)
              ·
                refine ⟨1150294037218567833964277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766862691479045222642851 1150294037218567833964277)
                ·
                  refine ⟨107840065989240734434151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1150294037218567833964277 107840065989240734434151)
                  ·
                    rfl

theorem cell20_236270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_236270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236270 prefixEnd_236270 := by exact prefixLift 236270
  have htrace : WordTrace (prefixWord ++ tailWord_236270) baseStart_236270 baseEnd_236270 := by
    simpa [prefixWord, tailWord_236270, baseEnd_236270] using wordTrace_append hprefix tailTrace_236270
  have hstable : (prefixWord ++ tailWord_236270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236270).length < 2 ^ (prefixWord ++ tailWord_236270).sum := by decide
  have hdescent : baseEnd_236270 < baseStart_236270 := by decide
  rcases family_descends (prefixWord ++ tailWord_236270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236273 : List Nat := [1, 2, 2, 2, 2, 2, 5, 2, 2]
def baseStart_236273 : Nat := 118140960795 + 236273 * 2 ^ 59
def prefixEnd_236273 : Nat := 4983230072969 + 3 ^ 40 * 236273 * 2
def baseEnd_236273 : Nat := 107841435270986057334139

theorem tailTrace_236273 : CollatzResearch.WordTrace tailWord_236273 prefixEnd_236273 107841435270986057334139 := by
  unfold tailWord_236273
  simp only [CollatzResearch.WordTrace]
  refine ⟨8617584273030748060905473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5745056182020498707270315 8617584273030748060905473)
  ·
    refine ⟨6463188204773061045679105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8617584273030748060905473 6463188204773061045679105)
    ·
      refine ⟨4847391153579795784259329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6463188204773061045679105 4847391153579795784259329)
      ·
        refine ⟨3635543365184846838194497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4847391153579795784259329 3635543365184846838194497)
        ·
          refine ⟨2726657523888635128645873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3635543365184846838194497 2726657523888635128645873)
          ·
            refine ⟨2044993142916476346484405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2726657523888635128645873 2044993142916476346484405)
            ·
              refine ⟨191718107148419657482913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2044993142916476346484405 191718107148419657482913)
              ·
                refine ⟨143788580361314743112185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191718107148419657482913 143788580361314743112185)
                ·
                  refine ⟨107841435270986057334139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143788580361314743112185 107841435270986057334139)
                  ·
                    rfl

theorem cell20_236273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_236273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236273 prefixEnd_236273 := by exact prefixLift 236273
  have htrace : WordTrace (prefixWord ++ tailWord_236273) baseStart_236273 baseEnd_236273 := by
    simpa [prefixWord, tailWord_236273, baseEnd_236273] using wordTrace_append hprefix tailTrace_236273
  have hstable : (prefixWord ++ tailWord_236273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236273).length < 2 ^ (prefixWord ++ tailWord_236273).sum := by decide
  have hdescent : baseEnd_236273 < baseStart_236273 := by decide
  rcases family_descends (prefixWord ++ tailWord_236273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236284 : List Nat := [2, 2, 2, 1, 3, 2, 1, 7]
def baseStart_236284 : Nat := 118140960795 + 236284 * 2 ^ 59
def prefixEnd_236284 : Nat := 4983230072969 + 3 ^ 40 * 236284 * 2
def baseEnd_236284 : Nat := 35948818656906302655809

theorem tailTrace_236284 : CollatzResearch.WordTrace tailWord_236284 prefixEnd_236284 35948818656906302655809 := by
  unfold tailWord_236284
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308992737995448469777953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5745323650660597959703937 4308992737995448469777953)
  ·
    refine ⟨3231744553496586352333465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4308992737995448469777953 3231744553496586352333465)
    ·
      refine ⟨2423808415122439764250099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3231744553496586352333465 2423808415122439764250099)
      ·
        refine ⟨3635712622683659646375149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423808415122439764250099 3635712622683659646375149)
        ·
          refine ⟨1363392233506372367390681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3635712622683659646375149 1363392233506372367390681)
          ·
            refine ⟨1022544175129779275543011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363392233506372367390681 1022544175129779275543011)
            ·
              refine ⟨1533816262694668913314517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022544175129779275543011 1533816262694668913314517)
              ·
                refine ⟨35948818656906302655809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1533816262694668913314517 35948818656906302655809)
                ·
                  rfl

theorem cell20_236284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_236284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236284 prefixEnd_236284 := by exact prefixLift 236284
  have htrace : WordTrace (prefixWord ++ tailWord_236284) baseStart_236284 baseEnd_236284 := by
    simpa [prefixWord, tailWord_236284, baseEnd_236284] using wordTrace_append hprefix tailTrace_236284
  have hstable : (prefixWord ++ tailWord_236284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236284).length < 2 ^ (prefixWord ++ tailWord_236284).sum := by decide
  have hdescent : baseEnd_236284 < baseStart_236284 := by decide
  rcases family_descends (prefixWord ++ tailWord_236284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236322 : List Nat := [3, 3, 1, 1, 2, 10]
def baseStart_236322 : Nat := 118140960795 + 236322 * 2 ^ 59
def prefixEnd_236322 : Nat := 4983230072969 + 3 ^ 40 * 236322 * 2
def baseEnd_236322 : Nat := 3994955563191098692615

theorem tailTrace_236322 : CollatzResearch.WordTrace tailWord_236322 prefixEnd_236322 3994955563191098692615 := by
  unfold tailWord_236322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154842862463307357359805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5746247633235486286292813 2154842862463307357359805)
  ·
    refine ⟨808066073423740259009927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2154842862463307357359805 808066073423740259009927)
    ·
      refine ⟨1212099110135610388514891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 808066073423740259009927 1212099110135610388514891)
      ·
        refine ⟨1818148665203415582772337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212099110135610388514891 1818148665203415582772337)
        ·
          refine ⟨1363611498902561687079253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818148665203415582772337 1363611498902561687079253)
          ·
            refine ⟨3994955563191098692615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1363611498902561687079253 3994955563191098692615)
            ·
              rfl

theorem cell20_236322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 10].length) (baseStart_236322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236322 prefixEnd_236322 := by exact prefixLift 236322
  have htrace : WordTrace (prefixWord ++ tailWord_236322) baseStart_236322 baseEnd_236322 := by
    simpa [prefixWord, tailWord_236322, baseEnd_236322] using wordTrace_append hprefix tailTrace_236322
  have hstable : (prefixWord ++ tailWord_236322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236322).length < 2 ^ (prefixWord ++ tailWord_236322).sum := by decide
  have hdescent : baseEnd_236322 < baseStart_236322 := by decide
  rcases family_descends (prefixWord ++ tailWord_236322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236332 : List Nat := [2, 2, 1, 1, 1, 4, 3, 4, 2]
def baseStart_236332 : Nat := 118140960795 + 236332 * 2 ^ 59
def prefixEnd_236332 : Nat := 4983230072969 + 3 ^ 40 * 236332 * 2
def baseEnd_236332 : Nat := 107868364478644074367231

theorem tailTrace_236332 : CollatzResearch.WordTrace tailWord_236332 prefixEnd_236332 107868364478644074367231 := by
  unfold tailWord_236332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4309868089908500568651625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5746490786544667424868833 4309868089908500568651625)
  ·
    refine ⟨3232401067431375426488719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4309868089908500568651625 3232401067431375426488719)
    ·
      refine ⟨4848601601147063139733079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3232401067431375426488719 4848601601147063139733079)
      ·
        refine ⟨7272902401720594709599619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4848601601147063139733079 7272902401720594709599619)
        ·
          refine ⟨10909353602580892064399429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7272902401720594709599619 10909353602580892064399429)
          ·
            refine ⟨2045503800483917262074893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10909353602580892064399429 2045503800483917262074893)
            ·
              refine ⟨767063925181468973278085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2045503800483917262074893 767063925181468973278085)
              ·
                refine ⟨143824485971525432489641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767063925181468973278085 143824485971525432489641)
                ·
                  refine ⟨107868364478644074367231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143824485971525432489641 107868364478644074367231)
                  ·
                    rfl

theorem cell20_236332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_236332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236332 prefixEnd_236332 := by exact prefixLift 236332
  have htrace : WordTrace (prefixWord ++ tailWord_236332) baseStart_236332 baseEnd_236332 := by
    simpa [prefixWord, tailWord_236332, baseEnd_236332] using wordTrace_append hprefix tailTrace_236332
  have hstable : (prefixWord ++ tailWord_236332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236332).length < 2 ^ (prefixWord ++ tailWord_236332).sum := by decide
  have hdescent : baseEnd_236332 < baseStart_236332 := by decide
  rcases family_descends (prefixWord ++ tailWord_236332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236336 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_236336 : Nat := 118140960795 + 236336 * 2 ^ 59
def prefixEnd_236336 : Nat := 4983230072969 + 3 ^ 40 * 236336 * 2
def baseEnd_236336 : Nat := 107870190187637838233881

theorem tailTrace_236336 : CollatzResearch.WordTrace tailWord_236336 prefixEnd_236336 107870190187637838233881 := by
  unfold tailWord_236336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4309941035901254910224431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5746588047868339880299241 4309941035901254910224431)
  ·
    refine ⟨6464911553851882365336647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4309941035901254910224431 6464911553851882365336647)
    ·
      refine ⟨9697367330777823548004971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6464911553851882365336647 9697367330777823548004971)
      ·
        refine ⟨14546050996166735322007457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9697367330777823548004971 14546050996166735322007457)
        ·
          refine ⟨10909538247125051491505593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14546050996166735322007457 10909538247125051491505593)
          ·
            refine ⟨8182153685343788618629195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10909538247125051491505593 8182153685343788618629195)
            ·
              refine ⟨12273230528015682927943793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8182153685343788618629195 12273230528015682927943793)
              ·
                refine ⟨9204922896011762195957845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12273230528015682927943793 9204922896011762195957845)
                ·
                  refine ⟨107870190187637838233881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9204922896011762195957845 107870190187637838233881)
                  ·
                    rfl

theorem cell20_236336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_236336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236336 prefixEnd_236336 := by exact prefixLift 236336
  have htrace : WordTrace (prefixWord ++ tailWord_236336) baseStart_236336 baseEnd_236336 := by
    simpa [prefixWord, tailWord_236336, baseEnd_236336] using wordTrace_append hprefix tailTrace_236336
  have hstable : (prefixWord ++ tailWord_236336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236336).length < 2 ^ (prefixWord ++ tailWord_236336).sum := by decide
  have hdescent : baseEnd_236336 < baseStart_236336 := by decide
  rcases family_descends (prefixWord ++ tailWord_236336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236339 : List Nat := [1, 1, 1, 2, 6, 3, 1, 5]
def baseStart_236339 : Nat := 118140960795 + 236339 * 2 ^ 59
def prefixEnd_236339 : Nat := 4983230072969 + 3 ^ 40 * 236339 * 2
def baseEnd_236339 : Nat := 35957186489794387044623

theorem tailTrace_236339 : CollatzResearch.WordTrace tailWord_236339 prefixEnd_236339 35957186489794387044623 := by
  unfold tailWord_236339
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619991490791641332808071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5746660993861094221872047 8619991490791641332808071)
  ·
    refine ⟨12929987236187461999212107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8619991490791641332808071 12929987236187461999212107)
    ·
      refine ⟨19394980854281192998818161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12929987236187461999212107 19394980854281192998818161)
      ·
        refine ⟨14546235640710894749113621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19394980854281192998818161 14546235640710894749113621)
        ·
          refine ⟨681854795658323191364701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14546235640710894749113621 681854795658323191364701)
          ·
            refine ⟨255695548371871196761763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 681854795658323191364701 255695548371871196761763)
            ·
              refine ⟨383543322557806795142645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255695548371871196761763 383543322557806795142645)
              ·
                refine ⟨35957186489794387044623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 383543322557806795142645 35957186489794387044623)
                ·
                  rfl

theorem cell20_236339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_236339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236339 prefixEnd_236339 := by exact prefixLift 236339
  have htrace : WordTrace (prefixWord ++ tailWord_236339) baseStart_236339 baseEnd_236339 := by
    simpa [prefixWord, tailWord_236339, baseEnd_236339] using wordTrace_append hprefix tailTrace_236339
  have hstable : (prefixWord ++ tailWord_236339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236339).length < 2 ^ (prefixWord ++ tailWord_236339).sum := by decide
  have hdescent : baseEnd_236339 < baseStart_236339 := by decide
  rcases family_descends (prefixWord ++ tailWord_236339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236380 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_236380 : Nat := 118140960795 + 236380 * 2 ^ 59
def prefixEnd_236380 : Nat := 4983230072969 + 3 ^ 40 * 236380 * 2
def baseEnd_236380 : Nat := 107890272986569240767035

theorem tailTrace_236380 : CollatzResearch.WordTrace tailWord_236380 prefixEnd_236380 107890272986569240767035 := by
  unfold tailWord_236380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310743441821552667525297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5747657922428736890033729 4310743441821552667525297)
  ·
    refine ⟨3233057581366164500643973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4310743441821552667525297 3233057581366164500643973)
    ·
      refine ⟨606198296506155843870745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3233057581366164500643973 606198296506155843870745)
      ·
        refine ⟨454648722379616882903059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606198296506155843870745 454648722379616882903059)
        ·
          refine ⟨681973083569425324354589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454648722379616882903059 681973083569425324354589)
          ·
            refine ⟨255739906338534496632971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 681973083569425324354589 255739906338534496632971)
            ·
              refine ⟨383609859507801744949457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255739906338534496632971 383609859507801744949457)
              ·
                refine ⟨287707394630851308712093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383609859507801744949457 287707394630851308712093)
                ·
                  refine ⟨107890272986569240767035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287707394630851308712093 107890272986569240767035)
                  ·
                    rfl

theorem cell20_236380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_236380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236380 prefixEnd_236380 := by exact prefixLift 236380
  have htrace : WordTrace (prefixWord ++ tailWord_236380) baseStart_236380 baseEnd_236380 := by
    simpa [prefixWord, tailWord_236380, baseEnd_236380] using wordTrace_append hprefix tailTrace_236380
  have hstable : (prefixWord ++ tailWord_236380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236380).length < 2 ^ (prefixWord ++ tailWord_236380).sum := by decide
  have hdescent : baseEnd_236380 < baseStart_236380 := by decide
  rcases family_descends (prefixWord ++ tailWord_236380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236391 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_236391 : Nat := 118140960795 + 236391 * 2 ^ 59
def prefixEnd_236391 : Nat := 4983230072969 + 3 ^ 40 * 236391 * 2
def baseEnd_236391 : Nat := 107895293686302091400323

theorem tailTrace_236391 : CollatzResearch.WordTrace tailWord_236391 prefixEnd_236391 107895293686302091400323 := by
  unfold tailWord_236391
  simp only [CollatzResearch.WordTrace]
  refine ⟨8621888086603254213701027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5747925391068836142467351 8621888086603254213701027)
  ·
    refine ⟨12932832129904881320551541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8621888086603254213701027 12932832129904881320551541)
    ·
      refine ⟨1212453012178582623801707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12932832129904881320551541 1212453012178582623801707)
      ·
        refine ⟨1818679518267873935702561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212453012178582623801707 1818679518267873935702561)
        ·
          refine ⟨1364009638700905451776921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818679518267873935702561 1364009638700905451776921)
          ·
            refine ⟨1023007229025679088832691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364009638700905451776921 1023007229025679088832691)
            ·
              refine ⟨1534510843538518633249037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023007229025679088832691 1534510843538518633249037)
              ·
                refine ⟨575441566326944487468389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1534510843538518633249037 575441566326944487468389)
                ·
                  refine ⟨107895293686302091400323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575441566326944487468389 107895293686302091400323)
                  ·
                    rfl

theorem cell20_236391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_236391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236391 prefixEnd_236391 := by exact prefixLift 236391
  have htrace : WordTrace (prefixWord ++ tailWord_236391) baseStart_236391 baseEnd_236391 := by
    simpa [prefixWord, tailWord_236391, baseEnd_236391] using wordTrace_append hprefix tailTrace_236391
  have hstable : (prefixWord ++ tailWord_236391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236391).length < 2 ^ (prefixWord ++ tailWord_236391).sum := by decide
  have hdescent : baseEnd_236391 < baseStart_236391 := by decide
  rcases family_descends (prefixWord ++ tailWord_236391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236401 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 3]
def baseStart_236401 : Nat := 118140960795 + 236401 * 2 ^ 59
def prefixEnd_236401 : Nat := 4983230072969 + 3 ^ 40 * 236401 * 2
def baseEnd_236401 : Nat := 107899857958786501066949

theorem tailTrace_236401 : CollatzResearch.WordTrace tailWord_236401 prefixEnd_236401 107899857958786501066949 := by
  unfold tailWord_236401
  simp only [CollatzResearch.WordTrace]
  refine ⟨8622252816567025921565057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5748168544378017281043371 8622252816567025921565057)
  ·
    refine ⟨6466689612425269441173793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8622252816567025921565057 6466689612425269441173793)
    ·
      refine ⟨4850017209318952080880345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6466689612425269441173793 4850017209318952080880345)
      ·
        refine ⟨3637512906989214060660259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4850017209318952080880345 3637512906989214060660259)
        ·
          refine ⟨5456269360483821090990389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637512906989214060660259 5456269360483821090990389)
          ·
            refine ⟨511525252545358227280349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5456269360483821090990389 511525252545358227280349)
            ·
              refine ⟨191821969704509335230131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511525252545358227280349 191821969704509335230131)
              ·
                refine ⟨287732954556764002845197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191821969704509335230131 287732954556764002845197)
                ·
                  refine ⟨107899857958786501066949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287732954556764002845197 107899857958786501066949)
                  ·
                    rfl

theorem cell20_236401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_236401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236401 prefixEnd_236401 := by exact prefixLift 236401
  have htrace : WordTrace (prefixWord ++ tailWord_236401) baseStart_236401 baseEnd_236401 := by
    simpa [prefixWord, tailWord_236401, baseEnd_236401] using wordTrace_append hprefix tailTrace_236401
  have hstable : (prefixWord ++ tailWord_236401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236401).length < 2 ^ (prefixWord ++ tailWord_236401).sum := by decide
  have hdescent : baseEnd_236401 < baseStart_236401 := by decide
  rcases family_descends (prefixWord ++ tailWord_236401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236425 : List Nat := [1, 2, 1, 1, 5, 4, 1, 3, 2]
def baseStart_236425 : Nat := 118140960795 + 236425 * 2 ^ 59
def prefixEnd_236425 : Nat := 4983230072969 + 3 ^ 40 * 236425 * 2
def baseEnd_236425 : Nat := 107910812212749084266851

theorem tailTrace_236425 : CollatzResearch.WordTrace tailWord_236425 prefixEnd_236425 107910812212749084266851 := by
  unfold tailWord_236425
  simp only [CollatzResearch.WordTrace]
  refine ⟨8623128168480078020438729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5748752112320052013625819 8623128168480078020438729)
  ·
    refine ⟨6467346126360058515329047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8623128168480078020438729 6467346126360058515329047)
    ·
      refine ⟨9701019189540087772993571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6467346126360058515329047 9701019189540087772993571)
      ·
        refine ⟨14551528784310131659490357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9701019189540087772993571 14551528784310131659490357)
        ·
          refine ⟨1364205823529074843077221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14551528784310131659490357 1364205823529074843077221)
          ·
            refine ⟨255788591911701533076979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1364205823529074843077221 255788591911701533076979)
            ·
              refine ⟨383682887867552299615469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255788591911701533076979 383682887867552299615469)
              ·
                refine ⟨143881082950332112355801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383682887867552299615469 143881082950332112355801)
                ·
                  refine ⟨107910812212749084266851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143881082950332112355801 107910812212749084266851)
                  ·
                    rfl

theorem cell20_236425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_236425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236425 prefixEnd_236425 := by exact prefixLift 236425
  have htrace : WordTrace (prefixWord ++ tailWord_236425) baseStart_236425 baseEnd_236425 := by
    simpa [prefixWord, tailWord_236425, baseEnd_236425] using wordTrace_append hprefix tailTrace_236425
  have hstable : (prefixWord ++ tailWord_236425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236425).length < 2 ^ (prefixWord ++ tailWord_236425).sum := by decide
  have hdescent : baseEnd_236425 < baseStart_236425 := by decide
  rcases family_descends (prefixWord ++ tailWord_236425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236438 : List Nat := [5, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_236438 : Nat := 118140960795 + 236438 * 2 ^ 59
def prefixEnd_236438 : Nat := 4983230072969 + 3 ^ 40 * 236438 * 2
def baseEnd_236438 : Nat := 107916745766978816833465

theorem tailTrace_236438 : CollatzResearch.WordTrace tailWord_236438 prefixEnd_236438 107916745766978816833465 := by
  unfold tailWord_236438
  simp only [CollatzResearch.WordTrace]
  refine ⟨538975144839561327541373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5749068211621987493774645 538975144839561327541373)
  ·
    refine ⟨202115679314835497828015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 538975144839561327541373 202115679314835497828015)
    ·
      refine ⟨303173518972253246742023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202115679314835497828015 303173518972253246742023)
      ·
        refine ⟨454760278458379870113035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303173518972253246742023 454760278458379870113035)
        ·
          refine ⟨682140417687569805169553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454760278458379870113035 682140417687569805169553)
          ·
            refine ⟨511605313265677353877165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682140417687569805169553 511605313265677353877165)
            ·
              refine ⟨191851992474629007703937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511605313265677353877165 191851992474629007703937)
              ·
                refine ⟨143888994355971755777953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191851992474629007703937 143888994355971755777953)
                ·
                  refine ⟨107916745766978816833465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143888994355971755777953 107916745766978816833465)
                  ·
                    rfl

theorem cell20_236438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_236438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236438 prefixEnd_236438 := by exact prefixLift 236438
  have htrace : WordTrace (prefixWord ++ tailWord_236438) baseStart_236438 baseEnd_236438 := by
    simpa [prefixWord, tailWord_236438, baseEnd_236438] using wordTrace_append hprefix tailTrace_236438
  have hstable : (prefixWord ++ tailWord_236438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236438).length < 2 ^ (prefixWord ++ tailWord_236438).sum := by decide
  have hdescent : baseEnd_236438 < baseStart_236438 := by decide
  rcases family_descends (prefixWord ++ tailWord_236438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236442 : List Nat := [3, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_236442 : Nat := 118140960795 + 236442 * 2 ^ 59
def prefixEnd_236442 : Nat := 4983230072969 + 3 ^ 40 * 236442 * 2
def baseEnd_236442 : Nat := 107918571475972580700115

theorem tailTrace_236442 : CollatzResearch.WordTrace tailWord_236442 prefixEnd_236442 107918571475972580700115 := by
  unfold tailWord_236442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155937052354622480951895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5749165472945659949205053 2155937052354622480951895)
  ·
    refine ⟨3233905578531933721427843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2155937052354622480951895 3233905578531933721427843)
    ·
      refine ⟨4850858367797900582141765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233905578531933721427843 4850858367797900582141765)
      ·
        refine ⟨909535943962106359151581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4850858367797900582141765 909535943962106359151581)
        ·
          refine ⟨341075978985789884681843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 909535943962106359151581 341075978985789884681843)
          ·
            refine ⟨511613968478684827022765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341075978985789884681843 511613968478684827022765)
            ·
              refine ⟨191855238179506810133537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511613968478684827022765 191855238179506810133537)
              ·
                refine ⟨143891428634630107600153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191855238179506810133537 143891428634630107600153)
                ·
                  refine ⟨107918571475972580700115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143891428634630107600153 107918571475972580700115)
                  ·
                    rfl

theorem cell20_236442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_236442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236442 prefixEnd_236442 := by exact prefixLift 236442
  have htrace : WordTrace (prefixWord ++ tailWord_236442) baseStart_236442 baseEnd_236442 := by
    simpa [prefixWord, tailWord_236442, baseEnd_236442] using wordTrace_append hprefix tailTrace_236442
  have hstable : (prefixWord ++ tailWord_236442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236442).length < 2 ^ (prefixWord ++ tailWord_236442).sum := by decide
  have hdescent : baseEnd_236442 < baseStart_236442 := by decide
  rcases family_descends (prefixWord ++ tailWord_236442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236493 : List Nat := [1, 6, 3, 1, 1, 2, 2, 2, 2]
def baseStart_236493 : Nat := 118140960795 + 236493 * 2 ^ 59
def prefixEnd_236493 : Nat := 4983230072969 + 3 ^ 40 * 236493 * 2
def baseEnd_236493 : Nat := 107941849265643069999907

theorem tailTrace_236493 : CollatzResearch.WordTrace tailWord_236493 prefixEnd_236493 107941849265643069999907 := by
  unfold tailWord_236493
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625608332233725633914133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5750405554822483755942755 8625608332233725633914133)
  ·
    refine ⟨404325390573455889089725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8625608332233725633914133 404325390573455889089725)
    ·
      refine ⟨151622021465045958408647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404325390573455889089725 151622021465045958408647)
      ·
        refine ⟨227433032197568937612971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151622021465045958408647 227433032197568937612971)
        ·
          refine ⟨341149548296353406419457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227433032197568937612971 341149548296353406419457)
          ·
            refine ⟨255862161222265054814593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341149548296353406419457 255862161222265054814593)
            ·
              refine ⟨191896620916698791110945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255862161222265054814593 191896620916698791110945)
              ·
                refine ⟨143922465687524093333209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191896620916698791110945 143922465687524093333209)
                ·
                  refine ⟨107941849265643069999907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143922465687524093333209 107941849265643069999907)
                  ·
                    rfl

theorem cell20_236493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_236493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236493 prefixEnd_236493 := by exact prefixLift 236493
  have htrace : WordTrace (prefixWord ++ tailWord_236493) baseStart_236493 baseEnd_236493 := by
    simpa [prefixWord, tailWord_236493, baseEnd_236493] using wordTrace_append hprefix tailTrace_236493
  have hstable : (prefixWord ++ tailWord_236493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236493).length < 2 ^ (prefixWord ++ tailWord_236493).sum := by decide
  have hdescent : baseEnd_236493 < baseStart_236493 := by decide
  rcases family_descends (prefixWord ++ tailWord_236493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236495 : List Nat := [1, 1, 2, 1, 1, 14]
def baseStart_236495 : Nat := 118140960795 + 236495 * 2 ^ 59
def prefixEnd_236495 : Nat := 4983230072969 + 3 ^ 40 * 236495 * 2
def baseEnd_236495 : Nat := 3997880078523701923453

theorem tailTrace_236495 : CollatzResearch.WordTrace tailWord_236495 prefixEnd_236495 3997880078523701923453 := by
  unfold tailWord_236495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625681278226479975486939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5750454185484319983657959 8625681278226479975486939)
  ·
    refine ⟨12938521917339719963230409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8625681278226479975486939 12938521917339719963230409)
    ·
      refine ⟨9703891438004789972422807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12938521917339719963230409 9703891438004789972422807)
      ·
        refine ⟨14555837157007184958634211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9703891438004789972422807 14555837157007184958634211)
        ·
          refine ⟨21833755735510777437951317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14555837157007184958634211 21833755735510777437951317)
          ·
            refine ⟨3997880078523701923453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 21833755735510777437951317 3997880078523701923453)
            ·
              rfl

theorem cell20_236495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 14].length) (baseStart_236495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236495 prefixEnd_236495 := by exact prefixLift 236495
  have htrace : WordTrace (prefixWord ++ tailWord_236495) baseStart_236495 baseEnd_236495 := by
    simpa [prefixWord, tailWord_236495, baseEnd_236495] using wordTrace_append hprefix tailTrace_236495
  have hstable : (prefixWord ++ tailWord_236495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236495).length < 2 ^ (prefixWord ++ tailWord_236495).sum := by decide
  have hdescent : baseEnd_236495 < baseStart_236495 := by decide
  rcases family_descends (prefixWord ++ tailWord_236495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236501 : List Nat := [1, 3, 2, 3, 3, 1, 1, 4, 2]
def baseStart_236501 : Nat := 118140960795 + 236501 * 2 ^ 59
def prefixEnd_236501 : Nat := 4983230072969 + 3 ^ 40 * 236501 * 2
def baseEnd_236501 : Nat := 107945500683630597733207

theorem tailTrace_236501 : CollatzResearch.WordTrace tailWord_236501 prefixEnd_236501 107945500683630597733207 := by
  unfold tailWord_236501
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625900116204743000205357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5750600077469828666803571 8625900116204743000205357)
  ·
    refine ⟨3234712543576778625077009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8625900116204743000205357 3234712543576778625077009)
    ·
      refine ⟨2426034407682583968807757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3234712543576778625077009 2426034407682583968807757)
      ·
        refine ⟨909762902880968988302909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2426034407682583968807757 909762902880968988302909)
        ·
          refine ⟨341161088580363370613591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 909762902880968988302909 341161088580363370613591)
          ·
            refine ⟨511741632870545055920387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341161088580363370613591 511741632870545055920387)
            ·
              refine ⟨767612449305817583880581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511741632870545055920387 767612449305817583880581)
              ·
                refine ⟨143927334244840796977609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767612449305817583880581 143927334244840796977609)
                ·
                  refine ⟨107945500683630597733207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143927334244840796977609 107945500683630597733207)
                  ·
                    rfl

theorem cell20_236501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_236501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236501 prefixEnd_236501 := by exact prefixLift 236501
  have htrace : WordTrace (prefixWord ++ tailWord_236501) baseStart_236501 baseEnd_236501 := by
    simpa [prefixWord, tailWord_236501, baseEnd_236501] using wordTrace_append hprefix tailTrace_236501
  have hstable : (prefixWord ++ tailWord_236501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236501).length < 2 ^ (prefixWord ++ tailWord_236501).sum := by decide
  have hdescent : baseEnd_236501 < baseStart_236501 := by decide
  rcases family_descends (prefixWord ++ tailWord_236501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236529 : List Nat := [1, 2, 2, 2, 4, 2, 3, 4]
def baseStart_236529 : Nat := 118140960795 + 236529 * 2 ^ 59
def prefixEnd_236529 : Nat := 4983230072969 + 3 ^ 40 * 236529 * 2
def baseEnd_236529 : Nat := 35986093548862314933253

theorem tailTrace_236529 : CollatzResearch.WordTrace tailWord_236529 prefixEnd_236529 35986093548862314933253 := by
  unfold tailWord_236529
  simp only [CollatzResearch.WordTrace]
  refine ⟨8626921360103303782224641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5751280906735535854816427 8626921360103303782224641)
  ·
    refine ⟨6470191020077477836668481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8626921360103303782224641 6470191020077477836668481)
    ·
      refine ⟨4852643265058108377501361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6470191020077477836668481 4852643265058108377501361)
      ·
        refine ⟨3639482448793581283126021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4852643265058108377501361 3639482448793581283126021)
        ·
          refine ⟨682402959148796490586129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3639482448793581283126021 682402959148796490586129)
          ·
            refine ⟨511802219361597367939597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682402959148796490586129 511802219361597367939597)
            ·
              refine ⟨191925832260599012977349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511802219361597367939597 191925832260599012977349)
              ·
                refine ⟨35986093548862314933253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191925832260599012977349 35986093548862314933253)
                ·
                  rfl

theorem cell20_236529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 4].length) (baseStart_236529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236529 prefixEnd_236529 := by exact prefixLift 236529
  have htrace : WordTrace (prefixWord ++ tailWord_236529) baseStart_236529 baseEnd_236529 := by
    simpa [prefixWord, tailWord_236529, baseEnd_236529] using wordTrace_append hprefix tailTrace_236529
  have hstable : (prefixWord ++ tailWord_236529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236529).length < 2 ^ (prefixWord ++ tailWord_236529).sum := by decide
  have hdescent : baseEnd_236529 < baseStart_236529 := by decide
  rcases family_descends (prefixWord ++ tailWord_236529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236546 : List Nat := [3, 4, 1, 3, 1, 1, 7]
def baseStart_236546 : Nat := 118140960795 + 236546 * 2 ^ 59
def prefixEnd_236546 : Nat := 4983230072969 + 3 ^ 40 * 236546 * 2
def baseEnd_236546 : Nat := 11996226656645604581447

theorem tailTrace_236546 : CollatzResearch.WordTrace tailWord_236546 prefixEnd_236546 11996226656645604581447 := by
  unfold tailWord_236546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156885350260428921398373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5751694267361143790395661 2156885350260428921398373)
  ·
    refine ⟨404416003173830422762195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2156885350260428921398373 404416003173830422762195)
    ·
      refine ⟨606624004760745634143293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404416003173830422762195 606624004760745634143293)
      ·
        refine ⟨227484001785279612803735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 606624004760745634143293 227484001785279612803735)
        ·
          refine ⟨341226002677919419205603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227484001785279612803735 341226002677919419205603)
          ·
            refine ⟨511839004016879128808405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341226002677919419205603 511839004016879128808405)
            ·
              refine ⟨11996226656645604581447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 511839004016879128808405 11996226656645604581447)
              ·
                rfl

theorem cell20_236546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 7].length) (baseStart_236546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236546 prefixEnd_236546 := by exact prefixLift 236546
  have htrace : WordTrace (prefixWord ++ tailWord_236546) baseStart_236546 baseEnd_236546 := by
    simpa [prefixWord, tailWord_236546, baseEnd_236546] using wordTrace_append hprefix tailTrace_236546
  have hstable : (prefixWord ++ tailWord_236546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236546).length < 2 ^ (prefixWord ++ tailWord_236546).sum := by decide
  have hdescent : baseEnd_236546 < baseStart_236546 := by decide
  rcases family_descends (prefixWord ++ tailWord_236546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236602 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_236602 : Nat := 118140960795 + 236602 * 2 ^ 59
def prefixEnd_236602 : Nat := 4983230072969 + 3 ^ 40 * 236602 * 2
def baseEnd_236602 : Nat := 107991599835723135366127

theorem tailTrace_236602 : CollatzResearch.WordTrace tailWord_236602 prefixEnd_236602 107991599835723135366127 := by
  unfold tailWord_236602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157395972209709312408015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5753055925892558166421373 2157395972209709312408015)
  ·
    refine ⟨3236093958314563968612023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2157395972209709312408015 3236093958314563968612023)
    ·
      refine ⟨4854140937471845952918035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3236093958314563968612023 4854140937471845952918035)
      ·
        refine ⟨7281211406207768929377053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854140937471845952918035 7281211406207768929377053)
        ·
          refine ⟨2730454277327913348516395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7281211406207768929377053 2730454277327913348516395)
          ·
            refine ⟨4095681415991870022774593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730454277327913348516395 4095681415991870022774593)
            ·
              refine ⟨3071761061993902517080945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4095681415991870022774593 3071761061993902517080945)
              ·
                refine ⟨2303820796495426887810709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3071761061993902517080945 2303820796495426887810709)
                ·
                  refine ⟨107991599835723135366127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2303820796495426887810709 107991599835723135366127)
                  ·
                    rfl

theorem cell20_236602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_236602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236602 prefixEnd_236602 := by exact prefixLift 236602
  have htrace : WordTrace (prefixWord ++ tailWord_236602) baseStart_236602 baseEnd_236602 := by
    simpa [prefixWord, tailWord_236602, baseEnd_236602] using wordTrace_append hprefix tailTrace_236602
  have hstable : (prefixWord ++ tailWord_236602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236602).length < 2 ^ (prefixWord ++ tailWord_236602).sum := by decide
  have hdescent : baseEnd_236602 < baseStart_236602 := by decide
  rcases family_descends (prefixWord ++ tailWord_236602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236615 : List Nat := [1, 1, 4, 1, 3, 3, 3, 2, 2]
def baseStart_236615 : Nat := 118140960795 + 236615 * 2 ^ 59
def prefixEnd_236615 : Nat := 4983230072969 + 3 ^ 40 * 236615 * 2
def baseEnd_236615 : Nat := 107997533389952867932741

theorem tailTrace_236615 : CollatzResearch.WordTrace tailWord_236615 prefixEnd_236615 107997533389952867932741 := by
  unfold tailWord_236615
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630058037791740469855299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5753372025194493646570199 8630058037791740469855299)
  ·
    refine ⟨12945087056687610704782949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8630058037791740469855299 12945087056687610704782949)
    ·
      refine ⟨2427203823128927007146803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12945087056687610704782949 2427203823128927007146803)
      ·
        refine ⟨3640805734693390510720205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427203823128927007146803 3640805734693390510720205)
        ·
          refine ⟨1365302150510021441520077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3640805734693390510720205 1365302150510021441520077)
          ·
            refine ⟨511988306441258040570029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1365302150510021441520077 511988306441258040570029)
            ·
              refine ⟨191995614915471765213761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511988306441258040570029 191995614915471765213761)
              ·
                refine ⟨143996711186603823910321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191995614915471765213761 143996711186603823910321)
                ·
                  refine ⟨107997533389952867932741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143996711186603823910321 107997533389952867932741)
                  ·
                    rfl

theorem cell20_236615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 2].length) (baseStart_236615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236615 prefixEnd_236615 := by exact prefixLift 236615
  have htrace : WordTrace (prefixWord ++ tailWord_236615) baseStart_236615 baseEnd_236615 := by
    simpa [prefixWord, tailWord_236615, baseEnd_236615] using wordTrace_append hprefix tailTrace_236615
  have hstable : (prefixWord ++ tailWord_236615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236615).length < 2 ^ (prefixWord ++ tailWord_236615).sum := by decide
  have hdescent : baseEnd_236615 < baseStart_236615 := by decide
  rcases family_descends (prefixWord ++ tailWord_236615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236626 : List Nat := [3, 2, 2, 1, 3, 1, 1, 7]
def baseStart_236626 : Nat := 118140960795 + 236626 * 2 ^ 59
def prefixEnd_236626 : Nat := 4983230072969 + 3 ^ 40 * 236626 * 2
def baseEnd_236626 : Nat := 36000851363228572855343

theorem tailTrace_236626 : CollatzResearch.WordTrace tailWord_236626 prefixEnd_236626 36000851363228572855343 := by
  unfold tailWord_236626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157614810187972337126433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5753639493834592899003821 2157614810187972337126433)
  ·
    refine ⟨1618211107640979252844825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2157614810187972337126433 1618211107640979252844825)
    ·
      refine ⟨1213658330730734439633619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1618211107640979252844825 1213658330730734439633619)
      ·
        refine ⟨1820487496096101659450429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213658330730734439633619 1820487496096101659450429)
        ·
          refine ⟨682682811036038122293911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1820487496096101659450429 682682811036038122293911)
          ·
            refine ⟨1024024216554057183440867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682682811036038122293911 1024024216554057183440867)
            ·
              refine ⟨1536036324831085775161301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024024216554057183440867 1536036324831085775161301)
              ·
                refine ⟨36000851363228572855343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1536036324831085775161301 36000851363228572855343)
                ·
                  rfl

theorem cell20_236626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_236626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236626 prefixEnd_236626 := by exact prefixLift 236626
  have htrace : WordTrace (prefixWord ++ tailWord_236626) baseStart_236626 baseEnd_236626 := by
    simpa [prefixWord, tailWord_236626, baseEnd_236626] using wordTrace_append hprefix tailTrace_236626
  have hstable : (prefixWord ++ tailWord_236626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236626).length < 2 ^ (prefixWord ++ tailWord_236626).sum := by decide
  have hdescent : baseEnd_236626 < baseStart_236626 := by decide
  rcases family_descends (prefixWord ++ tailWord_236626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236640 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_236640 : Nat := 118140960795 + 236640 * 2 ^ 59
def prefixEnd_236640 : Nat := 4983230072969 + 3 ^ 40 * 236640 * 2
def baseEnd_236640 : Nat := 108008944071163892099305

theorem tailTrace_236640 : CollatzResearch.WordTrace tailWord_236640 prefixEnd_236640 108008944071163892099305 := by
  unfold tailWord_236640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315484931350584869757687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5753979908467446493010249 4315484931350584869757687)
  ·
    refine ⟨6473227397025877304636531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4315484931350584869757687 6473227397025877304636531)
    ·
      refine ⟨9709841095538815956954797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473227397025877304636531 9709841095538815956954797)
      ·
        refine ⟨3641190410827055983858049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9709841095538815956954797 3641190410827055983858049)
        ·
          refine ⟨2730892808120291987893537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3641190410827055983858049 2730892808120291987893537)
          ·
            refine ⟨2048169606090218990920153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730892808120291987893537 2048169606090218990920153)
            ·
              refine ⟨1536127204567664243190115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048169606090218990920153 1536127204567664243190115)
              ·
                refine ⟨2304190806851496364785173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536127204567664243190115 2304190806851496364785173)
                ·
                  refine ⟨108008944071163892099305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2304190806851496364785173 108008944071163892099305)
                  ·
                    rfl

theorem cell20_236640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_236640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236640 prefixEnd_236640 := by exact prefixLift 236640
  have htrace : WordTrace (prefixWord ++ tailWord_236640) baseStart_236640 baseEnd_236640 := by
    simpa [prefixWord, tailWord_236640, baseEnd_236640] using wordTrace_append hprefix tailTrace_236640
  have hstable : (prefixWord ++ tailWord_236640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236640).length < 2 ^ (prefixWord ++ tailWord_236640).sum := by decide
  have hdescent : baseEnd_236640 < baseStart_236640 := by decide
  rcases family_descends (prefixWord ++ tailWord_236640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236695 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 4]
def baseStart_236695 : Nat := 118140960795 + 236695 * 2 ^ 59
def prefixEnd_236695 : Nat := 4983230072969 + 3 ^ 40 * 236695 * 2
def baseEnd_236695 : Nat := 108034047569828145265747

theorem tailTrace_236695 : CollatzResearch.WordTrace tailWord_236695 prefixEnd_236695 108034047569828145265747 := by
  unfold tailWord_236695
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632975877501914132767539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5755317251667942755178359 8632975877501914132767539)
  ·
    refine ⟨12949463816252871199151309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8632975877501914132767539 12949463816252871199151309)
    ·
      refine ⟨4856048931094826699681741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12949463816252871199151309 4856048931094826699681741)
      ·
        refine ⟨1821018349160560012380653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4856048931094826699681741 1821018349160560012380653)
        ·
          refine ⟨682881880935210004642745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1821018349160560012380653 682881880935210004642745)
          ·
            refine ⟨512161410701407503482059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682881880935210004642745 512161410701407503482059)
            ·
              refine ⟨768242116052111255223089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512161410701407503482059 768242116052111255223089)
              ·
                refine ⟨576181587039083441417317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768242116052111255223089 576181587039083441417317)
                ·
                  refine ⟨108034047569828145265747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576181587039083441417317 108034047569828145265747)
                  ·
                    rfl

theorem cell20_236695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_236695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236695 prefixEnd_236695 := by exact prefixLift 236695
  have htrace : WordTrace (prefixWord ++ tailWord_236695) baseStart_236695 baseEnd_236695 := by
    simpa [prefixWord, tailWord_236695, baseEnd_236695] using wordTrace_append hprefix tailTrace_236695
  have hstable : (prefixWord ++ tailWord_236695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236695).length < 2 ^ (prefixWord ++ tailWord_236695).sum := by decide
  have hdescent : baseEnd_236695 < baseStart_236695 := by decide
  rcases family_descends (prefixWord ++ tailWord_236695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236757 : List Nat := [1, 3, 2, 4, 1, 1, 4, 4]
def baseStart_236757 : Nat := 118140960795 + 236757 * 2 ^ 59
def prefixEnd_236757 : Nat := 4983230072969 + 3 ^ 40 * 236757 * 2
def baseEnd_236757 : Nat := 36020782019743828399609

theorem tailTrace_236757 : CollatzResearch.WordTrace tailWord_236757 prefixEnd_236757 36020782019743828399609 := by
  unfold tailWord_236757
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635237203277298721524525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5756824802184865814349683 8635237203277298721524525)
  ·
    refine ⟨3238213951228987020571697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8635237203277298721524525 3238213951228987020571697)
    ·
      refine ⟨2428660463421740265428773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3238213951228987020571697 2428660463421740265428773)
      ·
        refine ⟨455373836891576299767895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2428660463421740265428773 455373836891576299767895)
        ·
          refine ⟨683060755337364449651843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455373836891576299767895 683060755337364449651843)
          ·
            refine ⟨1024591133006046674477765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683060755337364449651843 1024591133006046674477765)
            ·
              refine ⟨192110837438633751464581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1024591133006046674477765 192110837438633751464581)
              ·
                refine ⟨36020782019743828399609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192110837438633751464581 36020782019743828399609)
                ·
                  rfl

theorem cell20_236757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 4].length) (baseStart_236757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236757 prefixEnd_236757 := by exact prefixLift 236757
  have htrace : WordTrace (prefixWord ++ tailWord_236757) baseStart_236757 baseEnd_236757 := by
    simpa [prefixWord, tailWord_236757, baseEnd_236757] using wordTrace_append hprefix tailTrace_236757
  have hstable : (prefixWord ++ tailWord_236757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236757).length < 2 ^ (prefixWord ++ tailWord_236757).sum := by decide
  have hdescent : baseEnd_236757 < baseStart_236757 := by decide
  rcases family_descends (prefixWord ++ tailWord_236757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236778 : List Nat := [3, 1, 3, 1, 1, 5, 6]
def baseStart_236778 : Nat := 118140960795 + 236778 * 2 ^ 59
def prefixEnd_236778 : Nat := 4983230072969 + 3 ^ 40 * 236778 * 2
def baseEnd_236778 : Nat := 12007992336827638388749

theorem tailTrace_236778 : CollatzResearch.WordTrace tailWord_236778 prefixEnd_236778 12007992336827638388749 := by
  unfold tailWord_236778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159000784050304827009747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5757335424134146205359325 2159000784050304827009747)
  ·
    refine ⟨3238501176075457240514621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2159000784050304827009747 3238501176075457240514621)
    ·
      refine ⟨1214437941028296465192983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3238501176075457240514621 1214437941028296465192983)
      ·
        refine ⟨1821656911542444697789475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214437941028296465192983 1821656911542444697789475)
        ·
          refine ⟨2732485367313667046684213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821656911542444697789475 2732485367313667046684213)
          ·
            refine ⟨256170503185656285626645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2732485367313667046684213 256170503185656285626645)
            ·
              refine ⟨12007992336827638388749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256170503185656285626645 12007992336827638388749)
              ·
                rfl

theorem cell20_236778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 6].length) (baseStart_236778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236778 prefixEnd_236778 := by exact prefixLift 236778
  have htrace : WordTrace (prefixWord ++ tailWord_236778) baseStart_236778 baseEnd_236778 := by
    simpa [prefixWord, tailWord_236778, baseEnd_236778] using wordTrace_append hprefix tailTrace_236778
  have hstable : (prefixWord ++ tailWord_236778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236778).length < 2 ^ (prefixWord ++ tailWord_236778).sum := by decide
  have hdescent : baseEnd_236778 < baseStart_236778 := by decide
  rcases family_descends (prefixWord ++ tailWord_236778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236785 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 3]
def baseStart_236785 : Nat := 118140960795 + 236785 * 2 ^ 59
def prefixEnd_236785 : Nat := 4983230072969 + 3 ^ 40 * 236785 * 2
def baseEnd_236785 : Nat := 108075126022187832265379

theorem tailTrace_236785 : CollatzResearch.WordTrace tailWord_236785 prefixEnd_236785 108075126022187832265379 := by
  unfold tailWord_236785
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636258447175859503543809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5757505631450573002362539 8636258447175859503543809)
  ·
    refine ⟨6477193835381894627657857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8636258447175859503543809 6477193835381894627657857)
    ·
      refine ⟨4857895376536420970743393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6477193835381894627657857 4857895376536420970743393)
      ·
        refine ⟨3643421532402315728057545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4857895376536420970743393 3643421532402315728057545)
        ·
          refine ⟨2732566149301736796043159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3643421532402315728057545 2732566149301736796043159)
          ·
            refine ⟨4098849223952605194064739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732566149301736796043159 4098849223952605194064739)
            ·
              refine ⟨6148273835928907791097109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098849223952605194064739 6148273835928907791097109)
              ·
                refine ⟨288200336059167552707677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6148273835928907791097109 288200336059167552707677)
                ·
                  refine ⟨108075126022187832265379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288200336059167552707677 108075126022187832265379)
                  ·
                    rfl

theorem cell20_236785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_236785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236785 prefixEnd_236785 := by exact prefixLift 236785
  have htrace : WordTrace (prefixWord ++ tailWord_236785) baseStart_236785 baseEnd_236785 := by
    simpa [prefixWord, tailWord_236785, baseEnd_236785] using wordTrace_append hprefix tailTrace_236785
  have hstable : (prefixWord ++ tailWord_236785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236785).length < 2 ^ (prefixWord ++ tailWord_236785).sum := by decide
  have hdescent : baseEnd_236785 < baseStart_236785 := by decide
  rcases family_descends (prefixWord ++ tailWord_236785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236798 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_236798 : Nat := 118140960795 + 236798 * 2 ^ 59
def prefixEnd_236798 : Nat := 4983230072969 + 3 ^ 40 * 236798 * 2
def baseEnd_236798 : Nat := 108081059576417564831993

theorem tailTrace_236798 : CollatzResearch.WordTrace tailWord_236798 prefixEnd_236798 108081059576417564831993 := by
  unfold tailWord_236798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079591574516095340470881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5757821730752508482511365 1079591574516095340470881)
  ·
    refine ⟨809693680887071505353161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1079591574516095340470881 809693680887071505353161)
    ·
      refine ⟨607270260665303629014871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 809693680887071505353161 607270260665303629014871)
      ·
        refine ⟨910905390997955443522307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607270260665303629014871 910905390997955443522307)
        ·
          refine ⟨1366358086496933165283461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910905390997955443522307 1366358086496933165283461)
          ·
            refine ⟨256192141218174968490649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1366358086496933165283461 256192141218174968490649)
            ·
              refine ⟨192144105913631226367987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256192141218174968490649 192144105913631226367987)
              ·
                refine ⟨288216158870446839551981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192144105913631226367987 288216158870446839551981)
                ·
                  refine ⟨108081059576417564831993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288216158870446839551981 108081059576417564831993)
                  ·
                    rfl

theorem cell20_236798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_236798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236798 prefixEnd_236798 := by exact prefixLift 236798
  have htrace : WordTrace (prefixWord ++ tailWord_236798) baseStart_236798 baseEnd_236798 := by
    simpa [prefixWord, tailWord_236798, baseEnd_236798] using wordTrace_append hprefix tailTrace_236798
  have hstable : (prefixWord ++ tailWord_236798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236798).length < 2 ^ (prefixWord ++ tailWord_236798).sum := by decide
  have hdescent : baseEnd_236798 < baseStart_236798 := by decide
  rcases family_descends (prefixWord ++ tailWord_236798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236799 : List Nat := [1, 1, 2, 2, 1, 5, 1, 7]
def baseStart_236799 : Nat := 118140960795 + 236799 * 2 ^ 59
def prefixEnd_236799 : Nat := 4983230072969 + 3 ^ 40 * 236799 * 2
def baseEnd_236799 : Nat := 36027172001222001932885

theorem tailTrace_236799 : CollatzResearch.WordTrace tailWord_236799 prefixEnd_236799 36027172001222001932885 := by
  unfold tailWord_236799
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636769069125139894553451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5757846046083426596368967 8636769069125139894553451)
  ·
    refine ⟨12955153603687709841830177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8636769069125139894553451 12955153603687709841830177)
    ·
      refine ⟨9716365202765782381372633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12955153603687709841830177 9716365202765782381372633)
      ·
        refine ⟨7287273902074336786029475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9716365202765782381372633 7287273902074336786029475)
        ·
          refine ⟨10930910853111505179044213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287273902074336786029475 10930910853111505179044213)
          ·
            refine ⟨1024772892479203610535395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10930910853111505179044213 1024772892479203610535395)
            ·
              refine ⟨1537159338718805415803093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024772892479203610535395 1537159338718805415803093)
              ·
                refine ⟨36027172001222001932885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1537159338718805415803093 36027172001222001932885)
                ·
                  rfl

theorem cell20_236799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_236799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236799 prefixEnd_236799 := by exact prefixLift 236799
  have htrace : WordTrace (prefixWord ++ tailWord_236799) baseStart_236799 baseEnd_236799 := by
    simpa [prefixWord, tailWord_236799, baseEnd_236799] using wordTrace_append hprefix tailTrace_236799
  have hstable : (prefixWord ++ tailWord_236799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236799).length < 2 ^ (prefixWord ++ tailWord_236799).sum := by decide
  have hdescent : baseEnd_236799 < baseStart_236799 := by decide
  rcases family_descends (prefixWord ++ tailWord_236799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236837 : List Nat := [1, 3, 1, 2, 4, 9]
def baseStart_236837 : Nat := 118140960795 + 236837 * 2 ^ 59
def prefixEnd_236837 : Nat := 4983230072969 + 3 ^ 40 * 236837 * 2
def baseEnd_236837 : Nat := 4003661490337287501179

theorem tailTrace_236837 : CollatzResearch.WordTrace tailWord_236837 prefixEnd_236837 4003661490337287501179 := by
  unfold tailWord_236837
  simp only [CollatzResearch.WordTrace]
  refine ⟨8638155042987472384436765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5758770028658314922957843 8638155042987472384436765)
  ·
    refine ⟨3239308141120302144163787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8638155042987472384436765 3239308141120302144163787)
    ·
      refine ⟨4858962211680453216245681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3239308141120302144163787 4858962211680453216245681)
      ·
        refine ⟨3644221658760339912184261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4858962211680453216245681 3644221658760339912184261)
        ·
          refine ⟨683291561017563733534549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3644221658760339912184261 683291561017563733534549)
          ·
            refine ⟨4003661490337287501179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 683291561017563733534549 4003661490337287501179)
            ·
              rfl

theorem cell20_236837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 9].length) (baseStart_236837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236837 prefixEnd_236837 := by exact prefixLift 236837
  have htrace : WordTrace (prefixWord ++ tailWord_236837) baseStart_236837 baseEnd_236837 := by
    simpa [prefixWord, tailWord_236837, baseEnd_236837] using wordTrace_append hprefix tailTrace_236837
  have hstable : (prefixWord ++ tailWord_236837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236837).length < 2 ^ (prefixWord ++ tailWord_236837).sum := by decide
  have hdescent : baseEnd_236837 < baseStart_236837 := by decide
  rcases family_descends (prefixWord ++ tailWord_236837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236840 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_236840 : Nat := 118140960795 + 236840 * 2 ^ 59
def prefixEnd_236840 : Nat := 4983230072969 + 3 ^ 40 * 236840 * 2
def baseEnd_236840 : Nat := 108100229520852085431821

theorem tailTrace_236840 : CollatzResearch.WordTrace tailWord_236840 prefixEnd_236840 108100229520852085431821 := by
  unfold tailWord_236840
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319132230988301948397987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5758842974651069264530649 4319132230988301948397987)
  ·
    refine ⟨6478698346482452922596981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4319132230988301948397987 6478698346482452922596981)
    ·
      refine ⟨607377969982729961493467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6478698346482452922596981 607377969982729961493467)
      ·
        refine ⟨911066954974094942240201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607377969982729961493467 911066954974094942240201)
        ·
          refine ⟨683300216230571206680151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911066954974094942240201 683300216230571206680151)
          ·
            refine ⟨1024950324345856810020227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683300216230571206680151 1024950324345856810020227)
            ·
              refine ⟨1537425486518785215030341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024950324345856810020227 1537425486518785215030341)
              ·
                refine ⟨288267278722272227818189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1537425486518785215030341 288267278722272227818189)
                ·
                  refine ⟨108100229520852085431821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288267278722272227818189 108100229520852085431821)
                  ·
                    rfl

theorem cell20_236840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_236840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236840 prefixEnd_236840 := by exact prefixLift 236840
  have htrace : WordTrace (prefixWord ++ tailWord_236840) baseStart_236840 baseEnd_236840 := by
    simpa [prefixWord, tailWord_236840, baseEnd_236840] using wordTrace_append hprefix tailTrace_236840
  have hstable : (prefixWord ++ tailWord_236840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236840).length < 2 ^ (prefixWord ++ tailWord_236840).sum := by decide
  have hdescent : baseEnd_236840 < baseStart_236840 := by decide
  rcases family_descends (prefixWord ++ tailWord_236840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236899 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_236899 : Nat := 118140960795 + 236899 * 2 ^ 59
def prefixEnd_236899 : Nat := 4983230072969 + 3 ^ 40 * 236899 * 2
def baseEnd_236899 : Nat := 108127158728510102464913

theorem tailTrace_236899 : CollatzResearch.WordTrace tailWord_236899 prefixEnd_236899 108127158728510102464913 := by
  unfold tailWord_236899
  simp only [CollatzResearch.WordTrace]
  refine ⟨8640416368762856973193751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5760277579175237982129167 8640416368762856973193751)
  ·
    refine ⟨12960624553144285459790627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8640416368762856973193751 12960624553144285459790627)
    ·
      refine ⟨19440936829716428189685941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12960624553144285459790627 19440936829716428189685941)
      ·
        refine ⟨1822587827785915142783057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19440936829716428189685941 1822587827785915142783057)
        ·
          refine ⟨1366940870839436357087293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822587827785915142783057 1366940870839436357087293)
          ·
            refine ⟨512602826564788633907735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1366940870839436357087293 512602826564788633907735)
            ·
              refine ⟨768904239847182950861603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512602826564788633907735 768904239847182950861603)
              ·
                refine ⟨1153356359770774426292405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768904239847182950861603 1153356359770774426292405)
                ·
                  refine ⟨108127158728510102464913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1153356359770774426292405 108127158728510102464913)
                  ·
                    rfl

theorem cell20_236899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_236899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236899 prefixEnd_236899 := by exact prefixLift 236899
  have htrace : WordTrace (prefixWord ++ tailWord_236899) baseStart_236899 baseEnd_236899 := by
    simpa [prefixWord, tailWord_236899, baseEnd_236899] using wordTrace_append hprefix tailTrace_236899
  have hstable : (prefixWord ++ tailWord_236899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236899).length < 2 ^ (prefixWord ++ tailWord_236899).sum := by decide
  have hdescent : baseEnd_236899 < baseStart_236899 := by decide
  rcases family_descends (prefixWord ++ tailWord_236899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236926 : List Nat := [4, 2, 3, 2, 1, 1, 1, 6]
def baseStart_236926 : Nat := 118140960795 + 236926 * 2 ^ 59
def prefixEnd_236926 : Nat := 4983230072969 + 3 ^ 40 * 236926 * 2
def baseEnd_236926 : Nat := 36046494088072669521601

theorem tailTrace_236926 : CollatzResearch.WordTrace tailWord_236926 prefixEnd_236926 36046494088072669521601 := by
  unfold tailWord_236926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080175142458130073053329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5760934093110027056284421 1080175142458130073053329)
  ·
    refine ⟨810131356843597554789997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1080175142458130073053329 810131356843597554789997)
    ·
      refine ⟨303799258816349083046249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 810131356843597554789997 303799258816349083046249)
      ·
        refine ⟨227849444112261812284687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303799258816349083046249 227849444112261812284687)
        ·
          refine ⟨341774166168392718427031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227849444112261812284687 341774166168392718427031)
          ·
            refine ⟨512661249252589077640547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341774166168392718427031 512661249252589077640547)
            ·
              refine ⟨768991873878883616460821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512661249252589077640547 768991873878883616460821)
              ·
                refine ⟨36046494088072669521601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 768991873878883616460821 36046494088072669521601)
                ·
                  rfl

theorem cell20_236926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_236926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236926 prefixEnd_236926 := by exact prefixLift 236926
  have htrace : WordTrace (prefixWord ++ tailWord_236926) baseStart_236926 baseEnd_236926 := by
    simpa [prefixWord, tailWord_236926, baseEnd_236926] using wordTrace_append hprefix tailTrace_236926
  have hstable : (prefixWord ++ tailWord_236926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236926).length < 2 ^ (prefixWord ++ tailWord_236926).sum := by decide
  have hdescent : baseEnd_236926 < baseStart_236926 := by decide
  rcases family_descends (prefixWord ++ tailWord_236926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236957 : List Nat := [1, 4, 2, 1, 3, 2, 3, 2, 2]
def baseStart_236957 : Nat := 118140960795 + 236957 * 2 ^ 59
def prefixEnd_236957 : Nat := 4983230072969 + 3 ^ 40 * 236957 * 2
def baseEnd_236957 : Nat := 108153631508919678531343

theorem tailTrace_236957 : CollatzResearch.WordTrace tailWord_236957 prefixEnd_236957 108153631508919678531343 := by
  unfold tailWord_236957
  simp only [CollatzResearch.WordTrace]
  refine ⟨8642531802552732878805125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5761687868368488585870083 8642531802552732878805125)
  ·
    refine ⟨1620474712978637414775961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8642531802552732878805125 1620474712978637414775961)
    ·
      refine ⟨1215356034733978061081971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1620474712978637414775961 1215356034733978061081971)
      ·
        refine ⟨1823034052100967091622957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215356034733978061081971 1823034052100967091622957)
        ·
          refine ⟨683637769537862659358609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1823034052100967091622957 683637769537862659358609)
          ·
            refine ⟨512728327153396994518957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683637769537862659358609 512728327153396994518957)
            ·
              refine ⟨192273122682523872944609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512728327153396994518957 192273122682523872944609)
              ·
                refine ⟨144204842011892904708457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192273122682523872944609 144204842011892904708457)
                ·
                  refine ⟨108153631508919678531343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144204842011892904708457 108153631508919678531343)
                  ·
                    rfl

theorem cell20_236957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_236957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236957 prefixEnd_236957 := by exact prefixLift 236957
  have htrace : WordTrace (prefixWord ++ tailWord_236957) baseStart_236957 baseEnd_236957 := by
    simpa [prefixWord, tailWord_236957, baseEnd_236957] using wordTrace_append hprefix tailTrace_236957
  have hstable : (prefixWord ++ tailWord_236957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236957).length < 2 ^ (prefixWord ++ tailWord_236957).sum := by decide
  have hdescent : baseEnd_236957 < baseStart_236957 := by decide
  rcases family_descends (prefixWord ++ tailWord_236957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236989 : List Nat := [1, 4, 1, 2, 2, 1, 1, 8]
def baseStart_236989 : Nat := 118140960795 + 236989 * 2 ^ 59
def prefixEnd_236989 : Nat := 4983230072969 + 3 ^ 40 * 236989 * 2
def baseEnd_236989 : Nat := 36056079060289929821515

theorem tailTrace_236989 : CollatzResearch.WordTrace tailWord_236989 prefixEnd_236989 36056079060289929821515 := by
  unfold tailWord_236989
  simp only [CollatzResearch.WordTrace]
  refine ⟨8643698938436802343970021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5762465958957868229313347 8643698938436802343970021)
  ·
    refine ⟨1620693550956900439494379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8643698938436802343970021 1620693550956900439494379)
    ·
      refine ⟨2431040326435350659241569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620693550956900439494379 2431040326435350659241569)
      ·
        refine ⟨1823280244826512994431177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2431040326435350659241569 1823280244826512994431177)
        ·
          refine ⟨1367460183619884745823383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1823280244826512994431177 1367460183619884745823383)
          ·
            refine ⟨2051190275429827118735075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367460183619884745823383 2051190275429827118735075)
            ·
              refine ⟨3076785413144740678102613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051190275429827118735075 3076785413144740678102613)
              ·
                refine ⟨36056079060289929821515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3076785413144740678102613 36056079060289929821515)
                ·
                  rfl

theorem cell20_236989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_236989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236989 prefixEnd_236989 := by exact prefixLift 236989
  have htrace : WordTrace (prefixWord ++ tailWord_236989) baseStart_236989 baseEnd_236989 := by
    simpa [prefixWord, tailWord_236989, baseEnd_236989] using wordTrace_append hprefix tailTrace_236989
  have hstable : (prefixWord ++ tailWord_236989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236989).length < 2 ^ (prefixWord ++ tailWord_236989).sum := by decide
  have hdescent : baseEnd_236989 < baseStart_236989 := by decide
  rcases family_descends (prefixWord ++ tailWord_236989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236999 : List Nat := [1, 1, 4, 1, 1, 3, 2, 5, 2]
def baseStart_236999 : Nat := 118140960795 + 236999 * 2 ^ 59
def prefixEnd_236999 : Nat := 4983230072969 + 3 ^ 40 * 236999 * 2
def baseEnd_236999 : Nat := 108172801453354199131171

theorem tailTrace_236999 : CollatzResearch.WordTrace tailWord_236999 prefixEnd_236999 108172801453354199131171 := by
  unfold tailWord_236999
  simp only [CollatzResearch.WordTrace]
  refine ⟨8644063668400574051834051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5762709112267049367889367 8644063668400574051834051)
  ·
    refine ⟨12966095502600861077751077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8644063668400574051834051 12966095502600861077751077)
    ·
      refine ⟨2431142906737661452078327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12966095502600861077751077 2431142906737661452078327)
      ·
        refine ⟨3646714360106492178117491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431142906737661452078327 3646714360106492178117491)
        ·
          refine ⟨5470071540159738267176237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3646714360106492178117491 5470071540159738267176237)
          ·
            refine ⟨2051276827559901850191089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5470071540159738267176237 2051276827559901850191089)
            ·
              refine ⟨1538457620669926387643317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051276827559901850191089 1538457620669926387643317)
              ·
                refine ⟨144230401937805598841561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1538457620669926387643317 144230401937805598841561)
                ·
                  refine ⟨108172801453354199131171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144230401937805598841561 108172801453354199131171)
                  ·
                    rfl

theorem cell20_236999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 2].length) (baseStart_236999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_236999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_236999 prefixEnd_236999 := by exact prefixLift 236999
  have htrace : WordTrace (prefixWord ++ tailWord_236999) baseStart_236999 baseEnd_236999 := by
    simpa [prefixWord, tailWord_236999, baseEnd_236999] using wordTrace_append hprefix tailTrace_236999
  have hstable : (prefixWord ++ tailWord_236999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236999).length < 2 ^ (prefixWord ++ tailWord_236999).sum := by decide
  have hdescent : baseEnd_236999 < baseStart_236999 := by decide
  rcases family_descends (prefixWord ++ tailWord_236999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237012 : List Nat := [2, 4, 1, 2, 3, 2, 2, 2, 2]
def baseStart_237012 : Nat := 118140960795 + 237012 * 2 ^ 59
def prefixEnd_237012 : Nat := 4983230072969 + 3 ^ 40 * 237012 * 2
def baseEnd_237012 : Nat := 108178735007583931697785

theorem tailTrace_237012 : CollatzResearch.WordTrace tailWord_237012 prefixEnd_237012 108178735007583931697785 := by
  unfold tailWord_237012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322268908676738636028645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5763025211568984848038193 4322268908676738636028645)
  ·
    refine ⟨810425420376888494255371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4322268908676738636028645 810425420376888494255371)
    ·
      refine ⟨1215638130565332741383057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810425420376888494255371 1215638130565332741383057)
      ·
        refine ⟨911728597923999556037293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1215638130565332741383057 911728597923999556037293)
        ·
          refine ⟨341898224221499833513985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 911728597923999556037293 341898224221499833513985)
          ·
            refine ⟨256423668166124875135489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341898224221499833513985 256423668166124875135489)
            ·
              refine ⟨192317751124593656351617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256423668166124875135489 192317751124593656351617)
              ·
                refine ⟨144238313343445242263713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192317751124593656351617 144238313343445242263713)
                ·
                  refine ⟨108178735007583931697785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144238313343445242263713 108178735007583931697785)
                  ·
                    rfl

theorem cell20_237012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_237012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237012 prefixEnd_237012 := by exact prefixLift 237012
  have htrace : WordTrace (prefixWord ++ tailWord_237012) baseStart_237012 baseEnd_237012 := by
    simpa [prefixWord, tailWord_237012, baseEnd_237012] using wordTrace_append hprefix tailTrace_237012
  have hstable : (prefixWord ++ tailWord_237012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237012).length < 2 ^ (prefixWord ++ tailWord_237012).sum := by decide
  have hdescent : baseEnd_237012 < baseStart_237012 := by decide
  rcases family_descends (prefixWord ++ tailWord_237012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237016 : List Nat := [2, 1, 2, 2, 2, 1, 6, 2, 2]
def baseStart_237016 : Nat := 118140960795 + 237016 * 2 ^ 59
def prefixEnd_237016 : Nat := 4983230072969 + 3 ^ 40 * 237016 * 2
def baseEnd_237016 : Nat := 108180560716577695564435

theorem tailTrace_237016 : CollatzResearch.WordTrace tailWord_237016 prefixEnd_237016 108180560716577695564435 := by
  unfold tailWord_237016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322341854669492977601451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5763122472892657303468601 4322341854669492977601451)
  ·
    refine ⟨6483512782004239466402177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4322341854669492977601451 6483512782004239466402177)
    ·
      refine ⟨4862634586503179599801633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6483512782004239466402177 4862634586503179599801633)
      ·
        refine ⟨3646975939877384699851225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4862634586503179599801633 3646975939877384699851225)
        ·
          refine ⟨2735231954908038524888419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3646975939877384699851225 2735231954908038524888419)
          ·
            refine ⟨4102847932362057787332629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735231954908038524888419 4102847932362057787332629)
            ·
              refine ⟨192320996829471458781217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4102847932362057787332629 192320996829471458781217)
              ·
                refine ⟨144240747622103594085913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192320996829471458781217 144240747622103594085913)
                ·
                  refine ⟨108180560716577695564435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144240747622103594085913 108180560716577695564435)
                  ·
                    rfl

theorem cell20_237016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_237016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237016 prefixEnd_237016 := by exact prefixLift 237016
  have htrace : WordTrace (prefixWord ++ tailWord_237016) baseStart_237016 baseEnd_237016 := by
    simpa [prefixWord, tailWord_237016, baseEnd_237016] using wordTrace_append hprefix tailTrace_237016
  have hstable : (prefixWord ++ tailWord_237016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237016).length < 2 ^ (prefixWord ++ tailWord_237016).sum := by decide
  have hdescent : baseEnd_237016 < baseStart_237016 := by decide
  rcases family_descends (prefixWord ++ tailWord_237016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237075 : List Nat := [1, 1, 1, 2, 1, 6, 2, 4, 2]
def baseStart_237075 : Nat := 118140960795 + 237075 * 2 ^ 59
def prefixEnd_237075 : Nat := 4983230072969 + 3 ^ 40 * 237075 * 2
def baseEnd_237075 : Nat := 108207489924235712597527

theorem tailTrace_237075 : CollatzResearch.WordTrace tailWord_237075 prefixEnd_237075 108207489924235712597527 := by
  unfold tailWord_237075
  simp only [CollatzResearch.WordTrace]
  refine ⟨8646835616125239031600679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5764557077416826021067119 8646835616125239031600679)
  ·
    refine ⟨12970253424187858547401019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8646835616125239031600679 12970253424187858547401019)
    ·
      refine ⟨19455380136281787821101529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12970253424187858547401019 19455380136281787821101529)
      ·
        refine ⟨14591535102211340865826147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19455380136281787821101529 14591535102211340865826147)
        ·
          refine ⟨21887302653317011298739221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14591535102211340865826147 21887302653317011298739221)
          ·
            refine ⟨1025967311874234904628401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21887302653317011298739221 1025967311874234904628401)
            ·
              refine ⟨769475483905676178471301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025967311874234904628401 769475483905676178471301)
              ·
                refine ⟨144276653232314283463369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769475483905676178471301 144276653232314283463369)
                ·
                  refine ⟨108207489924235712597527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144276653232314283463369 108207489924235712597527)
                  ·
                    rfl

theorem cell20_237075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 2].length) (baseStart_237075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237075 prefixEnd_237075 := by exact prefixLift 237075
  have htrace : WordTrace (prefixWord ++ tailWord_237075) baseStart_237075 baseEnd_237075 := by
    simpa [prefixWord, tailWord_237075, baseEnd_237075] using wordTrace_append hprefix tailTrace_237075
  have hstable : (prefixWord ++ tailWord_237075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237075).length < 2 ^ (prefixWord ++ tailWord_237075).sum := by decide
  have hdescent : baseEnd_237075 < baseStart_237075 := by decide
  rcases family_descends (prefixWord ++ tailWord_237075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237126 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_237126 : Nat := 118140960795 + 237126 * 2 ^ 59
def prefixEnd_237126 : Nat := 4983230072969 + 3 ^ 40 * 237126 * 2
def baseEnd_237126 : Nat := 108230767713906201897319

theorem tailTrace_237126 : CollatzResearch.WordTrace tailWord_237126 prefixEnd_237126 108230767713906201897319 := by
  unfold tailWord_237126
  simp only [CollatzResearch.WordTrace]
  refine ⟨270271741841889835678351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5765797159293649827804821 270271741841889835678351)
  ·
    refine ⟨405407612762834753517527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270271741841889835678351 405407612762834753517527)
    ·
      refine ⟨608111419144252130276291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405407612762834753517527 608111419144252130276291)
      ·
        refine ⟨912167128716378195414437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608111419144252130276291 912167128716378195414437)
        ·
          refine ⟨171031336634320911640207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 912167128716378195414437 171031336634320911640207)
          ·
            refine ⟨256547004951481367460311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171031336634320911640207 256547004951481367460311)
            ·
              refine ⟨384820507427222051190467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256547004951481367460311 384820507427222051190467)
              ·
                refine ⟨577230761140833076785701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384820507427222051190467 577230761140833076785701)
                ·
                  refine ⟨108230767713906201897319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577230761140833076785701 108230767713906201897319)
                  ·
                    rfl

theorem cell20_237126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_237126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237126 prefixEnd_237126 := by exact prefixLift 237126
  have htrace : WordTrace (prefixWord ++ tailWord_237126) baseStart_237126 baseEnd_237126 := by
    simpa [prefixWord, tailWord_237126, baseEnd_237126] using wordTrace_append hprefix tailTrace_237126
  have hstable : (prefixWord ++ tailWord_237126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237126).length < 2 ^ (prefixWord ++ tailWord_237126).sum := by decide
  have hdescent : baseEnd_237126 < baseStart_237126 := by decide
  rcases family_descends (prefixWord ++ tailWord_237126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237130 : List Nat := [3, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_237130 : Nat := 118140960795 + 237130 * 2 ^ 59
def prefixEnd_237130 : Nat := 4983230072969 + 3 ^ 40 * 237130 * 2
def baseEnd_237130 : Nat := 108232593422899965763969

theorem tailTrace_237130 : CollatzResearch.WordTrace tailWord_237130 prefixEnd_237130 108232593422899965763969 := by
  unfold tailWord_237130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162210407731495856213211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5765894420617322283235229 2162210407731495856213211)
  ·
    refine ⟨3243315611597243784319817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2162210407731495856213211 3243315611597243784319817)
    ·
      refine ⟨2432486708697932838239863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3243315611597243784319817 2432486708697932838239863)
      ·
        refine ⟨3648730063046899257359795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432486708697932838239863 3648730063046899257359795)
        ·
          refine ⟨5473095094570348886039693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648730063046899257359795 5473095094570348886039693)
          ·
            refine ⟨2052410660463880832264885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5473095094570348886039693 2052410660463880832264885)
            ·
              refine ⟨192413499418488828024833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2052410660463880832264885 192413499418488828024833)
              ·
                refine ⟨144310124563866621018625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192413499418488828024833 144310124563866621018625)
                ·
                  refine ⟨108232593422899965763969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144310124563866621018625 108232593422899965763969)
                  ·
                    rfl

theorem cell20_237130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_237130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237130 prefixEnd_237130 := by exact prefixLift 237130
  have htrace : WordTrace (prefixWord ++ tailWord_237130) baseStart_237130 baseEnd_237130 := by
    simpa [prefixWord, tailWord_237130, baseEnd_237130] using wordTrace_append hprefix tailTrace_237130
  have hstable : (prefixWord ++ tailWord_237130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237130).length < 2 ^ (prefixWord ++ tailWord_237130).sum := by decide
  have hdescent : baseEnd_237130 < baseStart_237130 := by decide
  rcases family_descends (prefixWord ++ tailWord_237130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237185 : List Nat := [1, 2, 4, 2, 1, 4, 2, 2, 2]
def baseStart_237185 : Nat := 118140960795 + 237185 * 2 ^ 59
def prefixEnd_237185 : Nat := 4983230072969 + 3 ^ 40 * 237185 * 2
def baseEnd_237185 : Nat := 108257696921564218930411

theorem tailTrace_237185 : CollatzResearch.WordTrace tailWord_237185 prefixEnd_237185 108257696921564218930411 := by
  unfold tailWord_237185
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650847645726727818105009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5767231763817818545403339 8650847645726727818105009)
  ·
    refine ⟨6488135734295045863578757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8650847645726727818105009 6488135734295045863578757)
    ·
      refine ⟨1216525450180321099421017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6488135734295045863578757 1216525450180321099421017)
      ·
        refine ⟨912394087635240824565763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1216525450180321099421017 912394087635240824565763)
        ·
          refine ⟨1368591131452861236848645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912394087635240824565763 1368591131452861236848645)
          ·
            refine ⟨256610837147411481909121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1368591131452861236848645 256610837147411481909121)
            ·
              refine ⟨192458127860558611431841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256610837147411481909121 192458127860558611431841)
              ·
                refine ⟨144343595895418958573881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192458127860558611431841 144343595895418958573881)
                ·
                  refine ⟨108257696921564218930411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144343595895418958573881 108257696921564218930411)
                  ·
                    rfl

theorem cell20_237185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_237185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237185 prefixEnd_237185 := by exact prefixLift 237185
  have htrace : WordTrace (prefixWord ++ tailWord_237185) baseStart_237185 baseEnd_237185 := by
    simpa [prefixWord, tailWord_237185, baseEnd_237185] using wordTrace_append hprefix tailTrace_237185
  have hstable : (prefixWord ++ tailWord_237185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237185).length < 2 ^ (prefixWord ++ tailWord_237185).sum := by decide
  have hdescent : baseEnd_237185 < baseStart_237185 := by decide
  rcases family_descends (prefixWord ++ tailWord_237185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237189 : List Nat := [1, 3, 1, 1, 4, 1, 3, 4, 2]
def baseStart_237189 : Nat := 118140960795 + 237189 * 2 ^ 59
def prefixEnd_237189 : Nat := 4983230072969 + 3 ^ 40 * 237189 * 2
def baseEnd_237189 : Nat := 108259522630557982797061

theorem tailTrace_237189 : CollatzResearch.WordTrace tailWord_237189 prefixEnd_237189 108259522630557982797061 := by
  unfold tailWord_237189
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650993537712236501250621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5767329025141491000833747 8650993537712236501250621)
  ·
    refine ⟨3244122576642088687968983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8650993537712236501250621 3244122576642088687968983)
    ·
      refine ⟨4866183864963133031953475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244122576642088687968983 4866183864963133031953475)
      ·
        refine ⟨7299275797444699547930213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866183864963133031953475 7299275797444699547930213)
        ·
          refine ⟨1368614212020881165236915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7299275797444699547930213 1368614212020881165236915)
          ·
            refine ⟨2052921318031321747855373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368614212020881165236915 2052921318031321747855373)
            ·
              refine ⟨769845494261745655445765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2052921318031321747855373 769845494261745655445765)
              ·
                refine ⟨144346030174077310396081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769845494261745655445765 144346030174077310396081)
                ·
                  refine ⟨108259522630557982797061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144346030174077310396081 108259522630557982797061)
                  ·
                    rfl

theorem cell20_237189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_237189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237189 prefixEnd_237189 := by exact prefixLift 237189
  have htrace : WordTrace (prefixWord ++ tailWord_237189) baseStart_237189 baseEnd_237189 := by
    simpa [prefixWord, tailWord_237189, baseEnd_237189] using wordTrace_append hprefix tailTrace_237189
  have hstable : (prefixWord ++ tailWord_237189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237189).length < 2 ^ (prefixWord ++ tailWord_237189).sum := by decide
  have hdescent : baseEnd_237189 < baseStart_237189 := by decide
  rcases family_descends (prefixWord ++ tailWord_237189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237192 : List Nat := [2, 1, 3, 5, 2, 1, 1, 5]
def baseStart_237192 : Nat := 118140960795 + 237192 * 2 ^ 59
def prefixEnd_237192 : Nat := 4983230072969 + 3 ^ 40 * 237192 * 2
def baseEnd_237192 : Nat := 36086963970767768565683

theorem tailTrace_237192 : CollatzResearch.WordTrace tailWord_237192 prefixEnd_237192 36086963970767768565683 := by
  unfold tailWord_237192
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325551478350684006804915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5767401971134245342406553 4325551478350684006804915)
  ·
    refine ⟨6488327217526026010207373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4325551478350684006804915 6488327217526026010207373)
    ·
      refine ⟨2433122706572259753827765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6488327217526026010207373 2433122706572259753827765)
      ·
        refine ⟨228105253741149351921353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2433122706572259753827765 228105253741149351921353)
        ·
          refine ⟨171078940305862013941015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228105253741149351921353 171078940305862013941015)
          ·
            refine ⟨256618410458793020911523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171078940305862013941015 256618410458793020911523)
            ·
              refine ⟨384927615688189531367285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256618410458793020911523 384927615688189531367285)
              ·
                refine ⟨36086963970767768565683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 384927615688189531367285 36086963970767768565683)
                ·
                  rfl

theorem cell20_237192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_237192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237192 prefixEnd_237192 := by exact prefixLift 237192
  have htrace : WordTrace (prefixWord ++ tailWord_237192) baseStart_237192 baseEnd_237192 := by
    simpa [prefixWord, tailWord_237192, baseEnd_237192] using wordTrace_append hprefix tailTrace_237192
  have hstable : (prefixWord ++ tailWord_237192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237192).length < 2 ^ (prefixWord ++ tailWord_237192).sum := by decide
  have hdescent : baseEnd_237192 < baseStart_237192 := by decide
  rcases family_descends (prefixWord ++ tailWord_237192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237231 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_237231 : Nat := 118140960795 + 237231 * 2 ^ 59
def prefixEnd_237231 : Nat := 4983230072969 + 3 ^ 40 * 237231 * 2
def baseEnd_237231 : Nat := 108278692574992503396889

theorem tailTrace_237231 : CollatzResearch.WordTrace tailWord_237231 prefixEnd_237231 108278692574992503396889 := by
  unfold tailWord_237231
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652525403560077674279547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5768350269040051782853031 8652525403560077674279547)
  ·
    refine ⟨12978788105340116511419321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8652525403560077674279547 12978788105340116511419321)
    ·
      refine ⟨9734091079005087383564491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12978788105340116511419321 9734091079005087383564491)
      ·
        refine ⟨14601136618507631075346737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9734091079005087383564491 14601136618507631075346737)
        ·
          refine ⟨10950852463880723306510053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14601136618507631075346737 10950852463880723306510053)
          ·
            refine ⟨2053284836977635619970635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10950852463880723306510053 2053284836977635619970635)
            ·
              refine ⟨3079927255466453429955953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053284836977635619970635 3079927255466453429955953)
              ·
                refine ⟨2309945441599840072466965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079927255466453429955953 2309945441599840072466965)
                ·
                  refine ⟨108278692574992503396889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2309945441599840072466965 108278692574992503396889)
                  ·
                    rfl

theorem cell20_237231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_237231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237231 prefixEnd_237231 := by exact prefixLift 237231
  have htrace : WordTrace (prefixWord ++ tailWord_237231) baseStart_237231 baseEnd_237231 := by
    simpa [prefixWord, tailWord_237231, baseEnd_237231] using wordTrace_append hprefix tailTrace_237231
  have hstable : (prefixWord ++ tailWord_237231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237231).length < 2 ^ (prefixWord ++ tailWord_237231).sum := by decide
  have hdescent : baseEnd_237231 < baseStart_237231 := by decide
  rcases family_descends (prefixWord ++ tailWord_237231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237237 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 3]
def baseStart_237237 : Nat := 118140960795 + 237237 * 2 ^ 59
def prefixEnd_237237 : Nat := 4983230072969 + 3 ^ 40 * 237237 * 2
def baseEnd_237237 : Nat := 108281431138483149196865

theorem tailTrace_237237 : CollatzResearch.WordTrace tailWord_237237 prefixEnd_237237 108281431138483149196865 := by
  unfold tailWord_237237
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652744241538340698997965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5768496161025560465998643 8652744241538340698997965)
  ·
    refine ⟨3244779090576877762124237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8652744241538340698997965 3244779090576877762124237)
    ·
      refine ⟨1216792158966329160796589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3244779090576877762124237 1216792158966329160796589)
      ·
        refine ⟨456297059612373435298721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1216792158966329160796589 456297059612373435298721)
        ·
          refine ⟨342222794709280076474041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456297059612373435298721 342222794709280076474041)
          ·
            refine ⟨256667096031960057355531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342222794709280076474041 256667096031960057355531)
            ·
              refine ⟨385000644047940086033297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256667096031960057355531 385000644047940086033297)
              ·
                refine ⟨288750483035955064524973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385000644047940086033297 288750483035955064524973)
                ·
                  refine ⟨108281431138483149196865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288750483035955064524973 108281431138483149196865)
                  ·
                    rfl

theorem cell20_237237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_237237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237237 prefixEnd_237237 := by exact prefixLift 237237
  have htrace : WordTrace (prefixWord ++ tailWord_237237) baseStart_237237 baseEnd_237237 := by
    simpa [prefixWord, tailWord_237237, baseEnd_237237] using wordTrace_append hprefix tailTrace_237237
  have hstable : (prefixWord ++ tailWord_237237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237237).length < 2 ^ (prefixWord ++ tailWord_237237).sum := by decide
  have hdescent : baseEnd_237237 < baseStart_237237 := by decide
  rcases family_descends (prefixWord ++ tailWord_237237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237241 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 3]
def baseStart_237241 : Nat := 118140960795 + 237241 * 2 ^ 59
def prefixEnd_237241 : Nat := 4983230072969 + 3 ^ 40 * 237241 * 2
def baseEnd_237241 : Nat := 108283256847476913063515

theorem tailTrace_237241 : CollatzResearch.WordTrace tailWord_237241 prefixEnd_237241 108283256847476913063515 := by
  unfold tailWord_237241
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652890133523849382143577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5768593422349232921429051 8652890133523849382143577)
  ·
    refine ⟨6489667600142887036607683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8652890133523849382143577 6489667600142887036607683)
    ·
      refine ⟨9734501400214330554911525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6489667600142887036607683 9734501400214330554911525)
      ·
        refine ⟨1825219012540186979045911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9734501400214330554911525 1825219012540186979045911)
        ·
          refine ⟨2737828518810280468568867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825219012540186979045911 2737828518810280468568867)
          ·
            refine ⟨4106742778215420702853301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737828518810280468568867 4106742778215420702853301)
            ·
              refine ⟨385007135457695690892497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4106742778215420702853301 385007135457695690892497)
              ·
                refine ⟨288755351593271768169373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385007135457695690892497 288755351593271768169373)
                ·
                  refine ⟨108283256847476913063515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288755351593271768169373 108283256847476913063515)
                  ·
                    rfl

theorem cell20_237241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_237241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237241 prefixEnd_237241 := by exact prefixLift 237241
  have htrace : WordTrace (prefixWord ++ tailWord_237241) baseStart_237241 baseEnd_237241 := by
    simpa [prefixWord, tailWord_237241, baseEnd_237241] using wordTrace_append hprefix tailTrace_237241
  have hstable : (prefixWord ++ tailWord_237241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237241).length < 2 ^ (prefixWord ++ tailWord_237241).sum := by decide
  have hdescent : baseEnd_237241 < baseStart_237241 := by decide
  rcases family_descends (prefixWord ++ tailWord_237241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237248 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_237248 : Nat := 118140960795 + 237248 * 2 ^ 59
def prefixEnd_237248 : Nat := 4983230072969 + 3 ^ 40 * 237248 * 2
def baseEnd_237248 : Nat := 108286451838215999830153

theorem tailTrace_237248 : CollatzResearch.WordTrace tailWord_237248 prefixEnd_237248 108286451838215999830153 := by
  unfold tailWord_237248
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326572722249244788824199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5768763629665659718432265 4326572722249244788824199)
  ·
    refine ⟨6489859083373867183236299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4326572722249244788824199 6489859083373867183236299)
    ·
      refine ⟨9734788625060800774854449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6489859083373867183236299 9734788625060800774854449)
      ·
        refine ⟨7301091468795600581140837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9734788625060800774854449 7301091468795600581140837)
        ·
          refine ⟨1368954650399175108963907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7301091468795600581140837 1368954650399175108963907)
          ·
            refine ⟨2053431975598762663445861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368954650399175108963907 2053431975598762663445861)
            ·
              refine ⟨385018495424767999396099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2053431975598762663445861 385018495424767999396099)
              ·
                refine ⟨577527743137151999094149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385018495424767999396099 577527743137151999094149)
                ·
                  refine ⟨108286451838215999830153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577527743137151999094149 108286451838215999830153)
                  ·
                    rfl

theorem cell20_237248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_237248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237248 prefixEnd_237248 := by exact prefixLift 237248
  have htrace : WordTrace (prefixWord ++ tailWord_237248) baseStart_237248 baseEnd_237248 := by
    simpa [prefixWord, tailWord_237248, baseEnd_237248] using wordTrace_append hprefix tailTrace_237248
  have hstable : (prefixWord ++ tailWord_237248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237248).length < 2 ^ (prefixWord ++ tailWord_237248).sum := by decide
  have hdescent : baseEnd_237248 < baseStart_237248 := by decide
  rcases family_descends (prefixWord ++ tailWord_237248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237293 : List Nat := [1, 5, 1, 2, 1, 2, 8]
def baseStart_237293 : Nat := 118140960795 + 237293 * 2 ^ 59
def prefixEnd_237293 : Nat := 4983230072969 + 3 ^ 40 * 237293 * 2
def baseEnd_237293 : Nat := 12034110118266204814441

theorem tailTrace_237293 : CollatzResearch.WordTrace tailWord_237293 prefixEnd_237293 12034110118266204814441 := by
  unfold tailWord_237293
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654786729335462263036533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5769857819556974842024355 8654786729335462263036533)
  ·
    refine ⟨811386255875199587159675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8654786729335462263036533 811386255875199587159675)
    ·
      refine ⟨1217079383812799380739513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811386255875199587159675 1217079383812799380739513)
      ·
        refine ⟨912809537859599535554635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1217079383812799380739513 912809537859599535554635)
        ·
          refine ⟨1369214306789399303331953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912809537859599535554635 1369214306789399303331953)
          ·
            refine ⟨1026910730092049477498965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369214306789399303331953 1026910730092049477498965)
            ·
              refine ⟨12034110118266204814441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1026910730092049477498965 12034110118266204814441)
              ·
                rfl

theorem cell20_237293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 8].length) (baseStart_237293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237293 prefixEnd_237293 := by exact prefixLift 237293
  have htrace : WordTrace (prefixWord ++ tailWord_237293) baseStart_237293 baseEnd_237293 := by
    simpa [prefixWord, tailWord_237293, baseEnd_237293] using wordTrace_append hprefix tailTrace_237293
  have hstable : (prefixWord ++ tailWord_237293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237293).length < 2 ^ (prefixWord ++ tailWord_237293).sum := by decide
  have hdescent : baseEnd_237293 < baseStart_237293 := by decide
  rcases family_descends (prefixWord ++ tailWord_237293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237307 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_237307 : Nat := 118140960795 + 237307 * 2 ^ 59
def prefixEnd_237307 : Nat := 4983230072969 + 3 ^ 40 * 237307 * 2
def baseEnd_237307 : Nat := 108313381045874016863245

theorem tailTrace_237307 : CollatzResearch.WordTrace tailWord_237307 prefixEnd_237307 108313381045874016863245 := by
  unfold tailWord_237307
  simp only [CollatzResearch.WordTrace]
  refine ⟨8655297351284742654046175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5770198234189828436030783 8655297351284742654046175)
  ·
    refine ⟨12982946026927113981069263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8655297351284742654046175 12982946026927113981069263)
    ·
      refine ⟨19474419040390670971603895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12982946026927113981069263 19474419040390670971603895)
      ·
        refine ⟨29211628560586006457405843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19474419040390670971603895 29211628560586006457405843)
        ·
          refine ⟨43817442840879009686108765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29211628560586006457405843 43817442840879009686108765)
          ·
            refine ⟨16431541065329628632290787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43817442840879009686108765 16431541065329628632290787)
            ·
              refine ⟨24647311597994442948436181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16431541065329628632290787 24647311597994442948436181)
              ·
                refine ⟨577671365577994756603973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24647311597994442948436181 577671365577994756603973)
                ·
                  refine ⟨108313381045874016863245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577671365577994756603973 108313381045874016863245)
                  ·
                    rfl

theorem cell20_237307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_237307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_237307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_237307 prefixEnd_237307 := by exact prefixLift 237307
  have htrace : WordTrace (prefixWord ++ tailWord_237307) baseStart_237307 baseEnd_237307 := by
    simpa [prefixWord, tailWord_237307, baseEnd_237307] using wordTrace_append hprefix tailTrace_237307
  have hstable : (prefixWord ++ tailWord_237307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237307).length < 2 ^ (prefixWord ++ tailWord_237307).sum := by decide
  have hdescent : baseEnd_237307 < baseStart_237307 := by decide
  rcases family_descends (prefixWord ++ tailWord_237307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
