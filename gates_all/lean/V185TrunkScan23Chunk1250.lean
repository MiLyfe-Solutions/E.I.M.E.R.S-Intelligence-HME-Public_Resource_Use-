import V185TrunkScan23Chunk1249

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7404042 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_7404042 : Nat := 118140960795 + 7404042 * 2 ^ 59
def prefixEnd_7404042 : Nat := 4983230072969 + 3 ^ 40 * 7404042 * 2
def baseEnd_7404042 : Nat := 3801832332076625885324437

theorem tailTrace_7404042 : CollatzResearch.WordTrace tailWord_7404042 prefixEnd_7404042 3801832332076625885324437 := by
  unfold tailWord_7404042
  simp only [CollatzResearch.WordTrace]
  refine ⟨67511899260606954636487595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180031731361618545697300253 67511899260606954636487595)
  ·
    refine ⟨101267848890910431954731393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67511899260606954636487595 101267848890910431954731393)
    ·
      refine ⟨75950886668182823966048545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101267848890910431954731393 75950886668182823966048545)
      ·
        refine ⟨56963165001137117974536409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75950886668182823966048545 56963165001137117974536409)
        ·
          refine ⟨42722373750852838480902307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56963165001137117974536409 42722373750852838480902307)
          ·
            refine ⟨64083560626279257721353461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42722373750852838480902307 64083560626279257721353461)
            ·
              refine ⟨6007833808713680411376887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64083560626279257721353461 6007833808713680411376887)
              ·
                refine ⟨9011750713070520617065331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007833808713680411376887 9011750713070520617065331)
                ·
                  refine ⟨13517626069605780925597997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9011750713070520617065331 13517626069605780925597997)
                  ·
                    refine ⟨5069109776102167847099249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13517626069605780925597997 5069109776102167847099249)
                    ·
                      refine ⟨3801832332076625885324437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069109776102167847099249 3801832332076625885324437)
                      ·
                        rfl

theorem cell23_7404042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_7404042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404042 prefixEnd_7404042 := by exact prefixLift 7404042
  have htrace : WordTrace (prefixWord ++ tailWord_7404042) baseStart_7404042 baseEnd_7404042 := by
    simpa [prefixWord, tailWord_7404042, baseEnd_7404042] using wordTrace_append hprefix tailTrace_7404042
  have hstable : (prefixWord ++ tailWord_7404042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404042).length < 2 ^ (prefixWord ++ tailWord_7404042).sum := by decide
  have hdescent : baseEnd_7404042 < baseStart_7404042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404051 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 4]
def baseStart_7404051 : Nat := 118140960795 + 7404051 * 2 ^ 59
def prefixEnd_7404051 : Nat := 4983230072969 + 3 ^ 40 * 7404051 * 2
def baseEnd_7404051 : Nat := 3801836953402516350111895

theorem tailTrace_7404051 : CollatzResearch.WordTrace tailWord_7404051 prefixEnd_7404051 3801836953402516350111895 := by
  unfold tailWord_7404051
  simp only [CollatzResearch.WordTrace]
  refine ⟨270047925299395213083028007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180031950199596808722018671 270047925299395213083028007)
  ·
    refine ⟨405071887949092819624542011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270047925299395213083028007 405071887949092819624542011)
    ·
      refine ⟨607607831923639229436813017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405071887949092819624542011 607607831923639229436813017)
      ·
        refine ⟨455705873942729422077609763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607607831923639229436813017 455705873942729422077609763)
        ·
          refine ⟨683558810914094133116414645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455705873942729422077609763 683558810914094133116414645)
          ·
            refine ⟨64083638523196324979663873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 683558810914094133116414645 64083638523196324979663873)
            ·
              refine ⟨48062728892397243734747905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64083638523196324979663873 48062728892397243734747905)
              ·
                refine ⟨36047046669297932801060929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48062728892397243734747905 36047046669297932801060929)
                ·
                  refine ⟨27035285001973449600795697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36047046669297932801060929 27035285001973449600795697)
                  ·
                    refine ⟨20276463751480087200596773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27035285001973449600795697 20276463751480087200596773)
                    ·
                      refine ⟨3801836953402516350111895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20276463751480087200596773 3801836953402516350111895)
                      ·
                        rfl

theorem cell23_7404051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_7404051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404051 prefixEnd_7404051 := by exact prefixLift 7404051
  have htrace : WordTrace (prefixWord ++ tailWord_7404051) baseStart_7404051 baseEnd_7404051 := by
    simpa [prefixWord, tailWord_7404051, baseEnd_7404051] using wordTrace_append hprefix tailTrace_7404051
  have hstable : (prefixWord ++ tailWord_7404051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404051).length < 2 ^ (prefixWord ++ tailWord_7404051).sum := by decide
  have hdescent : baseEnd_7404051 < baseStart_7404051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404072 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7404072 : Nat := 118140960795 + 7404072 * 2 ^ 59
def prefixEnd_7404072 : Nat := 4983230072969 + 3 ^ 40 * 7404072 * 2
def baseEnd_7404072 : Nat := 3801847736496260767949299

theorem tailTrace_7404072 : CollatzResearch.WordTrace tailWord_7404072 prefixEnd_7404072 3801847736496260767949299 := by
  unfold tailWord_7404072
  simp only [CollatzResearch.WordTrace]
  refine ⟨135024345616159566834771235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180032460821546089113028313 135024345616159566834771235)
  ·
    refine ⟨202536518424239350252156853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135024345616159566834771235 202536518424239350252156853)
    ·
      refine ⟨18987798602272439086139705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202536518424239350252156853 18987798602272439086139705)
      ·
        refine ⟨14240848951704329314604779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18987798602272439086139705 14240848951704329314604779)
        ·
          refine ⟨21361273427556493971907169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240848951704329314604779 21361273427556493971907169)
          ·
            refine ⟨16020955070667370478930377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21361273427556493971907169 16020955070667370478930377)
            ·
              refine ⟨12015716303000527859197783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16020955070667370478930377 12015716303000527859197783)
              ·
                refine ⟨18023574454500791788796675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12015716303000527859197783 18023574454500791788796675)
                ·
                  refine ⟨27035361681751187683195013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18023574454500791788796675 27035361681751187683195013)
                  ·
                    refine ⟨5069130315328347690599065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27035361681751187683195013 5069130315328347690599065)
                    ·
                      refine ⟨3801847736496260767949299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069130315328347690599065 3801847736496260767949299)
                      ·
                        rfl

theorem cell23_7404072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7404072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404072 prefixEnd_7404072 := by exact prefixLift 7404072
  have htrace : WordTrace (prefixWord ++ tailWord_7404072) baseStart_7404072 baseEnd_7404072 := by
    simpa [prefixWord, tailWord_7404072, baseEnd_7404072] using wordTrace_append hprefix tailTrace_7404072
  have hstable : (prefixWord ++ tailWord_7404072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404072).length < 2 ^ (prefixWord ++ tailWord_7404072).sum := by decide
  have hdescent : baseEnd_7404072 < baseStart_7404072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404151 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 8]
def baseStart_7404151 : Nat := 118140960795 + 7404151 * 2 ^ 59
def prefixEnd_7404151 : Nat := 4983230072969 + 3 ^ 40 * 7404151 * 2
def baseEnd_7404151 : Nat := 422432033496440662095715

theorem tailTrace_7404151 : CollatzResearch.WordTrace tailWord_7404151 prefixEnd_7404151 422432033496440662095715 := by
  unfold tailWord_7404151
  simp only [CollatzResearch.WordTrace]
  refine ⟨270051572599032930161668307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180034381732688620107778871 270051572599032930161668307)
  ·
    refine ⟨405077358898549395242502461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270051572599032930161668307 405077358898549395242502461)
    ·
      refine ⟨151904009586956023215938423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405077358898549395242502461 151904009586956023215938423)
      ·
        refine ⟨227856014380434034823907635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151904009586956023215938423 227856014380434034823907635)
        ·
          refine ⟨341784021570651052235861453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227856014380434034823907635 341784021570651052235861453)
          ·
            refine ⟨128169008088994144588448045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341784021570651052235861453 128169008088994144588448045)
            ·
              refine ⟨48063378033372804220668017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128169008088994144588448045 48063378033372804220668017)
              ·
                refine ⟨36047533525029603165501013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48063378033372804220668017 36047533525029603165501013)
                ·
                  refine ⟨422432033496440662095715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36047533525029603165501013 422432033496440662095715)
                  ·
                    rfl

theorem cell23_7404151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 8].length) (baseStart_7404151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404151 prefixEnd_7404151 := by exact prefixLift 7404151
  have htrace : WordTrace (prefixWord ++ tailWord_7404151) baseStart_7404151 baseEnd_7404151 := by
    simpa [prefixWord, tailWord_7404151, baseEnd_7404151] using wordTrace_append hprefix tailTrace_7404151
  have hstable : (prefixWord ++ tailWord_7404151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404151).length < 2 ^ (prefixWord ++ tailWord_7404151).sum := by decide
  have hdescent : baseEnd_7404151 < baseStart_7404151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404155 : List Nat := [1, 1, 1, 1, 1, 4, 2, 7, 1, 4]
def baseStart_7404155 : Nat := 118140960795 + 7404155 * 2 ^ 59
def prefixEnd_7404155 : Nat := 4983230072969 + 3 ^ 40 * 7404155 * 2
def baseEnd_7404155 : Nat := 1267296785130194647737139

theorem tailTrace_7404155 : CollatzResearch.WordTrace tailWord_7404155 prefixEnd_7404155 1267296785130194647737139 := by
  unfold tailWord_7404155
  simp only [CollatzResearch.WordTrace]
  refine ⟨270051718491018438844813919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180034478994012292563209279 270051718491018438844813919)
  ·
    refine ⟨405077577736527658267220879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270051718491018438844813919 405077577736527658267220879)
    ·
      refine ⟨607616366604791487400831319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405077577736527658267220879 607616366604791487400831319)
      ·
        refine ⟨911424549907187231101246979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607616366604791487400831319 911424549907187231101246979)
        ·
          refine ⟨1367136824860780846651870469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911424549907187231101246979 1367136824860780846651870469)
          ·
            refine ⟨256338154661396408747225713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1367136824860780846651870469 256338154661396408747225713)
            ·
              refine ⟨192253615996047306560419285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256338154661396408747225713 192253615996047306560419285)
              ·
                refine ⟨4505944124907358747509827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192253615996047306560419285 4505944124907358747509827)
                ·
                  refine ⟨6758916187361038121264741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505944124907358747509827 6758916187361038121264741)
                  ·
                    refine ⟨1267296785130194647737139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758916187361038121264741 1267296785130194647737139)
                    ·
                      rfl

theorem cell23_7404155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 4].length) (baseStart_7404155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404155 prefixEnd_7404155 := by exact prefixLift 7404155
  have htrace : WordTrace (prefixWord ++ tailWord_7404155) baseStart_7404155 baseEnd_7404155 := by
    simpa [prefixWord, tailWord_7404155, baseEnd_7404155] using wordTrace_append hprefix tailTrace_7404155
  have hstable : (prefixWord ++ tailWord_7404155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404155).length < 2 ^ (prefixWord ++ tailWord_7404155).sum := by decide
  have hdescent : baseEnd_7404155 < baseStart_7404155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404165 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_7404165 : Nat := 118140960795 + 7404165 * 2 ^ 59
def prefixEnd_7404165 : Nat := 4983230072969 + 3 ^ 40 * 7404165 * 2
def baseEnd_7404165 : Nat := 3801895490197128904086371

theorem tailTrace_7404165 : CollatzResearch.WordTrace tailWord_7404165 prefixEnd_7404165 3801895490197128904086371 := by
  unfold tailWord_7404165
  simp only [CollatzResearch.WordTrace]
  refine ⟨270052083220982210552677949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180034722147321473701785299 270052083220982210552677949)
  ·
    refine ⟨101269531207868328957254231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270052083220982210552677949 101269531207868328957254231)
    ·
      refine ⟨151904296811802493435881347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101269531207868328957254231 151904296811802493435881347)
      ·
        refine ⟨227856445217703740153822021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151904296811802493435881347 227856445217703740153822021)
        ·
          refine ⟨42723083478319451278841629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227856445217703740153822021 42723083478319451278841629)
          ·
            refine ⟨16021156304369794229565611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42723083478319451278841629 16021156304369794229565611)
            ·
              refine ⟨24031734456554691344348417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16021156304369794229565611 24031734456554691344348417)
              ·
                refine ⟨18023800842416018508261313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24031734456554691344348417 18023800842416018508261313)
                ·
                  refine ⟨13517850631812013881195985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18023800842416018508261313 13517850631812013881195985)
                  ·
                    refine ⟨10138387973859010410896989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13517850631812013881195985 10138387973859010410896989)
                    ·
                      refine ⟨3801895490197128904086371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10138387973859010410896989 3801895490197128904086371)
                      ·
                        rfl

theorem cell23_7404165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_7404165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404165 prefixEnd_7404165 := by exact prefixLift 7404165
  have htrace : WordTrace (prefixWord ++ tailWord_7404165) baseStart_7404165 baseEnd_7404165 := by
    simpa [prefixWord, tailWord_7404165, baseEnd_7404165] using wordTrace_append hprefix tailTrace_7404165
  have hstable : (prefixWord ++ tailWord_7404165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404165).length < 2 ^ (prefixWord ++ tailWord_7404165).sum := by decide
  have hdescent : baseEnd_7404165 < baseStart_7404165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404171 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 6]
def baseStart_7404171 : Nat := 118140960795 + 7404171 * 2 ^ 59
def prefixEnd_7404171 : Nat := 4983230072969 + 3 ^ 40 * 7404171 * 2
def baseEnd_7404171 : Nat := 3801898571081055880611343

theorem tailTrace_7404171 : CollatzResearch.WordTrace tailWord_7404171 prefixEnd_7404171 3801898571081055880611343 := by
  unfold tailWord_7404171
  simp only [CollatzResearch.WordTrace]
  refine ⟨270052302058960473577396367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180034868039306982384930911 270052302058960473577396367)
  ·
    refine ⟨405078453088440710366094551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270052302058960473577396367 405078453088440710366094551)
    ·
      refine ⟨607617679632661065549141827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405078453088440710366094551 607617679632661065549141827)
      ·
        refine ⟨911426519448991598323712741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607617679632661065549141827 911426519448991598323712741)
        ·
          refine ⟨170892472396685924685696139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 911426519448991598323712741 170892472396685924685696139)
          ·
            refine ⟨256338708595028887028544209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170892472396685924685696139 256338708595028887028544209)
            ·
              refine ⟨192254031446271665271408157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256338708595028887028544209 192254031446271665271408157)
              ·
                refine ⟨72095261792351874476778059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192254031446271665271408157 72095261792351874476778059)
                ·
                  refine ⟨108142892688527811715167089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72095261792351874476778059 108142892688527811715167089)
                  ·
                    refine ⟨81107169516395858786375317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108142892688527811715167089 81107169516395858786375317)
                    ·
                      refine ⟨3801898571081055880611343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81107169516395858786375317 3801898571081055880611343)
                      ·
                        rfl

theorem cell23_7404171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_7404171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404171 prefixEnd_7404171 := by exact prefixLift 7404171
  have htrace : WordTrace (prefixWord ++ tailWord_7404171) baseStart_7404171 baseEnd_7404171 := by
    simpa [prefixWord, tailWord_7404171, baseEnd_7404171] using wordTrace_append hprefix tailTrace_7404171
  have hstable : (prefixWord ++ tailWord_7404171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404171).length < 2 ^ (prefixWord ++ tailWord_7404171).sum := by decide
  have hdescent : baseEnd_7404171 < baseStart_7404171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404181 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_7404181 : Nat := 118140960795 + 7404181 * 2 ^ 59
def prefixEnd_7404181 : Nat := 4983230072969 + 3 ^ 40 * 7404181 * 2
def baseEnd_7404181 : Nat := 1267301235295866947162099

theorem tailTrace_7404181 : CollatzResearch.WordTrace tailWord_7404181 prefixEnd_7404181 1267301235295866947162099 := by
  unfold tailWord_7404181
  simp only [CollatzResearch.WordTrace]
  refine ⟨270052666788924245285260397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180035111192616163523506931 270052666788924245285260397)
  ·
    refine ⟨101269750045846591981972649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270052666788924245285260397 101269750045846591981972649)
    ·
      refine ⟨75952312534384943986479487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101269750045846591981972649 75952312534384943986479487)
      ·
        refine ⟨113928468801577415979719231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75952312534384943986479487 113928468801577415979719231)
        ·
          refine ⟨170892703202366123969578847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113928468801577415979719231 170892703202366123969578847)
          ·
            refine ⟨256339054803549185954368271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170892703202366123969578847 256339054803549185954368271)
            ·
              refine ⟨384508582205323778931552407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256339054803549185954368271 384508582205323778931552407)
              ·
                refine ⟨576762873307985668397328611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384508582205323778931552407 576762873307985668397328611)
                ·
                  refine ⟨865144309961978502595992917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576762873307985668397328611 865144309961978502595992917)
                  ·
                    refine ⟨1267301235295866947162099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 865144309961978502595992917 1267301235295866947162099)
                    ·
                      rfl

theorem cell23_7404181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_7404181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404181 prefixEnd_7404181 := by exact prefixLift 7404181
  have htrace : WordTrace (prefixWord ++ tailWord_7404181) baseStart_7404181 baseEnd_7404181 := by
    simpa [prefixWord, tailWord_7404181, baseEnd_7404181] using wordTrace_append hprefix tailTrace_7404181
  have hstable : (prefixWord ++ tailWord_7404181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404181).length < 2 ^ (prefixWord ++ tailWord_7404181).sum := by decide
  have hdescent : baseEnd_7404181 < baseStart_7404181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404199 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7404199 : Nat := 118140960795 + 7404199 * 2 ^ 59
def prefixEnd_7404199 : Nat := 4983230072969 + 3 ^ 40 * 7404199 * 2
def baseEnd_7404199 : Nat := 3801912948539381771061215

theorem tailTrace_7404199 : CollatzResearch.WordTrace tailWord_7404199 prefixEnd_7404199 3801912948539381771061215 := by
  unfold tailWord_7404199
  simp only [CollatzResearch.WordTrace]
  refine ⟨270053323302859034359415651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180035548868572689572943767 270053323302859034359415651)
  ·
    refine ⟨405079984954288551539123477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270053323302859034359415651 405079984954288551539123477)
    ·
      refine ⟨18988124294732275853396413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405079984954288551539123477 18988124294732275853396413)
      ·
        refine ⟨7120546610524603445023655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18988124294732275853396413 7120546610524603445023655)
        ·
          refine ⟨10680819915786905167535483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7120546610524603445023655 10680819915786905167535483)
          ·
            refine ⟨16021229873680357751303225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680819915786905167535483 16021229873680357751303225)
            ·
              refine ⟨12015922405260268313477419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16021229873680357751303225 12015922405260268313477419)
              ·
                refine ⟨18023883607890402470216129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12015922405260268313477419 18023883607890402470216129)
                ·
                  refine ⟨13517912705917801852662097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18023883607890402470216129 13517912705917801852662097)
                  ·
                    refine ⟨10138434529438351389496573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13517912705917801852662097 10138434529438351389496573)
                    ·
                      refine ⟨3801912948539381771061215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10138434529438351389496573 3801912948539381771061215)
                      ·
                        rfl

theorem cell23_7404199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7404199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404199 prefixEnd_7404199 := by exact prefixLift 7404199
  have htrace : WordTrace (prefixWord ++ tailWord_7404199) baseStart_7404199 baseEnd_7404199 := by
    simpa [prefixWord, tailWord_7404199, baseEnd_7404199] using wordTrace_append hprefix tailTrace_7404199
  have hstable : (prefixWord ++ tailWord_7404199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404199).length < 2 ^ (prefixWord ++ tailWord_7404199).sum := by decide
  have hdescent : baseEnd_7404199 < baseStart_7404199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404222 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_7404222 : Nat := 118140960795 + 7404222 * 2 ^ 59
def prefixEnd_7404222 : Nat := 4983230072969 + 3 ^ 40 * 7404222 * 2
def baseEnd_7404222 : Nat := 3801924758594435181073609

theorem tailTrace_7404222 : CollatzResearch.WordTrace tailWord_7404222 prefixEnd_7404222 3801924758594435181073609 := by
  unfold tailWord_7404222
  simp only [CollatzResearch.WordTrace]
  refine ⟨33756770272721963660937865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180036108121183806191668613 33756770272721963660937865)
  ·
    refine ⟨25317577704541472745703399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33756770272721963660937865 25317577704541472745703399)
    ·
      refine ⟨37976366556812209118555099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25317577704541472745703399 37976366556812209118555099)
      ·
        refine ⟨56964549835218313677832649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37976366556812209118555099 56964549835218313677832649)
        ·
          refine ⟨42723412376413735258374487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56964549835218313677832649 42723412376413735258374487)
          ·
            refine ⟨64085118564620602887561731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42723412376413735258374487 64085118564620602887561731)
            ·
              refine ⟨96127677846930904331342597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64085118564620602887561731 96127677846930904331342597)
              ·
                refine ⟨18023939596299544562126737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96127677846930904331342597 18023939596299544562126737)
                ·
                  refine ⟨13517954697224658421595053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18023939596299544562126737 13517954697224658421595053)
                  ·
                    refine ⟨5069233011459246908098145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13517954697224658421595053 5069233011459246908098145)
                    ·
                      refine ⟨3801924758594435181073609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069233011459246908098145 3801924758594435181073609)
                      ·
                        rfl

theorem cell23_7404222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_7404222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404222 prefixEnd_7404222 := by exact prefixLift 7404222
  have htrace : WordTrace (prefixWord ++ tailWord_7404222) baseStart_7404222 baseEnd_7404222 := by
    simpa [prefixWord, tailWord_7404222, baseEnd_7404222] using wordTrace_append hprefix tailTrace_7404222
  have hstable : (prefixWord ++ tailWord_7404222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404222).length < 2 ^ (prefixWord ++ tailWord_7404222).sum := by decide
  have hdescent : baseEnd_7404222 < baseStart_7404222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404252 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7404252 : Nat := 118140960795 + 7404252 * 2 ^ 59
def prefixEnd_7404252 : Nat := 4983230072969 + 3 ^ 40 * 7404252 * 2
def baseEnd_7404252 : Nat := 3801940163014070063698471

theorem tailTrace_7404252 : CollatzResearch.WordTrace tailWord_7404252 prefixEnd_7404252 3801940163014070063698471 := by
  unfold tailWord_7404252
  simp only [CollatzResearch.WordTrace]
  refine ⟨135027628185833512205547505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180036837581111349607396673 135027628185833512205547505)
  ·
    refine ⟨101270721139375134154160629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135027628185833512205547505 101270721139375134154160629)
    ·
      refine ⟨9494130106816418826952559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101270721139375134154160629 9494130106816418826952559)
      ·
        refine ⟨14241195160224628240428839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9494130106816418826952559 14241195160224628240428839)
        ·
          refine ⟨21361792740336942360643259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14241195160224628240428839 21361792740336942360643259)
          ·
            refine ⟨32042689110505413540964889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21361792740336942360643259 32042689110505413540964889)
            ·
              refine ⟨24032016832879060155723667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32042689110505413540964889 24032016832879060155723667)
              ·
                refine ⟨36048025249318590233585501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24032016832879060155723667 36048025249318590233585501)
                ·
                  refine ⟨13518009468494471337594563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36048025249318590233585501 13518009468494471337594563)
                  ·
                    refine ⟨20277014202741707006391845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13518009468494471337594563 20277014202741707006391845)
                    ·
                      refine ⟨3801940163014070063698471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20277014202741707006391845 3801940163014070063698471)
                      ·
                        rfl

theorem cell23_7404252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7404252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404252 prefixEnd_7404252 := by exact prefixLift 7404252
  have htrace : WordTrace (prefixWord ++ tailWord_7404252) baseStart_7404252 baseEnd_7404252 := by
    simpa [prefixWord, tailWord_7404252, baseEnd_7404252] using wordTrace_append hprefix tailTrace_7404252
  have hstable : (prefixWord ++ tailWord_7404252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404252).length < 2 ^ (prefixWord ++ tailWord_7404252).sum := by decide
  have hdescent : baseEnd_7404252 < baseStart_7404252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404255 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 3]
def baseStart_7404255 : Nat := 118140960795 + 7404255 * 2 ^ 59
def prefixEnd_7404255 : Nat := 4983230072969 + 3 ^ 40 * 7404255 * 2
def baseEnd_7404255 : Nat := 3801941703456033551960957

theorem tailTrace_7404255 : CollatzResearch.WordTrace tailWord_7404255 prefixEnd_7404255 3801941703456033551960957 := by
  unfold tailWord_7404255
  simp only [CollatzResearch.WordTrace]
  refine ⟨270055365790656155923454219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180036910527104103948969479 270055365790656155923454219)
  ·
    refine ⟨405083048685984233885181329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270055365790656155923454219 405083048685984233885181329)
    ·
      refine ⟨303812286514488175413885997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405083048685984233885181329 303812286514488175413885997)
      ·
        refine ⟨113929607442933065780207249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303812286514488175413885997 113929607442933065780207249)
        ·
          refine ⟨85447205582199799335155437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113929607442933065780207249 85447205582199799335155437)
          ·
            refine ⟨32042702093324924750683289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85447205582199799335155437 32042702093324924750683289)
            ·
              refine ⟨24032026569993693563012467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32042702093324924750683289 24032026569993693563012467)
              ·
                refine ⟨36048039854990540344518701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24032026569993693563012467 36048039854990540344518701)
                ·
                  refine ⟨13518014945621452629194513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36048039854990540344518701 13518014945621452629194513)
                  ·
                    refine ⟨10138511209216089471895885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13518014945621452629194513 10138511209216089471895885)
                    ·
                      refine ⟨3801941703456033551960957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10138511209216089471895885 3801941703456033551960957)
                      ·
                        rfl

theorem cell23_7404255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_7404255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404255 prefixEnd_7404255 := by exact prefixLift 7404255
  have htrace : WordTrace (prefixWord ++ tailWord_7404255) baseStart_7404255 baseEnd_7404255 := by
    simpa [prefixWord, tailWord_7404255, baseEnd_7404255] using wordTrace_append hprefix tailTrace_7404255
  have hstable : (prefixWord ++ tailWord_7404255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404255).length < 2 ^ (prefixWord ++ tailWord_7404255).sum := by decide
  have hdescent : baseEnd_7404255 < baseStart_7404255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404286 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_7404286 : Nat := 118140960795 + 7404286 * 2 ^ 59
def prefixEnd_7404286 : Nat := 4983230072969 + 3 ^ 40 * 7404286 * 2
def baseEnd_7404286 : Nat := 3801957621356322930673315

theorem tailTrace_7404286 : CollatzResearch.WordTrace tailWord_7404286 prefixEnd_7404286 3801957621356322930673315 := by
  unfold tailWord_7404286
  simp only [CollatzResearch.WordTrace]
  refine ⟨33757062056692981027229089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180037664302362565478555141 33757062056692981027229089)
  ·
    refine ⟨25317796542519735770421817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33757062056692981027229089 25317796542519735770421817)
    ·
      refine ⟨18988347406889801827816363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25317796542519735770421817 18988347406889801827816363)
      ·
        refine ⟨28482521110334702741724545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18988347406889801827816363 28482521110334702741724545)
        ·
          refine ⟨21361890832751027056293409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28482521110334702741724545 21361890832751027056293409)
          ·
            refine ⟨16021418124563270292220057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21361890832751027056293409 16021418124563270292220057)
            ·
              refine ⟨12016063593422452719165043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16021418124563270292220057 12016063593422452719165043)
              ·
                refine ⟨18024095390133679078747565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12016063593422452719165043 18024095390133679078747565)
                ·
                  refine ⟨6759035771300129654530337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18024095390133679078747565 6759035771300129654530337)
                  ·
                    refine ⟨5069276828475097240897753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6759035771300129654530337 5069276828475097240897753)
                    ·
                      refine ⟨3801957621356322930673315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069276828475097240897753 3801957621356322930673315)
                      ·
                        rfl

theorem cell23_7404286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_7404286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404286 prefixEnd_7404286 := by exact prefixLift 7404286
  have htrace : WordTrace (prefixWord ++ tailWord_7404286) baseStart_7404286 baseEnd_7404286 := by
    simpa [prefixWord, tailWord_7404286, baseEnd_7404286] using wordTrace_append hprefix tailTrace_7404286
  have hstable : (prefixWord ++ tailWord_7404286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404286).length < 2 ^ (prefixWord ++ tailWord_7404286).sum := by decide
  have hdescent : baseEnd_7404286 < baseStart_7404286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404306 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7404306 : Nat := 118140960795 + 7404306 * 2 ^ 59
def prefixEnd_7404306 : Nat := 4983230072969 + 3 ^ 40 * 7404306 * 2
def baseEnd_7404306 : Nat := 3801967890969412852423223

theorem tailTrace_7404306 : CollatzResearch.WordTrace tailWord_7404306 prefixEnd_7404306 3801967890969412852423223 := by
  unfold tailWord_7404306
  simp only [CollatzResearch.WordTrace]
  refine ⟨67514306478367847908390193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180038150608980927755707181 67514306478367847908390193)
  ·
    refine ⟨50635729858775885931292645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67514306478367847908390193 50635729858775885931292645)
    ·
      refine ⟨9494199348520478612117371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50635729858775885931292645 9494199348520478612117371)
      ·
        refine ⟨14241299022780717918176057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9494199348520478612117371 14241299022780717918176057)
        ·
          refine ⟨10680974267085538438632043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14241299022780717918176057 10680974267085538438632043)
          ·
            refine ⟨16021461400628307657948065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10680974267085538438632043 16021461400628307657948065)
            ·
              refine ⟨12016096050471230743461049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16021461400628307657948065 12016096050471230743461049)
              ·
                refine ⟨9012072037853423057595787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12016096050471230743461049 9012072037853423057595787)
                ·
                  refine ⟨13518108056780134586393681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9012072037853423057595787 13518108056780134586393681)
                  ·
                    refine ⟨10138581042585100939795261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13518108056780134586393681 10138581042585100939795261)
                    ·
                      refine ⟨3801967890969412852423223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10138581042585100939795261 3801967890969412852423223)
                      ·
                        rfl

theorem cell23_7404306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7404306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404306 prefixEnd_7404306 := by exact prefixLift 7404306
  have htrace : WordTrace (prefixWord ++ tailWord_7404306) baseStart_7404306 baseEnd_7404306 := by
    simpa [prefixWord, tailWord_7404306, baseEnd_7404306] using wordTrace_append hprefix tailTrace_7404306
  have hstable : (prefixWord ++ tailWord_7404306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404306).length < 2 ^ (prefixWord ++ tailWord_7404306).sum := by decide
  have hdescent : baseEnd_7404306 < baseStart_7404306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404395 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 2, 5]
def baseStart_7404395 : Nat := 118140960795 + 7404395 * 2 ^ 59
def prefixEnd_7404395 : Nat := 4983230072969 + 3 ^ 40 * 7404395 * 2
def baseEnd_7404395 : Nat := 1267337863582554334736771

theorem tailTrace_7404395 : CollatzResearch.WordTrace tailWord_7404395 prefixEnd_7404395 1267337863582554334736771 := by
  unfold tailWord_7404395
  simp only [CollatzResearch.WordTrace]
  refine ⟨270060472010148959833550639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180040314673432639889033759 270060472010148959833550639)
  ·
    refine ⟨405090708015223439750325959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270060472010148959833550639 405090708015223439750325959)
    ·
      refine ⟨607636062022835159625488939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405090708015223439750325959 607636062022835159625488939)
      ·
        refine ⟨911454093034252739438233409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607636062022835159625488939 911454093034252739438233409)
        ·
          refine ⟨683590569775689554578675057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911454093034252739438233409 683590569775689554578675057)
          ·
            refine ⟨512692927331767165934006293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683590569775689554578675057 512692927331767165934006293)
            ·
              refine ⟨24032480968676585903156545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 512692927331767165934006293 24032480968676585903156545)
              ·
                refine ⟨18024360726507439427367409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24032480968676585903156545 18024360726507439427367409)
                ·
                  refine ⟨13518270544880579570525557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18024360726507439427367409 13518270544880579570525557)
                  ·
                    refine ⟨1267337863582554334736771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13518270544880579570525557 1267337863582554334736771)
                    ·
                      rfl

theorem cell23_7404395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 5].length) (baseStart_7404395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404395 prefixEnd_7404395 := by exact prefixLift 7404395
  have htrace : WordTrace (prefixWord ++ tailWord_7404395) baseStart_7404395 baseEnd_7404395 := by
    simpa [prefixWord, tailWord_7404395, baseEnd_7404395] using wordTrace_append hprefix tailTrace_7404395
  have hstable : (prefixWord ++ tailWord_7404395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404395).length < 2 ^ (prefixWord ++ tailWord_7404395).sum := by decide
  have hdescent : baseEnd_7404395 < baseStart_7404395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404402 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_7404402 : Nat := 118140960795 + 7404402 * 2 ^ 59
def prefixEnd_7404402 : Nat := 4983230072969 + 3 ^ 40 * 7404402 * 2
def baseEnd_7404402 : Nat := 3802017185112244476822781

theorem tailTrace_7404402 : CollatzResearch.WordTrace tailWord_7404402 prefixEnd_7404402 3802017185112244476822781 := by
  unfold tailWord_7404402
  simp only [CollatzResearch.WordTrace]
  refine ⟨67515181830280900007263865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180040484880749066686036973 67515181830280900007263865)
  ·
    refine ⟨50636386372710675005447899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67515181830280900007263865 50636386372710675005447899)
    ·
      refine ⟨75954579559066012508171849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50636386372710675005447899 75954579559066012508171849)
      ·
        refine ⟨56965934669299509381128887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75954579559066012508171849 56965934669299509381128887)
        ·
          refine ⟨85448902003949264071693331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56965934669299509381128887 85448902003949264071693331)
          ·
            refine ⟨128173353005923896107539997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85448902003949264071693331 128173353005923896107539997)
            ·
              refine ⟨48065007377221461040327499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128173353005923896107539997 48065007377221461040327499)
              ·
                refine ⟨72097511065832191560491249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48065007377221461040327499 72097511065832191560491249)
                ·
                  refine ⟨54073133299374143670368437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72097511065832191560491249 54073133299374143670368437)
                  ·
                    refine ⟨5069356246816325969097041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54073133299374143670368437 5069356246816325969097041)
                    ·
                      refine ⟨3802017185112244476822781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069356246816325969097041 3802017185112244476822781)
                      ·
                        rfl

theorem cell23_7404402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_7404402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404402 prefixEnd_7404402 := by exact prefixLift 7404402
  have htrace : WordTrace (prefixWord ++ tailWord_7404402) baseStart_7404402 baseEnd_7404402 := by
    simpa [prefixWord, tailWord_7404402, baseEnd_7404402] using wordTrace_append hprefix tailTrace_7404402
  have hstable : (prefixWord ++ tailWord_7404402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404402).length < 2 ^ (prefixWord ++ tailWord_7404402).sum := by decide
  have hdescent : baseEnd_7404402 < baseStart_7404402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404415 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_7404415 : Nat := 118140960795 + 7404415 * 2 ^ 59
def prefixEnd_7404415 : Nat := 4983230072969 + 3 ^ 40 * 7404415 * 2
def baseEnd_7404415 : Nat := 3802023860360752925960221

theorem tailTrace_7404415 : CollatzResearch.WordTrace tailWord_7404415 prefixEnd_7404415 3802023860360752925960221 := by
  unfold tailWord_7404415
  simp only [CollatzResearch.WordTrace]
  refine ⟨270061201470076503249278699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180040800980051002166185799 270061201470076503249278699)
  ·
    refine ⟨405091802205114754873918049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270061201470076503249278699 405091802205114754873918049)
    ·
      refine ⟨303818851653836066155438537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405091802205114754873918049 303818851653836066155438537)
      ·
        refine ⟨227864138740377049616578903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303818851653836066155438537 227864138740377049616578903)
        ·
          refine ⟨341796208110565574424868355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227864138740377049616578903 341796208110565574424868355)
          ·
            refine ⟨512694312165848361637302533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341796208110565574424868355 512694312165848361637302533)
            ·
              refine ⟨96130183531096567806994225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 512694312165848361637302533 96130183531096567806994225)
              ·
                refine ⟨72097637648322425855245669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96130183531096567806994225 72097637648322425855245669)
                ·
                  refine ⟨13518307059060454847858563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72097637648322425855245669 13518307059060454847858563)
                  ·
                    refine ⟨20277460588590682271787845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13518307059060454847858563 20277460588590682271787845)
                    ·
                      refine ⟨3802023860360752925960221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20277460588590682271787845 3802023860360752925960221)
                      ·
                        rfl

theorem cell23_7404415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_7404415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404415 prefixEnd_7404415 := by exact prefixLift 7404415
  have htrace : WordTrace (prefixWord ++ tailWord_7404415) baseStart_7404415 baseEnd_7404415 := by
    simpa [prefixWord, tailWord_7404415, baseEnd_7404415] using wordTrace_append hprefix tailTrace_7404415
  have hstable : (prefixWord ++ tailWord_7404415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404415).length < 2 ^ (prefixWord ++ tailWord_7404415).sum := by decide
  have hdescent : baseEnd_7404415 < baseStart_7404415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404445 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_7404445 : Nat := 118140960795 + 7404445 * 2 ^ 59
def prefixEnd_7404445 : Nat := 4983230072969 + 3 ^ 40 * 7404445 * 2
def baseEnd_7404445 : Nat := 3802039264780387808585083

theorem tailTrace_7404445 : CollatzResearch.WordTrace tailWord_7404445 prefixEnd_7404445 3802039264780387808585083 := by
  unfold tailWord_7404445
  simp only [CollatzResearch.WordTrace]
  refine ⟨270062295659967818372870789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180041530439978545581913859 270062295659967818372870789)
  ·
    refine ⟨50636680436243965944913273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270062295659967818372870789 50636680436243965944913273)
    ·
      refine ⟨37977510327182974458684955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50636680436243965944913273 37977510327182974458684955)
      ·
        refine ⟨56966265490774461688027433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37977510327182974458684955 56966265490774461688027433)
        ·
          refine ⟨42724699118080846266020575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56966265490774461688027433 42724699118080846266020575)
          ·
            refine ⟨64087048677121269399030863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42724699118080846266020575 64087048677121269399030863)
            ·
              refine ⟨96130573015681904098546295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64087048677121269399030863 96130573015681904098546295)
              ·
                refine ⟨144195859523522856147819443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96130573015681904098546295 144195859523522856147819443)
                ·
                  refine ⟨216293789285284284221729165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144195859523522856147819443 216293789285284284221729165)
                  ·
                    refine ⟨81110170981981606583148437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216293789285284284221729165 81110170981981606583148437)
                    ·
                      refine ⟨3802039264780387808585083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81110170981981606583148437 3802039264780387808585083)
                      ·
                        rfl

theorem cell23_7404445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_7404445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404445 prefixEnd_7404445 := by exact prefixLift 7404445
  have htrace : WordTrace (prefixWord ++ tailWord_7404445) baseStart_7404445 baseEnd_7404445 := by
    simpa [prefixWord, tailWord_7404445, baseEnd_7404445] using wordTrace_append hprefix tailTrace_7404445
  have hstable : (prefixWord ++ tailWord_7404445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404445).length < 2 ^ (prefixWord ++ tailWord_7404445).sum := by decide
  have hdescent : baseEnd_7404445 < baseStart_7404445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404449 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7404449 : Nat := 118140960795 + 7404449 * 2 ^ 59
def prefixEnd_7404449 : Nat := 4983230072969 + 3 ^ 40 * 7404449 * 2
def baseEnd_7404449 : Nat := 3802041318703005792935065

theorem tailTrace_7404449 : CollatzResearch.WordTrace tailWord_7404449 prefixEnd_7404449 3802041318703005792935065 := by
  unfold tailWord_7404449
  simp only [CollatzResearch.WordTrace]
  refine ⟨270062441551953327056016401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180041627701302218037344267 270062441551953327056016401)
  ·
    refine ⟨202546831163964995292012301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270062441551953327056016401 202546831163964995292012301)
    ·
      refine ⟨75955061686486873234504613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202546831163964995292012301 75955061686486873234504613)
      ·
        refine ⟨14241574066216288731469615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75955061686486873234504613 14241574066216288731469615)
        ·
          refine ⟨21362361099324433097204423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14241574066216288731469615 21362361099324433097204423)
          ·
            refine ⟨32043541648986649645806635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21362361099324433097204423 32043541648986649645806635)
            ·
              refine ⟨48065312473479974468709953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32043541648986649645806635 48065312473479974468709953)
              ·
                refine ⟨36048984355109980851532465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48065312473479974468709953 36048984355109980851532465)
                ·
                  refine ⟨27036738266332485638649349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36048984355109980851532465 27036738266332485638649349)
                  ·
                    refine ⟨5069388424937341057246753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27036738266332485638649349 5069388424937341057246753)
                    ·
                      refine ⟨3802041318703005792935065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069388424937341057246753 3802041318703005792935065)
                      ·
                        rfl

theorem cell23_7404449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7404449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404449 prefixEnd_7404449 := by exact prefixLift 7404449
  have htrace : WordTrace (prefixWord ++ tailWord_7404449) baseStart_7404449 baseEnd_7404449 := by
    simpa [prefixWord, tailWord_7404449, baseEnd_7404449] using wordTrace_append hprefix tailTrace_7404449
  have hstable : (prefixWord ++ tailWord_7404449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404449).length < 2 ^ (prefixWord ++ tailWord_7404449).sum := by decide
  have hdescent : baseEnd_7404449 < baseStart_7404449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404452 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_7404452 : Nat := 118140960795 + 7404452 * 2 ^ 59
def prefixEnd_7404452 : Nat := 4983230072969 + 3 ^ 40 * 7404452 * 2
def baseEnd_7404452 : Nat := 3802042859144969281197551

theorem tailTrace_7404452 : CollatzResearch.WordTrace tailWord_7404452 prefixEnd_7404452 3802042859144969281197551 := by
  unfold tailWord_7404452
  simp only [CollatzResearch.WordTrace]
  refine ⟨135031275485471229284187805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180041700647294972378917073 135031275485471229284187805)
  ·
    refine ⟨50636728307051710981570427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135031275485471229284187805 50636728307051710981570427)
    ·
      refine ⟨75955092460577566472355641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50636728307051710981570427 75955092460577566472355641)
      ·
        refine ⟨56966319345433174854266731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75955092460577566472355641 56966319345433174854266731)
        ·
          refine ⟨85449479018149762281400097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56966319345433174854266731 85449479018149762281400097)
          ·
            refine ⟨64087109263612321711050073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85449479018149762281400097 64087109263612321711050073)
            ·
              refine ⟨48065331947709241283287555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64087109263612321711050073 48065331947709241283287555)
              ·
                refine ⟨72097997921563861924931333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48065331947709241283287555 72097997921563861924931333)
                ·
                  refine ⟨13518374610293224110924625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72097997921563861924931333 13518374610293224110924625)
                  ·
                    refine ⟨10138780957719918083193469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13518374610293224110924625 10138780957719918083193469)
                    ·
                      refine ⟨3802042859144969281197551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10138780957719918083193469 3802042859144969281197551)
                      ·
                        rfl

theorem cell23_7404452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_7404452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404452 prefixEnd_7404452 := by exact prefixLift 7404452
  have htrace : WordTrace (prefixWord ++ tailWord_7404452) baseStart_7404452 baseEnd_7404452 := by
    simpa [prefixWord, tailWord_7404452, baseEnd_7404452] using wordTrace_append hprefix tailTrace_7404452
  have hstable : (prefixWord ++ tailWord_7404452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404452).length < 2 ^ (prefixWord ++ tailWord_7404452).sum := by decide
  have hdescent : baseEnd_7404452 < baseStart_7404452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404485 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_7404485 : Nat := 118140960795 + 7404485 * 2 ^ 59
def prefixEnd_7404485 : Nat := 4983230072969 + 3 ^ 40 * 7404485 * 2
def baseEnd_7404485 : Nat := 1267353268002189217361633

theorem tailTrace_7404485 : CollatzResearch.WordTrace tailWord_7404485 prefixEnd_7404485 1267353268002189217361633 := by
  unfold tailWord_7404485
  simp only [CollatzResearch.WordTrace]
  refine ⟨270063754579822905204326909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180042503053215270136217939 270063754579822905204326909)
  ·
    refine ⟨101273907967433589451622591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270063754579822905204326909 101273907967433589451622591)
    ·
      refine ⟨151910861951150384177433887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101273907967433589451622591 151910861951150384177433887)
      ·
        refine ⟨227866292926725576266150831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151910861951150384177433887 227866292926725576266150831)
        ·
          refine ⟨341799439390088364399226247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227866292926725576266150831 341799439390088364399226247)
          ·
            refine ⟨512699159085132546598839371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341799439390088364399226247 512699159085132546598839371)
            ·
              refine ⟨769048738627698819898259057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512699159085132546598839371 769048738627698819898259057)
              ·
                refine ⟨576786553970774114923694293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769048738627698819898259057 576786553970774114923694293)
                ·
                  refine ⟨13518434858690018318524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 576786553970774114923694293 13518434858690018318524085)
                  ·
                    refine ⟨1267353268002189217361633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13518434858690018318524085 1267353268002189217361633)
                    ·
                      rfl

theorem cell23_7404485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_7404485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404485 prefixEnd_7404485 := by exact prefixLift 7404485
  have htrace : WordTrace (prefixWord ++ tailWord_7404485) baseStart_7404485 baseEnd_7404485 := by
    simpa [prefixWord, tailWord_7404485, baseEnd_7404485] using wordTrace_append hprefix tailTrace_7404485
  have hstable : (prefixWord ++ tailWord_7404485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404485).length < 2 ^ (prefixWord ++ tailWord_7404485).sum := by decide
  have hdescent : baseEnd_7404485 < baseStart_7404485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404539 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 5, 2, 2]
def baseStart_7404539 : Nat := 118140960795 + 7404539 * 2 ^ 59
def prefixEnd_7404539 : Nat := 4983230072969 + 3 ^ 40 * 7404539 * 2
def baseEnd_7404539 : Nat := 3802087531961910440809651

theorem tailTrace_7404539 : CollatzResearch.WordTrace tailWord_7404539 prefixEnd_7404539 3802087531961910440809651 := by
  unfold tailWord_7404539
  simp only [CollatzResearch.WordTrace]
  refine ⟨270065724121627272426792671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180043816081084848284528447 270065724121627272426792671)
  ·
    refine ⟨405098586182440908640189007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270065724121627272426792671 405098586182440908640189007)
    ·
      refine ⟨607647879273661362960283511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405098586182440908640189007 607647879273661362960283511)
      ·
        refine ⟨911471818910492044440425267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607647879273661362960283511 911471818910492044440425267)
        ·
          refine ⟨1367207728365738066660637901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911471818910492044440425267 1367207728365738066660637901)
          ·
            refine ⟨512702898137151774997739213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1367207728365738066660637901 512702898137151774997739213)
            ·
              refine ⟨192263586801431915624152205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512702898137151774997739213 192263586801431915624152205)
              ·
                refine ⟨72098845050536968359057077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192263586801431915624152205 72098845050536968359057077)
                ·
                  refine ⟨6759266723487840783661601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72098845050536968359057077 6759266723487840783661601)
                  ·
                    refine ⟨5069450042615880587746201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6759266723487840783661601 5069450042615880587746201)
                    ·
                      refine ⟨3802087531961910440809651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069450042615880587746201 3802087531961910440809651)
                      ·
                        rfl

theorem cell23_7404539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 2, 2].length) (baseStart_7404539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404539 prefixEnd_7404539 := by exact prefixLift 7404539
  have htrace : WordTrace (prefixWord ++ tailWord_7404539) baseStart_7404539 baseEnd_7404539 := by
    simpa [prefixWord, tailWord_7404539, baseEnd_7404539] using wordTrace_append hprefix tailTrace_7404539
  have hstable : (prefixWord ++ tailWord_7404539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404539).length < 2 ^ (prefixWord ++ tailWord_7404539).sum := by decide
  have hdescent : baseEnd_7404539 < baseStart_7404539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404552 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_7404552 : Nat := 118140960795 + 7404552 * 2 ^ 59
def prefixEnd_7404552 : Nat := 4983230072969 + 3 ^ 40 * 7404552 * 2
def baseEnd_7404552 : Nat := 3802094207210418889947091

theorem tailTrace_7404552 : CollatzResearch.WordTrace tailWord_7404552 prefixEnd_7404552 3802094207210418889947091 := by
  unfold tailWord_7404552
  simp only [CollatzResearch.WordTrace]
  refine ⟨135033099135290087823507955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180044132180386783764677273 135033099135290087823507955)
  ·
    refine ⟨202549648702935131735261933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135033099135290087823507955 202549648702935131735261933)
    ·
      refine ⟨75956118263600674400723225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202549648702935131735261933 75956118263600674400723225)
      ·
        refine ⟨56967088697700505800542419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75956118263600674400723225 56967088697700505800542419)
        ·
          refine ⟨85450633046550758700813629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56967088697700505800542419 85450633046550758700813629)
          ·
            refine ⟨32043987392456534512805111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85450633046550758700813629 32043987392456534512805111)
            ·
              refine ⟨48065981088684801769207667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32043987392456534512805111 48065981088684801769207667)
              ·
                refine ⟨72098971633027202653811501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48065981088684801769207667 72098971633027202653811501)
                ·
                  refine ⟨27037114362385200995179313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72098971633027202653811501 27037114362385200995179313)
                  ·
                    refine ⟨20277835771788900746384485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27037114362385200995179313 20277835771788900746384485)
                    ·
                      refine ⟨3802094207210418889947091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20277835771788900746384485 3802094207210418889947091)
                      ·
                        rfl

theorem cell23_7404552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_7404552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404552 prefixEnd_7404552 := by exact prefixLift 7404552
  have htrace : WordTrace (prefixWord ++ tailWord_7404552) baseStart_7404552 baseEnd_7404552 := by
    simpa [prefixWord, tailWord_7404552, baseEnd_7404552] using wordTrace_append hprefix tailTrace_7404552
  have hstable : (prefixWord ++ tailWord_7404552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404552).length < 2 ^ (prefixWord ++ tailWord_7404552).sum := by decide
  have hdescent : baseEnd_7404552 < baseStart_7404552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404556 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 1, 1, 4]
def baseStart_7404556 : Nat := 118140960795 + 7404556 * 2 ^ 59
def prefixEnd_7404556 : Nat := 4983230072969 + 3 ^ 40 * 7404556 * 2
def baseEnd_7404556 : Nat := 3802096261133036874297073

theorem tailTrace_7404556 : CollatzResearch.WordTrace tailWord_7404556 prefixEnd_7404556 3802096261133036874297073 := by
  unfold tailWord_7404556
  simp only [CollatzResearch.WordTrace]
  refine ⟨135033172081282842165080761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180044229441710456220107681 135033172081282842165080761)
  ·
    refine ⟨101274879060962131623810571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135033172081282842165080761 101274879060962131623810571)
    ·
      refine ⟨151912318591443197435715857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101274879060962131623810571 151912318591443197435715857)
      ·
        refine ⟨113934238943582398076786893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151912318591443197435715857 113934238943582398076786893)
        ·
          refine ⟨42725339603843399278795085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113934238943582398076786893 42725339603843399278795085)
          ·
            refine ⟨16022002351441274729548157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42725339603843399278795085 16022002351441274729548157)
            ·
              refine ⟨6008250881790478023580559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16022002351441274729548157 6008250881790478023580559)
              ·
                refine ⟨9012376322685717035370839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6008250881790478023580559 9012376322685717035370839)
                ·
                  refine ⟨13518564484028575553056259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9012376322685717035370839 13518564484028575553056259)
                  ·
                    refine ⟨20277846726042863329584389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13518564484028575553056259 20277846726042863329584389)
                    ·
                      refine ⟨3802096261133036874297073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20277846726042863329584389 3802096261133036874297073)
                      ·
                        rfl

theorem cell23_7404556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_7404556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404556 prefixEnd_7404556 := by exact prefixLift 7404556
  have htrace : WordTrace (prefixWord ++ tailWord_7404556) baseStart_7404556 baseEnd_7404556 := by
    simpa [prefixWord, tailWord_7404556, baseEnd_7404556] using wordTrace_append hprefix tailTrace_7404556
  have hstable : (prefixWord ++ tailWord_7404556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404556).length < 2 ^ (prefixWord ++ tailWord_7404556).sum := by decide
  have hdescent : baseEnd_7404556 < baseStart_7404556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404586 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_7404586 : Nat := 118140960795 + 7404586 * 2 ^ 59
def prefixEnd_7404586 : Nat := 4983230072969 + 3 ^ 40 * 7404586 * 2
def baseEnd_7404586 : Nat := 3802111665552671756921935

theorem tailTrace_7404586 : CollatzResearch.WordTrace tailWord_7404586 prefixEnd_7404586 3802111665552671756921935 := by
  unfold tailWord_7404586
  simp only [CollatzResearch.WordTrace]
  refine ⟨67516859588114249863438403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180044958901637999635835741 67516859588114249863438403)
  ·
    refine ⟨101275289382171374795157605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67516859588114249863438403 101275289382171374795157605)
    ·
      refine ⟨18989116759157132774092051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101275289382171374795157605 18989116759157132774092051)
      ·
        refine ⟨28483675138735699161138077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18989116759157132774092051 28483675138735699161138077)
        ·
          refine ⟨10681378177025887185426779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28483675138735699161138077 10681378177025887185426779)
          ·
            refine ⟨16022067265538830778140169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10681378177025887185426779 16022067265538830778140169)
            ·
              refine ⟨12016550449154123083605127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16022067265538830778140169 12016550449154123083605127)
              ·
                refine ⟨18024825673731184625407691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12016550449154123083605127 18024825673731184625407691)
                ·
                  refine ⟨27037238510596776938111537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18024825673731184625407691 27037238510596776938111537)
                  ·
                    refine ⟨20277928882947582703583653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27037238510596776938111537 20277928882947582703583653)
                    ·
                      refine ⟨3802111665552671756921935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20277928882947582703583653 3802111665552671756921935)
                      ·
                        rfl

theorem cell23_7404586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_7404586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404586 prefixEnd_7404586 := by exact prefixLift 7404586
  have htrace : WordTrace (prefixWord ++ tailWord_7404586) baseStart_7404586 baseEnd_7404586 := by
    simpa [prefixWord, tailWord_7404586, baseEnd_7404586] using wordTrace_append hprefix tailTrace_7404586
  have hstable : (prefixWord ++ tailWord_7404586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404586).length < 2 ^ (prefixWord ++ tailWord_7404586).sum := by decide
  have hdescent : baseEnd_7404586 < baseStart_7404586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404596 : List Nat := [2, 5, 1, 2, 1, 2, 3, 7]
def baseStart_7404596 : Nat := 118140960795 + 7404596 * 2 ^ 59
def prefixEnd_7404596 : Nat := 4983230072969 + 3 ^ 40 * 7404596 * 2
def baseEnd_7404596 : Nat := 140819140754045063622107

theorem tailTrace_7404596 : CollatzResearch.WordTrace tailWord_7404596 prefixEnd_7404596 140819140754045063622107 := by
  unfold tailWord_7404596
  simp only [CollatzResearch.WordTrace]
  refine ⟨135033901541210385580808821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180045202054947180774411761 135033901541210385580808821)
  ·
    refine ⟨12659428269488473648200827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135033901541210385580808821 12659428269488473648200827)
    ·
      refine ⟨18989142404232710472301241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12659428269488473648200827 18989142404232710472301241)
      ·
        refine ⟨14241856803174532854225931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18989142404232710472301241 14241856803174532854225931)
        ·
          refine ⟨21362785204761799281338897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14241856803174532854225931 21362785204761799281338897)
          ·
            refine ⟨16022088903571349461004173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21362785204761799281338897 16022088903571349461004173)
            ·
              refine ⟨6008283338839256047876565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16022088903571349461004173 6008283338839256047876565)
              ·
                refine ⟨140819140754045063622107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6008283338839256047876565 140819140754045063622107)
                ·
                  rfl

theorem cell23_7404596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 7].length) (baseStart_7404596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404596 prefixEnd_7404596 := by exact prefixLift 7404596
  have htrace : WordTrace (prefixWord ++ tailWord_7404596) baseStart_7404596 baseEnd_7404596 := by
    simpa [prefixWord, tailWord_7404596, baseEnd_7404596] using wordTrace_append hprefix tailTrace_7404596
  have hstable : (prefixWord ++ tailWord_7404596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404596).length < 2 ^ (prefixWord ++ tailWord_7404596).sum := by decide
  have hdescent : baseEnd_7404596 < baseStart_7404596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404606 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_7404606 : Nat := 118140960795 + 7404606 * 2 ^ 59
def prefixEnd_7404606 : Nat := 4983230072969 + 3 ^ 40 * 7404606 * 2
def baseEnd_7404606 : Nat := 3802121935165761678671843

theorem tailTrace_7404606 : CollatzResearch.WordTrace tailWord_7404606 prefixEnd_7404606 3802121935165761678671843 := by
  unfold tailWord_7404606
  simp only [CollatzResearch.WordTrace]
  refine ⟨33758520976548067858685209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180045445208256361912987781 33758520976548067858685209)
  ·
    refine ⟨25318890732411050894013907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33758520976548067858685209 25318890732411050894013907)
    ·
      refine ⟨37978336098616576341020861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25318890732411050894013907 37978336098616576341020861)
      ·
        refine ⟨14241876036981216127882823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37978336098616576341020861 14241876036981216127882823)
        ·
          refine ⟨21362814055471824191824235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14241876036981216127882823 21362814055471824191824235)
          ·
            refine ⟨32044221083207736287736353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21362814055471824191824235 32044221083207736287736353)
            ·
              refine ⟨24033165812405802215802265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32044221083207736287736353 24033165812405802215802265)
              ·
                refine ⟨18024874359304351661851699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24033165812405802215802265 18024874359304351661851699)
                ·
                  refine ⟨27037311538956527492777549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18024874359304351661851699 27037311538956527492777549)
                  ·
                    refine ⟨10138991827108697809791581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27037311538956527492777549 10138991827108697809791581)
                    ·
                      refine ⟨3802121935165761678671843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10138991827108697809791581 3802121935165761678671843)
                      ·
                        rfl

theorem cell23_7404606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_7404606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404606 prefixEnd_7404606 := by exact prefixLift 7404606
  have htrace : WordTrace (prefixWord ++ tailWord_7404606) baseStart_7404606 baseEnd_7404606 := by
    simpa [prefixWord, tailWord_7404606, baseEnd_7404606] using wordTrace_append hprefix tailTrace_7404606
  have hstable : (prefixWord ++ tailWord_7404606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404606).length < 2 ^ (prefixWord ++ tailWord_7404606).sum := by decide
  have hdescent : baseEnd_7404606 < baseStart_7404606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404616 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_7404616 : Nat := 118140960795 + 7404616 * 2 ^ 59
def prefixEnd_7404616 : Nat := 4983230072969 + 3 ^ 40 * 7404616 * 2
def baseEnd_7404616 : Nat := 3802127069972306639546797

theorem tailTrace_7404616 : CollatzResearch.WordTrace tailWord_7404616 prefixEnd_7404616 3802127069972306639546797 := by
  unfold tailWord_7404616
  simp only [CollatzResearch.WordTrace]
  refine ⟨135034266271174157288672851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180045688361565543051563801 135034266271174157288672851)
  ·
    refine ⟨202551399406761235933009277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135034266271174157288672851 202551399406761235933009277)
    ·
      refine ⟨75956774777535463474878479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202551399406761235933009277 75956774777535463474878479)
      ·
        refine ⟨113935162166303195212317719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75956774777535463474878479 113935162166303195212317719)
        ·
          refine ⟨170902743249454792818476579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113935162166303195212317719 170902743249454792818476579)
          ·
            refine ⟨256354114874182189227714869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170902743249454792818476579 256354114874182189227714869)
            ·
              refine ⟨24033198269454580240098269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256354114874182189227714869 24033198269454580240098269)
              ·
                refine ⟨9012449351045467590036851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24033198269454580240098269 9012449351045467590036851)
                ·
                  refine ⟨13518674026568201385055277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9012449351045467590036851 13518674026568201385055277)
                  ·
                    refine ⟨5069502759963075519395729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13518674026568201385055277 5069502759963075519395729)
                    ·
                      refine ⟨3802127069972306639546797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069502759963075519395729 3802127069972306639546797)
                      ·
                        rfl

theorem cell23_7404616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_7404616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404616 prefixEnd_7404616 := by exact prefixLift 7404616
  have htrace : WordTrace (prefixWord ++ tailWord_7404616) baseStart_7404616 baseEnd_7404616 := by
    simpa [prefixWord, tailWord_7404616, baseEnd_7404616] using wordTrace_append hprefix tailTrace_7404616
  have hstable : (prefixWord ++ tailWord_7404616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404616).length < 2 ^ (prefixWord ++ tailWord_7404616).sum := by decide
  have hdescent : baseEnd_7404616 < baseStart_7404616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404622 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_7404622 : Nat := 118140960795 + 7404622 * 2 ^ 59
def prefixEnd_7404622 : Nat := 4983230072969 + 3 ^ 40 * 7404622 * 2
def baseEnd_7404622 : Nat := 1267376716952077872023923

theorem tailTrace_7404622 : CollatzResearch.WordTrace tailWord_7404622 prefixEnd_7404622 1267376716952077872023923 := by
  unfold tailWord_7404622
  simp only [CollatzResearch.WordTrace]
  refine ⟨33758593922540822200258015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180045834253551051734709413 33758593922540822200258015)
  ·
    refine ⟨50637890883811233300387023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33758593922540822200258015 50637890883811233300387023)
    ·
      refine ⟨75956836325716849950580535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50637890883811233300387023 75956836325716849950580535)
      ·
        refine ⟨113935254488575274925870803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75956836325716849950580535 113935254488575274925870803)
        ·
          refine ⟨170902881732862912388806205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113935254488575274925870803 170902881732862912388806205)
          ·
            refine ⟨64088580649823592145802327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170902881732862912388806205 64088580649823592145802327)
            ·
              refine ⟨96132870974735388218703491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64088580649823592145802327 96132870974735388218703491)
              ·
                refine ⟨144199306462103082328055237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96132870974735388218703491 144199306462103082328055237)
                ·
                  refine ⟨27037369961644327936510357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144199306462103082328055237 27037369961644327936510357)
                  ·
                    refine ⟨1267376716952077872023923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27037369961644327936510357 1267376716952077872023923)
                    ·
                      rfl

theorem cell23_7404622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_7404622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404622 prefixEnd_7404622 := by exact prefixLift 7404622
  have htrace : WordTrace (prefixWord ++ tailWord_7404622) baseStart_7404622 baseEnd_7404622 := by
    simpa [prefixWord, tailWord_7404622, baseEnd_7404622] using wordTrace_append hprefix tailTrace_7404622
  have hstable : (prefixWord ++ tailWord_7404622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404622).length < 2 ^ (prefixWord ++ tailWord_7404622).sum := by decide
  have hdescent : baseEnd_7404622 < baseStart_7404622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404652 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 7]
def baseStart_7404652 : Nat := 118140960795 + 7404652 * 2 ^ 59
def prefixEnd_7404652 : Nat := 4983230072969 + 3 ^ 40 * 7404652 * 2
def baseEnd_7404652 : Nat := 422460617252874277632959

theorem tailTrace_7404652 : CollatzResearch.WordTrace tailWord_7404652 prefixEnd_7404652 422460617252874277632959 := by
  unfold tailWord_7404652
  simp only [CollatzResearch.WordTrace]
  refine ⟨135034922785108946362828105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180046563713478595150437473 135034922785108946362828105)
  ·
    refine ⟨101276192088831709772121079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135034922785108946362828105 101276192088831709772121079)
    ·
      refine ⟨151914288133247564658181619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101276192088831709772121079 151914288133247564658181619)
      ·
        refine ⟨227871432199871346987272429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151914288133247564658181619 227871432199871346987272429)
        ·
          refine ⟨85451787074951755120227161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227871432199871346987272429 85451787074951755120227161)
          ·
            refine ⟨64088840306213816340170371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85451787074951755120227161 64088840306213816340170371)
            ·
              refine ⟨96133260459320724510255557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64088840306213816340170371 96133260459320724510255557)
              ·
                refine ⟨18024986336122635845672917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96133260459320724510255557 18024986336122635845672917)
                ·
                  refine ⟨422460617252874277632959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18024986336122635845672917 422460617252874277632959)
                  ·
                    rfl

theorem cell23_7404652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_7404652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404652 prefixEnd_7404652 := by exact prefixLift 7404652
  have htrace : WordTrace (prefixWord ++ tailWord_7404652) baseStart_7404652 baseEnd_7404652 := by
    simpa [prefixWord, tailWord_7404652, baseEnd_7404652] using wordTrace_append hprefix tailTrace_7404652
  have hstable : (prefixWord ++ tailWord_7404652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404652).length < 2 ^ (prefixWord ++ tailWord_7404652).sum := by decide
  have hdescent : baseEnd_7404652 < baseStart_7404652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404686 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_7404686 : Nat := 118140960795 + 7404686 * 2 ^ 59
def prefixEnd_7404686 : Nat := 4983230072969 + 3 ^ 40 * 7404686 * 2
def baseEnd_7404686 : Nat := 422462557068680151741275

theorem tailTrace_7404686 : CollatzResearch.WordTrace tailWord_7404686 prefixEnd_7404686 422462557068680151741275 := by
  unfold tailWord_7404686
  simp only [CollatzResearch.WordTrace]
  refine ⟨33758885706511839566549239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180047390434729811021595941 33758885706511839566549239)
  ·
    refine ⟨50638328559767759349823859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33758885706511839566549239 50638328559767759349823859)
    ·
      refine ⟨75957492839651639024735789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50638328559767759349823859 75957492839651639024735789)
      ·
        refine ⟨28484059814869364634275921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75957492839651639024735789 28484059814869364634275921)
        ·
          refine ⟨21363044861152023475706941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28484059814869364634275921 21363044861152023475706941)
          ·
            refine ⟨8011141822932008803390103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21363044861152023475706941 8011141822932008803390103)
            ·
              refine ⟨12016712734398013205085155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8011141822932008803390103 12016712734398013205085155)
              ·
                refine ⟨18025069101597019807627733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12016712734398013205085155 18025069101597019807627733)
                ·
                  refine ⟨422462557068680151741275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18025069101597019807627733 422462557068680151741275)
                  ·
                    rfl

theorem cell23_7404686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_7404686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404686 prefixEnd_7404686 := by exact prefixLift 7404686
  have htrace : WordTrace (prefixWord ++ tailWord_7404686) baseStart_7404686 baseEnd_7404686 := by
    simpa [prefixWord, tailWord_7404686, baseEnd_7404686] using wordTrace_append hprefix tailTrace_7404686
  have hstable : (prefixWord ++ tailWord_7404686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404686).length < 2 ^ (prefixWord ++ tailWord_7404686).sum := by decide
  have hdescent : baseEnd_7404686 < baseStart_7404686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404719 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_7404719 : Nat := 118140960795 + 7404719 * 2 ^ 59
def prefixEnd_7404719 : Nat := 4983230072969 + 3 ^ 40 * 7404719 * 2
def baseEnd_7404719 : Nat := 3802179958479719736558823

theorem tailTrace_7404719 : CollatzResearch.WordTrace tailWord_7404719 prefixEnd_7404719 3802179958479719736558823 := by
  unfold tailWord_7404719
  simp only [CollatzResearch.WordTrace]
  refine ⟨270072289260975163168345211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180048192840650108778896807 270072289260975163168345211)
  ·
    refine ⟨405108433891462744752517817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270072289260975163168345211 405108433891462744752517817)
    ·
      refine ⟨303831325418597058564388363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405108433891462744752517817 303831325418597058564388363)
      ·
        refine ⟨455746988127895587846582545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303831325418597058564388363 455746988127895587846582545)
        ·
          refine ⟨341810241095921690884936909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455746988127895587846582545 341810241095921690884936909)
          ·
            refine ⟨128178840410970634081851341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341810241095921690884936909 128178840410970634081851341)
            ·
              refine ⟨48067065154113987780694253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128178840410970634081851341 48067065154113987780694253)
              ·
                refine ⟨18025149432792745417760345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48067065154113987780694253 18025149432792745417760345)
                ·
                  refine ⟨13518862074594559063320259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18025149432792745417760345 13518862074594559063320259)
                  ·
                    refine ⟨20278293111891838594980389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13518862074594559063320259 20278293111891838594980389)
                    ·
                      refine ⟨3802179958479719736558823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20278293111891838594980389 3802179958479719736558823)
                      ·
                        rfl

theorem cell23_7404719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_7404719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404719 prefixEnd_7404719 := by exact prefixLift 7404719
  have htrace : WordTrace (prefixWord ++ tailWord_7404719) baseStart_7404719 baseEnd_7404719 := by
    simpa [prefixWord, tailWord_7404719, baseEnd_7404719] using wordTrace_append hprefix tailTrace_7404719
  have hstable : (prefixWord ++ tailWord_7404719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404719).length < 2 ^ (prefixWord ++ tailWord_7404719).sum := by decide
  have hdescent : baseEnd_7404719 < baseStart_7404719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404739 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 3]
def baseStart_7404739 : Nat := 118140960795 + 7404739 * 2 ^ 59
def prefixEnd_7404739 : Nat := 4983230072969 + 3 ^ 40 * 7404739 * 2
def baseEnd_7404739 : Nat := 3802190228092809658308731

theorem tailTrace_7404739 : CollatzResearch.WordTrace tailWord_7404739 prefixEnd_7404739 3802190228092809658308731 := by
  unfold tailWord_7404739
  simp only [CollatzResearch.WordTrace]
  refine ⟨270073018720902706584073271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180048679147268471056048847 270073018720902706584073271)
  ·
    refine ⟨405109528081354059876109907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270073018720902706584073271 405109528081354059876109907)
    ·
      refine ⟨607664292122031089814164861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405109528081354059876109907 607664292122031089814164861)
      ·
        refine ⟨227874109545761658680311823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607664292122031089814164861 227874109545761658680311823)
        ·
          refine ⟨341811164318642488020467735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227874109545761658680311823 341811164318642488020467735)
          ·
            refine ⟨512716746477963732030701603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341811164318642488020467735 512716746477963732030701603)
            ·
              refine ⟨769075119716945598046052405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512716746477963732030701603 769075119716945598046052405)
              ·
                refine ⟨72100792473463649816817413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 769075119716945598046052405 72100792473463649816817413)
                ·
                  refine ⟨13518898588774434340653265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72100792473463649816817413 13518898588774434340653265)
                  ·
                    refine ⟨10139173941580825755489949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13518898588774434340653265 10139173941580825755489949)
                    ·
                      refine ⟨3802190228092809658308731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10139173941580825755489949 3802190228092809658308731)
                      ·
                        rfl

theorem cell23_7404739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_7404739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404739 prefixEnd_7404739 := by exact prefixLift 7404739
  have htrace : WordTrace (prefixWord ++ tailWord_7404739) baseStart_7404739 baseEnd_7404739 := by
    simpa [prefixWord, tailWord_7404739, baseEnd_7404739] using wordTrace_append hprefix tailTrace_7404739
  have hstable : (prefixWord ++ tailWord_7404739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404739).length < 2 ^ (prefixWord ++ tailWord_7404739).sum := by decide
  have hdescent : baseEnd_7404739 < baseStart_7404739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404759 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 6]
def baseStart_7404759 : Nat := 118140960795 + 7404759 * 2 ^ 59
def prefixEnd_7404759 : Nat := 4983230072969 + 3 ^ 40 * 7404759 * 2
def baseEnd_7404759 : Nat := 422466721967322175562071

theorem tailTrace_7404759 : CollatzResearch.WordTrace tailWord_7404759 prefixEnd_7404759 422466721967322175562071 := by
  unfold tailWord_7404759
  simp only [CollatzResearch.WordTrace]
  refine ⟨270073748180830249999801331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180049165453886833333200887 270073748180830249999801331)
  ·
    refine ⟨405110622271245374999701997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270073748180830249999801331 405110622271245374999701997)
    ·
      refine ⟨151916483351717015624888249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405110622271245374999701997 151916483351717015624888249)
      ·
        refine ⟨113937362513787761718666187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151916483351717015624888249 113937362513787761718666187)
        ·
          refine ⟨170906043770681642577999281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113937362513787761718666187 170906043770681642577999281)
          ·
            refine ⟨128179532828011231933499461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170906043770681642577999281 128179532828011231933499461)
            ·
              refine ⟨24033662405252105987531149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128179532828011231933499461 24033662405252105987531149)
              ·
                refine ⟨9012623401969539745324181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24033662405252105987531149 9012623401969539745324181)
                ·
                  refine ⟨422466721967322175562071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9012623401969539745324181 422466721967322175562071)
                  ·
                    rfl

theorem cell23_7404759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 6].length) (baseStart_7404759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404759 prefixEnd_7404759 := by exact prefixLift 7404759
  have htrace : WordTrace (prefixWord ++ tailWord_7404759) baseStart_7404759 baseEnd_7404759 := by
    simpa [prefixWord, tailWord_7404759, baseEnd_7404759] using wordTrace_append hprefix tailTrace_7404759
  have hstable : (prefixWord ++ tailWord_7404759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404759).length < 2 ^ (prefixWord ++ tailWord_7404759).sum := by decide
  have hdescent : baseEnd_7404759 < baseStart_7404759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404803 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 3]
def baseStart_7404803 : Nat := 118140960795 + 7404803 * 2 ^ 59
def prefixEnd_7404803 : Nat := 4983230072969 + 3 ^ 40 * 7404803 * 2
def baseEnd_7404803 : Nat := 3802223090854697407908437

theorem tailTrace_7404803 : CollatzResearch.WordTrace tailWord_7404803 prefixEnd_7404803 3802223090854697407908437 := by
  unfold tailWord_7404803
  simp only [CollatzResearch.WordTrace]
  refine ⟨270075352992670845514403063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180050235328447230342935375 270075352992670845514403063)
  ·
    refine ⟨405113029489006268271604595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270075352992670845514403063 405113029489006268271604595)
    ·
      refine ⟨607669544233509402407406893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405113029489006268271604595 607669544233509402407406893)
      ·
        refine ⟨227876079087566025902777585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607669544233509402407406893 227876079087566025902777585)
        ·
          refine ⟨170907059315674519427083189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227876079087566025902777585 170907059315674519427083189)
          ·
            refine ⟨16022536810844486196289049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170907059315674519427083189 16022536810844486196289049)
            ·
              refine ⟨12016902608133364647216787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16022536810844486196289049 12016902608133364647216787)
              ·
                refine ⟨18025353912200046970825181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12016902608133364647216787 18025353912200046970825181)
                ·
                  refine ⟨6759507717075017614059443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18025353912200046970825181 6759507717075017614059443)
                  ·
                    refine ⟨10139261575612526421089165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6759507717075017614059443 10139261575612526421089165)
                    ·
                      refine ⟨3802223090854697407908437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10139261575612526421089165 3802223090854697407908437)
                      ·
                        rfl

theorem cell23_7404803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_7404803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404803 prefixEnd_7404803 := by exact prefixLift 7404803
  have htrace : WordTrace (prefixWord ++ tailWord_7404803) baseStart_7404803 baseEnd_7404803 := by
    simpa [prefixWord, tailWord_7404803, baseEnd_7404803] using wordTrace_append hprefix tailTrace_7404803
  have hstable : (prefixWord ++ tailWord_7404803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404803).length < 2 ^ (prefixWord ++ tailWord_7404803).sum := by decide
  have hdescent : baseEnd_7404803 < baseStart_7404803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404836 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_7404836 : Nat := 118140960795 + 7404836 * 2 ^ 59
def prefixEnd_7404836 : Nat := 4983230072969 + 3 ^ 40 * 7404836 * 2
def baseEnd_7404836 : Nat := 1267413345238765259598595

theorem tailTrace_7404836 : CollatzResearch.WordTrace tailWord_7404836 prefixEnd_7404836 1267413345238765259598595 := by
  unfold tailWord_7404836
  simp only [CollatzResearch.WordTrace]
  refine ⟨135038278300775646075177181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180051037734367528100236241 135038278300775646075177181)
  ·
    refine ⟨50639354362790867278191443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135038278300775646075177181 50639354362790867278191443)
    ·
      refine ⟨75959031544186300917287165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50639354362790867278191443 75959031544186300917287165)
      ·
        refine ⟨28484636829069862843982687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75959031544186300917287165 28484636829069862843982687)
        ·
          refine ⟨42726955243604794265974031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28484636829069862843982687 42726955243604794265974031)
          ·
            refine ⟨64090432865407191398961047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42726955243604794265974031 64090432865407191398961047)
            ·
              refine ⟨96135649298110787098441571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64090432865407191398961047 96135649298110787098441571)
              ·
                refine ⟨144203473947166180647662357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96135649298110787098441571 144203473947166180647662357)
                ·
                  refine ⟨6759537841273414717859173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144203473947166180647662357 6759537841273414717859173)
                  ·
                    refine ⟨1267413345238765259598595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6759537841273414717859173 1267413345238765259598595)
                    ·
                      rfl

theorem cell23_7404836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_7404836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404836 prefixEnd_7404836 := by exact prefixLift 7404836
  have htrace : WordTrace (prefixWord ++ tailWord_7404836) baseStart_7404836 baseEnd_7404836 := by
    simpa [prefixWord, tailWord_7404836, baseEnd_7404836] using wordTrace_append hprefix tailTrace_7404836
  have hstable : (prefixWord ++ tailWord_7404836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404836).length < 2 ^ (prefixWord ++ tailWord_7404836).sum := by decide
  have hdescent : baseEnd_7404836 < baseStart_7404836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404837 : List Nat := [1, 3, 1, 2, 4, 3, 1, 3, 1, 1, 3]
def baseStart_7404837 : Nat := 118140960795 + 7404837 * 2 ^ 59
def prefixEnd_7404837 : Nat := 4983230072969 + 3 ^ 40 * 7404837 * 2
def baseEnd_7404837 : Nat := 3802240549196950274883281

theorem tailTrace_7404837 : CollatzResearch.WordTrace tailWord_7404837 prefixEnd_7404837 3802240549196950274883281 := by
  unfold tailWord_7404837
  simp only [CollatzResearch.WordTrace]
  refine ⟨270076593074547669321140765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180051062049698446214093843 270076593074547669321140765)
  ·
    refine ⟨101278722402955375995427787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270076593074547669321140765 101278722402955375995427787)
    ·
      refine ⟨151918083604433063993141681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101278722402955375995427787 151918083604433063993141681)
      ·
        refine ⟨113938562703324797994856261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151918083604433063993141681 113938562703324797994856261)
        ·
          refine ⟨21363480506873399624035549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113938562703324797994856261 21363480506873399624035549)
          ·
            refine ⟨8011305190077524859013331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21363480506873399624035549 8011305190077524859013331)
            ·
              refine ⟨12016957785116287288519997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8011305190077524859013331 12016957785116287288519997)
              ·
                refine ⟨4506359169418607733194999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12016957785116287288519997 4506359169418607733194999)
                ·
                  refine ⟨6759538754127911599792499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506359169418607733194999 6759538754127911599792499)
                  ·
                    refine ⟨10139308131191867399688749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6759538754127911599792499 10139308131191867399688749)
                    ·
                      refine ⟨3802240549196950274883281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10139308131191867399688749 3802240549196950274883281)
                      ·
                        rfl

theorem cell23_7404837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_7404837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404837 prefixEnd_7404837 := by exact prefixLift 7404837
  have htrace : WordTrace (prefixWord ++ tailWord_7404837) baseStart_7404837 baseEnd_7404837 := by
    simpa [prefixWord, tailWord_7404837, baseEnd_7404837] using wordTrace_append hprefix tailTrace_7404837
  have hstable : (prefixWord ++ tailWord_7404837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404837).length < 2 ^ (prefixWord ++ tailWord_7404837).sum := by decide
  have hdescent : baseEnd_7404837 < baseStart_7404837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404849 : List Nat := [1, 2, 2, 3, 3, 1, 11]
def baseStart_7404849 : Nat := 118140960795 + 7404849 * 2 ^ 59
def prefixEnd_7404849 : Nat := 4983230072969 + 3 ^ 40 * 7404849 * 2
def baseEnd_7404849 : Nat := 46941317419318570715225

theorem tailTrace_7404849 : CollatzResearch.WordTrace tailWord_7404849 prefixEnd_7404849 46941317419318570715225 := by
  unfold tailWord_7404849
  simp only [CollatzResearch.WordTrace]
  refine ⟨270077030750504195370577601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180051353833669463580385067 270077030750504195370577601)
  ·
    refine ⟨202557773062878146527933201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270077030750504195370577601 202557773062878146527933201)
    ·
      refine ⟨151918329797158609895949901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202557773062878146527933201 151918329797158609895949901)
      ·
        refine ⟨56969373673934478710981213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151918329797158609895949901 56969373673934478710981213)
        ·
          refine ⟨21363515127725429516617955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56969373673934478710981213 21363515127725429516617955)
          ·
            refine ⟨32045272691588144274926933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21363515127725429516617955 32045272691588144274926933)
            ·
              refine ⟨46941317419318570715225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32045272691588144274926933 46941317419318570715225)
              ·
                rfl

theorem cell23_7404849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 11].length) (baseStart_7404849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404849 prefixEnd_7404849 := by exact prefixLift 7404849
  have htrace : WordTrace (prefixWord ++ tailWord_7404849) baseStart_7404849 baseEnd_7404849 := by
    simpa [prefixWord, tailWord_7404849, baseEnd_7404849] using wordTrace_append hprefix tailTrace_7404849
  have hstable : (prefixWord ++ tailWord_7404849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404849).length < 2 ^ (prefixWord ++ tailWord_7404849).sum := by decide
  have hdescent : baseEnd_7404849 < baseStart_7404849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404854 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7404854 : Nat := 118140960795 + 7404854 * 2 ^ 59
def prefixEnd_7404854 : Nat := 4983230072969 + 3 ^ 40 * 7404854 * 2
def baseEnd_7404854 : Nat := 3802249278368076708370703

theorem tailTrace_7404854 : CollatzResearch.WordTrace tailWord_7404854 prefixEnd_7404854 3802249278368076708370703 := by
  unfold tailWord_7404854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16879825819717880076531851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180051475410324054149673077 16879825819717880076531851)
  ·
    refine ⟨25319738729576820114797777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16879825819717880076531851 25319738729576820114797777)
    ·
      refine ⟨18989804047182615086098333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25319738729576820114797777 18989804047182615086098333)
      ·
        refine ⟨7121176517693480657286875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18989804047182615086098333 7121176517693480657286875)
        ·
          refine ⟨10681764776540220985930313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121176517693480657286875 10681764776540220985930313)
          ·
            refine ⟨8011323582405165739447735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10681764776540220985930313 8011323582405165739447735)
            ·
              refine ⟨12016985373607748609171603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8011323582405165739447735 12016985373607748609171603)
              ·
                refine ⟨18025478060411622913757405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12016985373607748609171603 18025478060411622913757405)
                ·
                  refine ⟨6759554272654358592659027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18025478060411622913757405 6759554272654358592659027)
                  ·
                    refine ⟨10139331408981537888988541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6759554272654358592659027 10139331408981537888988541)
                    ·
                      refine ⟨3802249278368076708370703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10139331408981537888988541 3802249278368076708370703)
                      ·
                        rfl

theorem cell23_7404854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7404854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404854 prefixEnd_7404854 := by exact prefixLift 7404854
  have htrace : WordTrace (prefixWord ++ tailWord_7404854) baseStart_7404854 baseEnd_7404854 := by
    simpa [prefixWord, tailWord_7404854, baseEnd_7404854] using wordTrace_append hprefix tailTrace_7404854
  have hstable : (prefixWord ++ tailWord_7404854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404854).length < 2 ^ (prefixWord ++ tailWord_7404854).sum := by decide
  have hdescent : baseEnd_7404854 < baseStart_7404854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404860 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_7404860 : Nat := 118140960795 + 7404860 * 2 ^ 59
def prefixEnd_7404860 : Nat := 4983230072969 + 3 ^ 40 * 7404860 * 2
def baseEnd_7404860 : Nat := 3802252359252003684895675

theorem tailTrace_7404860 : CollatzResearch.WordTrace tailWord_7404860 prefixEnd_7404860 3802252359252003684895675 := by
  unfold tailWord_7404860
  simp only [CollatzResearch.WordTrace]
  refine ⟨135038715976732172124614017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180051621302309562832818689 135038715976732172124614017)
  ·
    refine ⟨101279036982549129093460513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135038715976732172124614017 101279036982549129093460513)
    ·
      refine ⟨75959277736911846820095385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101279036982549129093460513 75959277736911846820095385)
      ·
        refine ⟨56969458302683885115071539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75959277736911846820095385 56969458302683885115071539)
        ·
          refine ⟨85454187454025827672607309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56969458302683885115071539 85454187454025827672607309)
          ·
            refine ⟨32045320295259685377227741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85454187454025827672607309 32045320295259685377227741)
            ·
              refine ⟨12016995110722382016460403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32045320295259685377227741 12016995110722382016460403)
              ·
                refine ⟨18025492666083573024690605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12016995110722382016460403 18025492666083573024690605)
                ·
                  refine ⟨6759559749781339884258977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18025492666083573024690605 6759559749781339884258977)
                  ·
                    refine ⟨5069669812336004913194233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6759559749781339884258977 5069669812336004913194233)
                    ·
                      refine ⟨3802252359252003684895675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069669812336004913194233 3802252359252003684895675)
                      ·
                        rfl

theorem cell23_7404860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_7404860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404860 prefixEnd_7404860 := by exact prefixLift 7404860
  have htrace : WordTrace (prefixWord ++ tailWord_7404860) baseStart_7404860 baseEnd_7404860 := by
    simpa [prefixWord, tailWord_7404860, baseEnd_7404860] using wordTrace_append hprefix tailTrace_7404860
  have hstable : (prefixWord ++ tailWord_7404860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404860).length < 2 ^ (prefixWord ++ tailWord_7404860).sum := by decide
  have hdescent : baseEnd_7404860 < baseStart_7404860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404889 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_7404889 : Nat := 118140960795 + 7404889 * 2 ^ 59
def prefixEnd_7404889 : Nat := 4983230072969 + 3 ^ 40 * 7404889 * 2
def baseEnd_7404889 : Nat := 3802267250190984071433041

theorem tailTrace_7404889 : CollatzResearch.WordTrace tailWord_7404889 prefixEnd_7404889 3802267250190984071433041 := by
  unfold tailWord_7404889
  simp only [CollatzResearch.WordTrace]
  refine ⟨270078489670359282202033721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180052326446906188134689147 270078489670359282202033721)
  ·
    refine ⟨202558867252769461651525291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270078489670359282202033721 202558867252769461651525291)
    ·
      refine ⟨303838300879154192477287937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202558867252769461651525291 303838300879154192477287937)
      ·
        refine ⟨227878725659365644357965953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303838300879154192477287937 227878725659365644357965953)
        ·
          refine ⟨170909044244524233268474465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227878725659365644357965953 170909044244524233268474465)
          ·
            refine ⟨128181783183393174951355849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170909044244524233268474465 128181783183393174951355849)
            ·
              refine ⟨96136337387544881213516887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128181783183393174951355849 96136337387544881213516887)
              ·
                refine ⟨144204506081317321820275331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96136337387544881213516887 144204506081317321820275331)
                ·
                  refine ⟨216306759121975982730412997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144204506081317321820275331 216306759121975982730412997)
                  ·
                    refine ⟨40557517335370496761952437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216306759121975982730412997 40557517335370496761952437)
                    ·
                      refine ⟨3802267250190984071433041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40557517335370496761952437 3802267250190984071433041)
                      ·
                        rfl

theorem cell23_7404889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_7404889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404889 prefixEnd_7404889 := by exact prefixLift 7404889
  have htrace : WordTrace (prefixWord ++ tailWord_7404889) baseStart_7404889 baseEnd_7404889 := by
    simpa [prefixWord, tailWord_7404889, baseEnd_7404889] using wordTrace_append hprefix tailTrace_7404889
  have hstable : (prefixWord ++ tailWord_7404889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404889).length < 2 ^ (prefixWord ++ tailWord_7404889).sum := by decide
  have hdescent : baseEnd_7404889 < baseStart_7404889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404933 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 1, 4, 2]
def baseStart_7404933 : Nat := 118140960795 + 7404933 * 2 ^ 59
def prefixEnd_7404933 : Nat := 4983230072969 + 3 ^ 40 * 7404933 * 2
def baseEnd_7404933 : Nat := 3802289843339781899282839

theorem tailTrace_7404933 : CollatzResearch.WordTrace tailWord_7404933 prefixEnd_7404933 3802289843339781899282839 := by
  unfold tailWord_7404933
  simp only [CollatzResearch.WordTrace]
  refine ⟨270080094482199877716635453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180053396321466585144423635 270080094482199877716635453)
  ·
    refine ⟨101280035430824954143738295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270080094482199877716635453 101280035430824954143738295)
    ·
      refine ⟨151920053146237431215607443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101280035430824954143738295 151920053146237431215607443)
      ·
        refine ⟨227880079719356146823411165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151920053146237431215607443 227880079719356146823411165)
        ·
          refine ⟨85455029894758555058779187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227880079719356146823411165 85455029894758555058779187)
          ·
            refine ⟨128182544842137832588168781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85455029894758555058779187 128182544842137832588168781)
            ·
              refine ⟨48068454315801687220563293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128182544842137832588168781 48068454315801687220563293)
              ·
                refine ⟨18025670368425632707711235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48068454315801687220563293 18025670368425632707711235)
                ·
                  refine ⟨27038505552638449061566853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18025670368425632707711235 27038505552638449061566853)
                  ·
                    refine ⟨5069719791119709199043785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27038505552638449061566853 5069719791119709199043785)
                    ·
                      refine ⟨3802289843339781899282839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069719791119709199043785 3802289843339781899282839)
                      ·
                        rfl

theorem cell23_7404933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_7404933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404933 prefixEnd_7404933 := by exact prefixLift 7404933
  have htrace : WordTrace (prefixWord ++ tailWord_7404933) baseStart_7404933 baseEnd_7404933 := by
    simpa [prefixWord, tailWord_7404933, baseEnd_7404933] using wordTrace_append hprefix tailTrace_7404933
  have hstable : (prefixWord ++ tailWord_7404933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404933).length < 2 ^ (prefixWord ++ tailWord_7404933).sum := by decide
  have hdescent : baseEnd_7404933 < baseStart_7404933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404973 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 7]
def baseStart_7404973 : Nat := 118140960795 + 7404973 * 2 ^ 59
def prefixEnd_7404973 : Nat := 4983230072969 + 3 ^ 40 * 7404973 * 2
def baseEnd_7404973 : Nat := 422478931396217971420295

theorem tailTrace_7404973 : CollatzResearch.WordTrace tailWord_7404973 prefixEnd_7404973 422478931396217971420295 := by
  unfold tailWord_7404973
  simp only [CollatzResearch.WordTrace]
  refine ⟨270081553402054964548091573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180054368934703309698727715 270081553402054964548091573)
  ·
    refine ⟨25320145631442652926383585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270081553402054964548091573 25320145631442652926383585)
    ·
      refine ⟨18990109223581989694787689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25320145631442652926383585 18990109223581989694787689)
      ·
        refine ⟨14242581917686492271090767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18990109223581989694787689 14242581917686492271090767)
        ·
          refine ⟨21363872876529738406636151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14242581917686492271090767 21363872876529738406636151)
          ·
            refine ⟨32045809314794607609954227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21363872876529738406636151 32045809314794607609954227)
            ·
              refine ⟨48068713972191911414931341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32045809314794607609954227 48068713972191911414931341)
              ·
                refine ⟨18025767739571966780599253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48068713972191911414931341 18025767739571966780599253)
                ·
                  refine ⟨422478931396217971420295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18025767739571966780599253 422478931396217971420295)
                  ·
                    rfl

theorem cell23_7404973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_7404973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7404973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7404973 prefixEnd_7404973 := by exact prefixLift 7404973
  have htrace : WordTrace (prefixWord ++ tailWord_7404973) baseStart_7404973 baseEnd_7404973 := by
    simpa [prefixWord, tailWord_7404973, baseEnd_7404973] using wordTrace_append hprefix tailTrace_7404973
  have hstable : (prefixWord ++ tailWord_7404973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404973).length < 2 ^ (prefixWord ++ tailWord_7404973).sum := by decide
  have hdescent : baseEnd_7404973 < baseStart_7404973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405023 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_7405023 : Nat := 118140960795 + 7405023 * 2 ^ 59
def prefixEnd_7405023 : Nat := 4983230072969 + 3 ^ 40 * 7405023 * 2
def baseEnd_7405023 : Nat := 3802336056598686547157425

theorem tailTrace_7405023 : CollatzResearch.WordTrace tailWord_7405023 prefixEnd_7405023 3802336056598686547157425 := by
  unfold tailWord_7405023
  simp only [CollatzResearch.WordTrace]
  refine ⟨270083377051873823087411723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180055584701249215391607815 270083377051873823087411723)
  ·
    refine ⟨405125065577810734631117585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270083377051873823087411723 405125065577810734631117585)
    ·
      refine ⟨303843799183358050973338189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405125065577810734631117585 303843799183358050973338189)
      ·
        refine ⟨113941424693759269115001821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303843799183358050973338189 113941424693759269115001821)
        ·
          refine ⟨42728034260159725918125683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113941424693759269115001821 42728034260159725918125683)
          ·
            refine ⟨64092051390239588877188525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42728034260159725918125683 64092051390239588877188525)
            ·
              refine ⟨24034519271339845828945697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64092051390239588877188525 24034519271339845828945697)
              ·
                refine ⟨18025889453504884371709273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24034519271339845828945697 18025889453504884371709273)
                ·
                  refine ⟨13519417090128663278781955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18025889453504884371709273 13519417090128663278781955)
                  ·
                    refine ⟨20279125635192994918172933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13519417090128663278781955 20279125635192994918172933)
                    ·
                      refine ⟨3802336056598686547157425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20279125635192994918172933 3802336056598686547157425)
                      ·
                        rfl

theorem cell23_7405023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_7405023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405023 prefixEnd_7405023 := by exact prefixLift 7405023
  have htrace : WordTrace (prefixWord ++ tailWord_7405023) baseStart_7405023 baseEnd_7405023 := by
    simpa [prefixWord, tailWord_7405023, baseEnd_7405023] using wordTrace_append hprefix tailTrace_7405023
  have hstable : (prefixWord ++ tailWord_7405023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405023).length < 2 ^ (prefixWord ++ tailWord_7405023).sum := by decide
  have hdescent : baseEnd_7405023 < baseStart_7405023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405036 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_7405036 : Nat := 118140960795 + 7405036 * 2 ^ 59
def prefixEnd_7405036 : Nat := 4983230072969 + 3 ^ 40 * 7405036 * 2
def baseEnd_7405036 : Nat := 3802342731847194996294865

theorem tailTrace_7405036 : CollatzResearch.WordTrace tailWord_7405036 prefixEnd_7405036 3802342731847194996294865 := by
  unfold tailWord_7405036
  simp only [CollatzResearch.WordTrace]
  refine ⟨135041925600413363153817481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180055900800551150871756641 135041925600413363153817481)
  ·
    refine ⟨101281444200310022365363111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135041925600413363153817481 101281444200310022365363111)
    ·
      refine ⟨151922166300465033548044667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101281444200310022365363111 151922166300465033548044667)
      ·
        refine ⟨227883249450697550322067001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151922166300465033548044667 227883249450697550322067001)
        ·
          refine ⟨170912437088023162741550251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227883249450697550322067001 170912437088023162741550251)
          ·
            refine ⟨256368655632034744112325377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170912437088023162741550251 256368655632034744112325377)
            ·
              refine ⟨192276491724026058084244033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256368655632034744112325377 192276491724026058084244033)
              ·
                refine ⟨144207368793019543563183025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192276491724026058084244033 144207368793019543563183025)
                ·
                  refine ⟨108155526594764657672387269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144207368793019543563183025 108155526594764657672387269)
                  ·
                    refine ⟨20279161236518373313572613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108155526594764657672387269 20279161236518373313572613)
                    ·
                      refine ⟨3802342731847194996294865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20279161236518373313572613 3802342731847194996294865)
                      ·
                        rfl

theorem cell23_7405036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_7405036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405036 prefixEnd_7405036 := by exact prefixLift 7405036
  have htrace : WordTrace (prefixWord ++ tailWord_7405036) baseStart_7405036 baseEnd_7405036 := by
    simpa [prefixWord, tailWord_7405036, baseEnd_7405036] using wordTrace_append hprefix tailTrace_7405036
  have hstable : (prefixWord ++ tailWord_7405036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405036).length < 2 ^ (prefixWord ++ tailWord_7405036).sum := by decide
  have hdescent : baseEnd_7405036 < baseStart_7405036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405080 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 6]
def baseStart_7405080 : Nat := 118140960795 + 7405080 * 2 ^ 59
def prefixEnd_7405080 : Nat := 4983230072969 + 3 ^ 40 * 7405080 * 2
def baseEnd_7405080 : Nat := 422485036110665869349407

theorem tailTrace_7405080 : CollatzResearch.WordTrace tailWord_7405080 prefixEnd_7405080 422485036110665869349407 := by
  unfold tailWord_7405080
  simp only [CollatzResearch.WordTrace]
  refine ⟨135042728006333660911118347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180056970675111547881491129 135042728006333660911118347)
  ·
    refine ⟨202564092009500491366677521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135042728006333660911118347 202564092009500491366677521)
    ·
      refine ⟨151923069007125368525008141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202564092009500491366677521 151923069007125368525008141)
      ·
        refine ⟨56971150877672013196878053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151923069007125368525008141 56971150877672013196878053)
        ·
          refine ⟨10682090789563502474414635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56971150877672013196878053 10682090789563502474414635)
          ·
            refine ⟨16023136184345253711621953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10682090789563502474414635 16023136184345253711621953)
            ·
              refine ⟨12017352138258940283716465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16023136184345253711621953 12017352138258940283716465)
              ·
                refine ⟨9013014103694205212787349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12017352138258940283716465 9013014103694205212787349)
                ·
                  refine ⟨422485036110665869349407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9013014103694205212787349 422485036110665869349407)
                  ·
                    rfl

theorem cell23_7405080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 6].length) (baseStart_7405080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405080 prefixEnd_7405080 := by exact prefixLift 7405080
  have htrace : WordTrace (prefixWord ++ tailWord_7405080) baseStart_7405080 baseEnd_7405080 := by
    simpa [prefixWord, tailWord_7405080, baseEnd_7405080] using wordTrace_append hprefix tailTrace_7405080
  have hstable : (prefixWord ++ tailWord_7405080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405080).length < 2 ^ (prefixWord ++ tailWord_7405080).sum := by decide
  have hdescent : baseEnd_7405080 < baseStart_7405080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405117 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_7405117 : Nat := 118140960795 + 7405117 * 2 ^ 59
def prefixEnd_7405117 : Nat := 4983230072969 + 3 ^ 40 * 7405117 * 2
def baseEnd_7405117 : Nat := 3802384323780209179381993

theorem tailTrace_7405117 : CollatzResearch.WordTrace tailWord_7405117 prefixEnd_7405117 3802384323780209179381993 := by
  unfold tailWord_7405117
  simp only [CollatzResearch.WordTrace]
  refine ⟨270086805513533277141333605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180057870342355518094222403 270086805513533277141333605)
  ·
    refine ⟨50641276033787489464000051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270086805513533277141333605 50641276033787489464000051)
    ·
      refine ⟨75961914050681234196000077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50641276033787489464000051 75961914050681234196000077)
      ·
        refine ⟨28485717769005462823500029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75961914050681234196000077 28485717769005462823500029)
        ·
          refine ⟨10682144163377048558812511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28485717769005462823500029 10682144163377048558812511)
          ·
            refine ⟨16023216245065572838218767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10682144163377048558812511 16023216245065572838218767)
            ·
              refine ⟨24034824367598359257328151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16023216245065572838218767 24034824367598359257328151)
              ·
                refine ⟨36052236551397538885992227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24034824367598359257328151 36052236551397538885992227)
                ·
                  refine ⟨54078354827096308328988341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36052236551397538885992227 54078354827096308328988341)
                  ·
                    refine ⟨5069845765040278905842657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54078354827096308328988341 5069845765040278905842657)
                    ·
                      refine ⟨3802384323780209179381993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069845765040278905842657 3802384323780209179381993)
                      ·
                        rfl

theorem cell23_7405117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_7405117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405117 prefixEnd_7405117 := by exact prefixLift 7405117
  have htrace : WordTrace (prefixWord ++ tailWord_7405117) baseStart_7405117 baseEnd_7405117 := by
    simpa [prefixWord, tailWord_7405117, baseEnd_7405117] using wordTrace_append hprefix tailTrace_7405117
  have hstable : (prefixWord ++ tailWord_7405117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405117).length < 2 ^ (prefixWord ++ tailWord_7405117).sum := by decide
  have hdescent : baseEnd_7405117 < baseStart_7405117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405130 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_7405130 : Nat := 118140960795 + 7405130 * 2 ^ 59
def prefixEnd_7405130 : Nat := 4983230072969 + 3 ^ 40 * 7405130 * 2
def baseEnd_7405130 : Nat := 3802390999028717628519433

theorem tailTrace_7405130 : CollatzResearch.WordTrace tailWord_7405130 prefixEnd_7405130 3802390999028717628519433 := by
  unfold tailWord_7405130
  simp only [CollatzResearch.WordTrace]
  refine ⟨67521819915621545090389211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180058186441657453574371229 67521819915621545090389211)
  ·
    refine ⟨101282729873432317635583817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67521819915621545090389211 101282729873432317635583817)
    ·
      refine ⟨75962047405074238226687863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101282729873432317635583817 75962047405074238226687863)
      ·
        refine ⟨113943071107611357340031795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75962047405074238226687863 113943071107611357340031795)
        ·
          refine ⟨170914606661417036010047693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113943071107611357340031795 170914606661417036010047693)
          ·
            refine ⟨64092977498031388503767885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170914606661417036010047693 64092977498031388503767885)
            ·
              refine ⟨24034866561761770688912957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64092977498031388503767885 24034866561761770688912957)
              ·
                refine ⟨9013074960660664008342359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24034866561761770688912957 9013074960660664008342359)
                ·
                  refine ⟨13519612440990996012513539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013074960660664008342359 13519612440990996012513539)
                  ·
                    refine ⟨20279418661486494018770309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13519612440990996012513539 20279418661486494018770309)
                    ·
                      refine ⟨3802390999028717628519433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20279418661486494018770309 3802390999028717628519433)
                      ·
                        rfl

theorem cell23_7405130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_7405130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405130 prefixEnd_7405130 := by exact prefixLift 7405130
  have htrace : WordTrace (prefixWord ++ tailWord_7405130) baseStart_7405130 baseEnd_7405130 := by
    simpa [prefixWord, tailWord_7405130, baseEnd_7405130] using wordTrace_append hprefix tailTrace_7405130
  have hstable : (prefixWord ++ tailWord_7405130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405130).length < 2 ^ (prefixWord ++ tailWord_7405130).sum := by decide
  have hdescent : baseEnd_7405130 < baseStart_7405130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405136 : List Nat := [2, 1, 1, 1, 1, 3, 14]
def baseStart_7405136 : Nat := 118140960795 + 7405136 * 2 ^ 59
def prefixEnd_7405136 : Nat := 4983230072969 + 3 ^ 40 * 7405136 * 2
def baseEnd_7405136 : Nat := 46943136789044995124005

theorem tailTrace_7405136 : CollatzResearch.WordTrace tailWord_7405136 prefixEnd_7405136 46943136789044995124005 := by
  unfold tailWord_7405136
  simp only [CollatzResearch.WordTrace]
  refine ⟨135043749250232221693137631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180058332333642962257516841 135043749250232221693137631)
  ·
    refine ⟨202565623875348332539706447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135043749250232221693137631 202565623875348332539706447)
    ·
      refine ⟨303848435813022498809559671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202565623875348332539706447 303848435813022498809559671)
      ·
        refine ⟨455772653719533748214339507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303848435813022498809559671 455772653719533748214339507)
        ·
          refine ⟨683658980579300622321509261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455772653719533748214339507 683658980579300622321509261)
          ·
            refine ⟨256372117717237733370565973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683658980579300622321509261 256372117717237733370565973)
            ·
              refine ⟨46943136789044995124005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 256372117717237733370565973 46943136789044995124005)
              ·
                rfl

theorem cell23_7405136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 14].length) (baseStart_7405136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405136 prefixEnd_7405136 := by exact prefixLift 7405136
  have htrace : WordTrace (prefixWord ++ tailWord_7405136) baseStart_7405136 baseEnd_7405136 := by
    simpa [prefixWord, tailWord_7405136, baseEnd_7405136] using wordTrace_append hprefix tailTrace_7405136
  have hstable : (prefixWord ++ tailWord_7405136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405136).length < 2 ^ (prefixWord ++ tailWord_7405136).sum := by decide
  have hdescent : baseEnd_7405136 < baseStart_7405136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405140 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_7405140 : Nat := 118140960795 + 7405140 * 2 ^ 59
def prefixEnd_7405140 : Nat := 4983230072969 + 3 ^ 40 * 7405140 * 2
def baseEnd_7405140 : Nat := 1267465377945087529798129

theorem tailTrace_7405140 : CollatzResearch.WordTrace tailWord_7405140 prefixEnd_7405140 1267465377945087529798129 := by
  unfold tailWord_7405140
  simp only [CollatzResearch.WordTrace]
  refine ⟨135043822196224976034710437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180058429594966634712947249 135043822196224976034710437)
  ·
    refine ⟨25320716661792183006508207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135043822196224976034710437 25320716661792183006508207)
    ·
      refine ⟨37981074992688274509762311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25320716661792183006508207 37981074992688274509762311)
      ·
        refine ⟨56971612489032411764643467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37981074992688274509762311 56971612489032411764643467)
        ·
          refine ⟨85457418733548617646965201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56971612489032411764643467 85457418733548617646965201)
          ·
            refine ⟨64093064050161463235223901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85457418733548617646965201 64093064050161463235223901)
            ·
              refine ⟨24034899018810548713208963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64093064050161463235223901 24034899018810548713208963)
              ·
                refine ⟨36052348528215823069813445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24034899018810548713208963 36052348528215823069813445)
                ·
                  refine ⟨6759815349040466825590021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36052348528215823069813445 6759815349040466825590021)
                  ·
                    refine ⟨1267465377945087529798129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6759815349040466825590021 1267465377945087529798129)
                    ·
                      rfl

theorem cell23_7405140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_7405140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405140 prefixEnd_7405140 := by exact prefixLift 7405140
  have htrace : WordTrace (prefixWord ++ tailWord_7405140) baseStart_7405140 baseEnd_7405140 := by
    simpa [prefixWord, tailWord_7405140, baseEnd_7405140] using wordTrace_append hprefix tailTrace_7405140
  have hstable : (prefixWord ++ tailWord_7405140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405140).length < 2 ^ (prefixWord ++ tailWord_7405140).sum := by decide
  have hdescent : baseEnd_7405140 < baseStart_7405140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405160 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_7405160 : Nat := 118140960795 + 7405160 * 2 ^ 59
def prefixEnd_7405160 : Nat := 4983230072969 + 3 ^ 40 * 7405160 * 2
def baseEnd_7405160 : Nat := 3802406403448352511144295

theorem tailTrace_7405160 : CollatzResearch.WordTrace tailWord_7405160 prefixEnd_7405160 3802406403448352511144295 := by
  unfold tailWord_7405160
  simp only [CollatzResearch.WordTrace]
  refine ⟨135044186926188747742574467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180058915901584996990099289 135044186926188747742574467)
  ·
    refine ⟨202566280389283121613861701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135044186926188747742574467 202566280389283121613861701)
    ·
      refine ⟨37981177572990585302599069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202566280389283121613861701 37981177572990585302599069)
      ·
        refine ⟨14242941589871469488474651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37981177572990585302599069 14242941589871469488474651)
        ·
          refine ⟨21364412384807204232711977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14242941589871469488474651 21364412384807204232711977)
          ·
            refine ⟨16023309288605403174533983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21364412384807204232711977 16023309288605403174533983)
            ·
              refine ⟨24034963932908104761800975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16023309288605403174533983 24034963932908104761800975)
              ·
                refine ⟨36052445899362157142701463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24034963932908104761800975 36052445899362157142701463)
                ·
                  refine ⟨54078668849043235714052195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36052445899362157142701463 54078668849043235714052195)
                  ·
                    refine ⟨81118003273564853571078293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54078668849043235714052195 81118003273564853571078293)
                    ·
                      refine ⟨3802406403448352511144295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81118003273564853571078293 3802406403448352511144295)
                      ·
                        rfl

theorem cell23_7405160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_7405160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405160 prefixEnd_7405160 := by exact prefixLift 7405160
  have htrace : WordTrace (prefixWord ++ tailWord_7405160) baseStart_7405160 baseEnd_7405160 := by
    simpa [prefixWord, tailWord_7405160, baseEnd_7405160] using wordTrace_append hprefix tailTrace_7405160
  have hstable : (prefixWord ++ tailWord_7405160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405160).length < 2 ^ (prefixWord ++ tailWord_7405160).sum := by decide
  have hdescent : baseEnd_7405160 < baseStart_7405160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405170 : List Nat := [3, 2, 1, 2, 3, 1, 4, 7]
def baseStart_7405170 : Nat := 118140960795 + 7405170 * 2 ^ 59
def prefixEnd_7405170 : Nat := 4983230072969 + 3 ^ 40 * 7405170 * 2
def baseEnd_7405170 : Nat := 140830056972403610074787

theorem tailTrace_7405170 : CollatzResearch.WordTrace tailWord_7405170 prefixEnd_7405170 140830056972403610074787 := by
  unfold tailWord_7405170
  simp only [CollatzResearch.WordTrace]
  refine ⟨67522184645585316798253241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180059159054894178128675309 67522184645585316798253241)
  ·
    refine ⟨50641638484188987598689931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67522184645585316798253241 50641638484188987598689931)
    ·
      refine ⟨75962457726283481398034897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50641638484188987598689931 75962457726283481398034897)
      ·
        refine ⟨56971843294712611048526173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75962457726283481398034897 56971843294712611048526173)
        ·
          refine ⟨21364441235517229143197315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56971843294712611048526173 21364441235517229143197315)
          ·
            refine ⟨32046661853275843714795973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21364441235517229143197315 32046661853275843714795973)
            ·
              refine ⟨6008749097489220696524245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32046661853275843714795973 6008749097489220696524245)
              ·
                refine ⟨140830056972403610074787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6008749097489220696524245 140830056972403610074787)
                ·
                  rfl

theorem cell23_7405170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 7].length) (baseStart_7405170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405170 prefixEnd_7405170 := by exact prefixLift 7405170
  have htrace : WordTrace (prefixWord ++ tailWord_7405170) baseStart_7405170 baseEnd_7405170 := by
    simpa [prefixWord, tailWord_7405170, baseEnd_7405170] using wordTrace_append hprefix tailTrace_7405170
  have hstable : (prefixWord ++ tailWord_7405170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405170).length < 2 ^ (prefixWord ++ tailWord_7405170).sum := by decide
  have hdescent : baseEnd_7405170 < baseStart_7405170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405181 : List Nat := [1, 4, 1, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_7405181 : Nat := 118140960795 + 7405181 * 2 ^ 59
def prefixEnd_7405181 : Nat := 4983230072969 + 3 ^ 40 * 7405181 * 2
def baseEnd_7405181 : Nat := 3802417186542096928981699

theorem tailTrace_7405181 : CollatzResearch.WordTrace tailWord_7405181 prefixEnd_7405181 3802417186542096928981699 := by
  unfold tailWord_7405181
  simp only [CollatzResearch.WordTrace]
  refine ⟨270089139785301416071663397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180059426523534277381108931 270089139785301416071663397)
  ·
    refine ⟨50641713709744015513436887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270089139785301416071663397 50641713709744015513436887)
    ·
      refine ⟨75962570564616023270155331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50641713709744015513436887 75962570564616023270155331)
      ·
        refine ⟨113943855846924034905232997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75962570564616023270155331 113943855846924034905232997)
        ·
          refine ⟨21364472971298256544731187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113943855846924034905232997 21364472971298256544731187)
          ·
            refine ⟨32046709456947384817096781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21364472971298256544731187 32046709456947384817096781)
            ·
              refine ⟨12017516046355269306411293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32046709456947384817096781 12017516046355269306411293)
              ·
                refine ⟨4506568517383225989904235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12017516046355269306411293 4506568517383225989904235)
                ·
                  refine ⟨6759852776074838984856353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506568517383225989904235 6759852776074838984856353)
                  ·
                    refine ⟨5069889582056129238642265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6759852776074838984856353 5069889582056129238642265)
                    ·
                      refine ⟨3802417186542096928981699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069889582056129238642265 3802417186542096928981699)
                      ·
                        rfl

theorem cell23_7405181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_7405181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405181 prefixEnd_7405181 := by exact prefixLift 7405181
  have htrace : WordTrace (prefixWord ++ tailWord_7405181) baseStart_7405181 baseEnd_7405181 := by
    simpa [prefixWord, tailWord_7405181, baseEnd_7405181] using wordTrace_append hprefix tailTrace_7405181
  have hstable : (prefixWord ++ tailWord_7405181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405181).length < 2 ^ (prefixWord ++ tailWord_7405181).sum := by decide
  have hdescent : baseEnd_7405181 < baseStart_7405181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405198 : List Nat := [4, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7405198 : Nat := 118140960795 + 7405198 * 2 ^ 59
def prefixEnd_7405198 : Nat := 4983230072969 + 3 ^ 40 * 7405198 * 2
def baseEnd_7405198 : Nat := 3802425915713223362469121

theorem tailTrace_7405198 : CollatzResearch.WordTrace tailWord_7405198 prefixEnd_7405198 3802425915713223362469121 := by
  unfold tailWord_7405198
  simp only [CollatzResearch.WordTrace]
  refine ⟨33761219978279978496879031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180059839884159885316688165 33761219978279978496879031)
  ·
    refine ⟨50641829967419967745318547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33761219978279978496879031 50641829967419967745318547)
    ·
      refine ⟨75962744951129951617977821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50641829967419967745318547 75962744951129951617977821)
      ·
        refine ⟨28486029356673731856741683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75962744951129951617977821 28486029356673731856741683)
        ·
          refine ⟨42729044035010597785112525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28486029356673731856741683 42729044035010597785112525)
          ·
            refine ⟨16023391513128974169417197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42729044035010597785112525 16023391513128974169417197)
            ·
              refine ⟨6008771817423365313531449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16023391513128974169417197 6008771817423365313531449)
              ·
                refine ⟨4506578863067523985148587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6008771817423365313531449 4506578863067523985148587)
                ·
                  refine ⟨6759868294601285977722881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506578863067523985148587 6759868294601285977722881)
                  ·
                    refine ⟨5069901220950964483292161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6759868294601285977722881 5069901220950964483292161)
                    ·
                      refine ⟨3802425915713223362469121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5069901220950964483292161 3802425915713223362469121)
                      ·
                        rfl

theorem cell23_7405198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7405198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405198 prefixEnd_7405198 := by exact prefixLift 7405198
  have htrace : WordTrace (prefixWord ++ tailWord_7405198) baseStart_7405198 baseEnd_7405198 := by
    simpa [prefixWord, tailWord_7405198, baseEnd_7405198] using wordTrace_append hprefix tailTrace_7405198
  have hstable : (prefixWord ++ tailWord_7405198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405198).length < 2 ^ (prefixWord ++ tailWord_7405198).sum := by decide
  have hdescent : baseEnd_7405198 < baseStart_7405198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405213 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_7405213 : Nat := 118140960795 + 7405213 * 2 ^ 59
def prefixEnd_7405213 : Nat := 4983230072969 + 3 ^ 40 * 7405213 * 2
def baseEnd_7405213 : Nat := 1267477872641013601260517

theorem tailTrace_7405213 : CollatzResearch.WordTrace tailWord_7405213 prefixEnd_7405213 1267477872641013601260517 := by
  unfold tailWord_7405213
  simp only [CollatzResearch.WordTrace]
  refine ⟨270090306921185485536828293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180060204614123657024552195 270090306921185485536828293)
  ·
    refine ⟨50641932547722278538155305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270090306921185485536828293 50641932547722278538155305)
    ·
      refine ⟨37981449410791708903616479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50641932547722278538155305 37981449410791708903616479)
      ·
        refine ⟨56972174116187563355424719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37981449410791708903616479 56972174116187563355424719)
        ·
          refine ⟨85458261174281345033137079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56972174116187563355424719 85458261174281345033137079)
          ·
            refine ⟨128187391761422017549705619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85458261174281345033137079 128187391761422017549705619)
            ·
              refine ⟨192281087642133026324558429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128187391761422017549705619 192281087642133026324558429)
              ·
                refine ⟨72105407865799884871709411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192281087642133026324558429 72105407865799884871709411)
                ·
                  refine ⟨108158111798699827307564117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72105407865799884871709411 108158111798699827307564117)
                  ·
                    refine ⟨1267477872641013601260517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108158111798699827307564117 1267477872641013601260517)
                    ·
                      rfl

theorem cell23_7405213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_7405213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405213 prefixEnd_7405213 := by exact prefixLift 7405213
  have htrace : WordTrace (prefixWord ++ tailWord_7405213) baseStart_7405213 baseEnd_7405213 := by
    simpa [prefixWord, tailWord_7405213, baseEnd_7405213] using wordTrace_append hprefix tailTrace_7405213
  have hstable : (prefixWord ++ tailWord_7405213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405213).length < 2 ^ (prefixWord ++ tailWord_7405213).sum := by decide
  have hdescent : baseEnd_7405213 < baseStart_7405213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405218 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_7405218 : Nat := 118140960795 + 7405218 * 2 ^ 59
def prefixEnd_7405218 : Nat := 4983230072969 + 3 ^ 40 * 7405218 * 2
def baseEnd_7405218 : Nat := 3802436185326313284219029

theorem tailTrace_7405218 : CollatzResearch.WordTrace tailWord_7405218 prefixEnd_7405218 3802436185326313284219029 := by
  unfold tailWord_7405218
  simp only [CollatzResearch.WordTrace]
  refine ⟨67522622321541842847690077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180060326190778247593840205 67522622321541842847690077)
  ·
    refine ⟨25320983370578191067883779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67522622321541842847690077 25320983370578191067883779)
    ·
      refine ⟨37981475055867286601825669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25320983370578191067883779 37981475055867286601825669)
      ·
        refine ⟨7121526572975116237842313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37981475055867286601825669 7121526572975116237842313)
        ·
          refine ⟨5341144929731337178381735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7121526572975116237842313 5341144929731337178381735)
          ·
            refine ⟨8011717394597005767572603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5341144929731337178381735 8011717394597005767572603)
            ·
              refine ⟨12017576091895508651358905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8011717394597005767572603 12017576091895508651358905)
              ·
                refine ⟨9013182068921631488519179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12017576091895508651358905 9013182068921631488519179)
                ·
                  refine ⟨13519773103382447232778769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013182068921631488519179 13519773103382447232778769)
                  ·
                    refine ⟨10139829827536835424584077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13519773103382447232778769 10139829827536835424584077)
                    ·
                      refine ⟨3802436185326313284219029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10139829827536835424584077 3802436185326313284219029)
                      ·
                        rfl

theorem cell23_7405218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_7405218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405218 prefixEnd_7405218 := by exact prefixLift 7405218
  have htrace : WordTrace (prefixWord ++ tailWord_7405218) baseStart_7405218 baseEnd_7405218 := by
    simpa [prefixWord, tailWord_7405218, baseEnd_7405218] using wordTrace_append hprefix tailTrace_7405218
  have hstable : (prefixWord ++ tailWord_7405218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405218).length < 2 ^ (prefixWord ++ tailWord_7405218).sum := by decide
  have hdescent : baseEnd_7405218 < baseStart_7405218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405254 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7405254 : Nat := 118140960795 + 7405254 * 2 ^ 59
def prefixEnd_7405254 : Nat := 4983230072969 + 3 ^ 40 * 7405254 * 2
def baseEnd_7405254 : Nat := 3802454670629875143368863

theorem tailTrace_7405254 : CollatzResearch.WordTrace tailWord_7405254 prefixEnd_7405254 3802454670629875143368863 := by
  unfold tailWord_7405254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8440368822313654673095963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180061201542691299692713877 8440368822313654673095963)
  ·
    refine ⟨12660553233470482009643945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8440368822313654673095963 12660553233470482009643945)
    ·
      refine ⟨9495414925102861507232959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12660553233470482009643945 9495414925102861507232959)
      ·
        refine ⟨14243122387654292260849439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9495414925102861507232959 14243122387654292260849439)
        ·
          refine ⟨21364683581481438391274159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14243122387654292260849439 21364683581481438391274159)
          ·
            refine ⟨32047025372222157586911239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21364683581481438391274159 32047025372222157586911239)
            ·
              refine ⟨48070538058333236380366859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32047025372222157586911239 48070538058333236380366859)
              ·
                refine ⟨72105807087499854570550289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48070538058333236380366859 72105807087499854570550289)
                ·
                  refine ⟨54079355315624890927912717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72105807087499854570550289 54079355315624890927912717)
                  ·
                    refine ⟨20279758243359334097967269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54079355315624890927912717 20279758243359334097967269)
                    ·
                      refine ⟨3802454670629875143368863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20279758243359334097967269 3802454670629875143368863)
                      ·
                        rfl

theorem cell23_7405254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7405254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405254 prefixEnd_7405254 := by exact prefixLift 7405254
  have htrace : WordTrace (prefixWord ++ tailWord_7405254) baseStart_7405254 baseEnd_7405254 := by
    simpa [prefixWord, tailWord_7405254, baseEnd_7405254] using wordTrace_append hprefix tailTrace_7405254
  have hstable : (prefixWord ++ tailWord_7405254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405254).length < 2 ^ (prefixWord ++ tailWord_7405254).sum := by decide
  have hdescent : baseEnd_7405254 < baseStart_7405254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405340 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7405340 : Nat := 118140960795 + 7405340 * 2 ^ 59
def prefixEnd_7405340 : Nat := 4983230072969 + 3 ^ 40 * 7405340 * 2
def baseEnd_7405340 : Nat := 3802498829966161806893467

theorem tailTrace_7405340 : CollatzResearch.WordTrace tailWord_7405340 prefixEnd_7405340 3802498829966161806893467 := by
  unfold tailWord_7405340
  simp only [CollatzResearch.WordTrace]
  refine ⟨135047469495862693113350737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180063292661150257484467649 135047469495862693113350737)
  ·
    refine ⟨101285602121897019835013053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135047469495862693113350737 101285602121897019835013053)
    ·
      refine ⟨37982100795711382438129895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101285602121897019835013053 37982100795711382438129895)
      ·
        refine ⟨56973151193567073657194843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37982100795711382438129895 56973151193567073657194843)
        ·
          refine ⟨85459726790350610485792265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56973151193567073657194843 85459726790350610485792265)
          ·
            refine ⟨64094795092762957864344199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85459726790350610485792265 64094795092762957864344199)
            ·
              refine ⟨96142192639144436796516299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64094795092762957864344199 96142192639144436796516299)
              ·
                refine ⟨144213288958716655194774449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96142192639144436796516299 144213288958716655194774449)
                ·
                  refine ⟨108159966719037491396080837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144213288958716655194774449 108159966719037491396080837)
                  ·
                    refine ⟨20279993759819529636765157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108159966719037491396080837 20279993759819529636765157)
                    ·
                      refine ⟨3802498829966161806893467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20279993759819529636765157 3802498829966161806893467)
                      ·
                        rfl

theorem cell23_7405340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7405340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405340 prefixEnd_7405340 := by exact prefixLift 7405340
  have htrace : WordTrace (prefixWord ++ tailWord_7405340) baseStart_7405340 baseEnd_7405340 := by
    simpa [prefixWord, tailWord_7405340, baseEnd_7405340] using wordTrace_append hprefix tailTrace_7405340
  have hstable : (prefixWord ++ tailWord_7405340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405340).length < 2 ^ (prefixWord ++ tailWord_7405340).sum := by decide
  have hdescent : baseEnd_7405340 < baseStart_7405340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405364 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_7405364 : Nat := 118140960795 + 7405364 * 2 ^ 59
def prefixEnd_7405364 : Nat := 4983230072969 + 3 ^ 40 * 7405364 * 2
def baseEnd_7405364 : Nat := 3802511153501869712993357

theorem tailTrace_7405364 : CollatzResearch.WordTrace tailWord_7405364 prefixEnd_7405364 3802511153501869712993357 := by
  unfold tailWord_7405364
  simp only [CollatzResearch.WordTrace]
  refine ⟨135047907171819219162787573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180063876229092292217050097 135047907171819219162787573)
  ·
    refine ⟨12660741297358051796511335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135047907171819219162787573 12660741297358051796511335)
    ·
      refine ⟨18991111946037077694767003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12660741297358051796511335 18991111946037077694767003)
      ·
        refine ⟨28486667919055616542150505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18991111946037077694767003 28486667919055616542150505)
        ·
          refine ⟨21365000939291712406612879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28486667919055616542150505 21365000939291712406612879)
          ·
            refine ⟨32047501408937568609919319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21365000939291712406612879 32047501408937568609919319)
            ·
              refine ⟨48071252113406352914878979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32047501408937568609919319 48071252113406352914878979)
              ·
                refine ⟨72106878170109529372318469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48071252113406352914878979 72106878170109529372318469)
                ·
                  refine ⟨13520039656895536757309713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72106878170109529372318469 13520039656895536757309713)
                  ·
                    refine ⟨10140029742671652567982285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13520039656895536757309713 10140029742671652567982285)
                    ·
                      refine ⟨3802511153501869712993357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10140029742671652567982285 3802511153501869712993357)
                      ·
                        rfl

theorem cell23_7405364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_7405364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405364 prefixEnd_7405364 := by exact prefixLift 7405364
  have htrace : WordTrace (prefixWord ++ tailWord_7405364) baseStart_7405364 baseEnd_7405364 := by
    simpa [prefixWord, tailWord_7405364, baseEnd_7405364] using wordTrace_append hprefix tailTrace_7405364
  have hstable : (prefixWord ++ tailWord_7405364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405364).length < 2 ^ (prefixWord ++ tailWord_7405364).sum := by decide
  have hdescent : baseEnd_7405364 < baseStart_7405364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405384 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 6]
def baseStart_7405384 : Nat := 118140960795 + 7405384 * 2 ^ 59
def prefixEnd_7405384 : Nat := 4983230072969 + 3 ^ 40 * 7405384 * 2
def baseEnd_7405384 : Nat := 422502380346106626082585

theorem tailTrace_7405384 : CollatzResearch.WordTrace tailWord_7405384 prefixEnd_7405384 422502380346106626082585 := by
  unfold tailWord_7405384
  simp only [CollatzResearch.WordTrace]
  refine ⟨135048271901782990870651603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180064362535710654494202137 135048271901782990870651603)
  ·
    refine ⟨202572407852674486305977405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135048271901782990870651603 202572407852674486305977405)
    ·
      refine ⟨75964652944752932364741527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202572407852674486305977405 75964652944752932364741527)
      ·
        refine ⟨113946979417129398547112291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75964652944752932364741527 113946979417129398547112291)
        ·
          refine ⟨170920469125694097820668437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113946979417129398547112291 170920469125694097820668437)
          ·
            refine ⟨8011896990266910835343833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170920469125694097820668437 8011896990266910835343833)
            ·
              refine ⟨6008922742700183126507875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8011896990266910835343833 6008922742700183126507875)
              ·
                refine ⟨9013384114050274689761813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6008922742700183126507875 9013384114050274689761813)
                ·
                  refine ⟨422502380346106626082585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9013384114050274689761813 422502380346106626082585)
                  ·
                    rfl

theorem cell23_7405384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 6].length) (baseStart_7405384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405384 prefixEnd_7405384 := by exact prefixLift 7405384
  have htrace : WordTrace (prefixWord ++ tailWord_7405384) baseStart_7405384 baseEnd_7405384 := by
    simpa [prefixWord, tailWord_7405384, baseEnd_7405384] using wordTrace_append hprefix tailTrace_7405384
  have hstable : (prefixWord ++ tailWord_7405384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405384).length < 2 ^ (prefixWord ++ tailWord_7405384).sum := by decide
  have hdescent : baseEnd_7405384 < baseStart_7405384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405397 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_7405397 : Nat := 118140960795 + 7405397 * 2 ^ 59
def prefixEnd_7405397 : Nat := 4983230072969 + 3 ^ 40 * 7405397 * 2
def baseEnd_7405397 : Nat := 1267509366121156027960235

theorem tailTrace_7405397 : CollatzResearch.WordTrace tailWord_7405397 prefixEnd_7405397 1267509366121156027960235 := by
  unfold tailWord_7405397
  simp only [CollatzResearch.WordTrace]
  refine ⟨270097017952518884961526445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180064678635012589974350963 270097017952518884961526445)
  ·
    refine ⟨101286381732194581860572417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270097017952518884961526445 101286381732194581860572417)
    ·
      refine ⟨75964786299145936395429313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101286381732194581860572417 75964786299145936395429313)
      ·
        refine ⟨56973589724359452296571985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75964786299145936395429313 56973589724359452296571985)
        ·
          refine ⟨42730192293269589222428989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56973589724359452296571985 42730192293269589222428989)
          ·
            refine ⟨16023822109976095958410871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42730192293269589222428989 16023822109976095958410871)
            ·
              refine ⟨24035733164964143937616307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16023822109976095958410871 24035733164964143937616307)
              ·
                refine ⟨36053599747446215906424461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24035733164964143937616307 36053599747446215906424461)
                ·
                  refine ⟨13520099905292330964909173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36053599747446215906424461 13520099905292330964909173)
                  ·
                    refine ⟨1267509366121156027960235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13520099905292330964909173 1267509366121156027960235)
                    ·
                      rfl

theorem cell23_7405397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_7405397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405397 prefixEnd_7405397 := by exact prefixLift 7405397
  have htrace : WordTrace (prefixWord ++ tailWord_7405397) baseStart_7405397 baseEnd_7405397 := by
    simpa [prefixWord, tailWord_7405397, baseEnd_7405397] using wordTrace_append hprefix tailTrace_7405397
  have hstable : (prefixWord ++ tailWord_7405397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405397).length < 2 ^ (prefixWord ++ tailWord_7405397).sum := by decide
  have hdescent : baseEnd_7405397 < baseStart_7405397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405417 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 4]
def baseStart_7405417 : Nat := 118140960795 + 7405417 * 2 ^ 59
def prefixEnd_7405417 : Nat := 4983230072969 + 3 ^ 40 * 7405417 * 2
def baseEnd_7405417 : Nat := 3802538367976558005630613

theorem tailTrace_7405417 : CollatzResearch.WordTrace tailWord_7405417 prefixEnd_7405417 3802538367976558005630613 := by
  unfold tailWord_7405417
  simp only [CollatzResearch.WordTrace]
  refine ⟨270097747412446428377254505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180065164941630952251503003 270097747412446428377254505)
  ·
    refine ⟨202573310559334821282940879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270097747412446428377254505 202573310559334821282940879)
    ·
      refine ⟨303859965839002231924411319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202573310559334821282940879 303859965839002231924411319)
      ·
        refine ⟨455789948758503347886616979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303859965839002231924411319 455789948758503347886616979)
        ·
          refine ⟨683684923137755021829925469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455789948758503347886616979 683684923137755021829925469)
          ·
            refine ⟨256381846176658133186222051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683684923137755021829925469 256381846176658133186222051)
            ·
              refine ⟨384572769264987199779333077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256381846176658133186222051 384572769264987199779333077)
              ·
                refine ⟨9013424279648137494828119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 384572769264987199779333077 9013424279648137494828119)
                ·
                  refine ⟨13520136419472206242242179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013424279648137494828119 13520136419472206242242179)
                  ·
                    refine ⟨20280204629208309363363269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13520136419472206242242179 20280204629208309363363269)
                    ·
                      refine ⟨3802538367976558005630613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20280204629208309363363269 3802538367976558005630613)
                      ·
                        rfl

theorem cell23_7405417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 1, 4].length) (baseStart_7405417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405417 prefixEnd_7405417 := by exact prefixLift 7405417
  have htrace : WordTrace (prefixWord ++ tailWord_7405417) baseStart_7405417 baseEnd_7405417 := by
    simpa [prefixWord, tailWord_7405417, baseEnd_7405417] using wordTrace_append hprefix tailTrace_7405417
  have hstable : (prefixWord ++ tailWord_7405417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405417).length < 2 ^ (prefixWord ++ tailWord_7405417).sum := by decide
  have hdescent : baseEnd_7405417 < baseStart_7405417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405444 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_7405444 : Nat := 118140960795 + 7405444 * 2 ^ 59
def prefixEnd_7405444 : Nat := 4983230072969 + 3 ^ 40 * 7405444 * 2
def baseEnd_7405444 : Nat := 1267517410651409799997663

theorem tailTrace_7405444 : CollatzResearch.WordTrace tailWord_7405444 prefixEnd_7405444 1267517410651409799997663 := by
  unfold tailWord_7405444
  simp only [CollatzResearch.WordTrace]
  refine ⟨135049366091674305994243693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180065821455565741325658257 135049366091674305994243693)
  ·
    refine ⟨50643512284377864747841385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135049366091674305994243693 50643512284377864747841385)
    ·
      refine ⟨37982634213283398560881039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50643512284377864747841385 37982634213283398560881039)
      ·
        refine ⟨56973951319925097841321559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37982634213283398560881039 56973951319925097841321559)
        ·
          refine ⟨85460926979887646761982339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56973951319925097841321559 85460926979887646761982339)
          ·
            refine ⟨128191390469831470142973509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85460926979887646761982339 128191390469831470142973509)
            ·
              refine ⟨24035885713093400651807533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128191390469831470142973509 24035885713093400651807533)
              ·
                refine ⟨9013457142410025244427825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24035885713093400651807533 9013457142410025244427825)
                ·
                  refine ⟨6760092856807518933320869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9013457142410025244427825 6760092856807518933320869)
                  ·
                    refine ⟨1267517410651409799997663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6760092856807518933320869 1267517410651409799997663)
                    ·
                      rfl

theorem cell23_7405444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_7405444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405444 prefixEnd_7405444 := by exact prefixLift 7405444
  have htrace : WordTrace (prefixWord ++ tailWord_7405444) baseStart_7405444 baseEnd_7405444 := by
    simpa [prefixWord, tailWord_7405444, baseEnd_7405444] using wordTrace_append hprefix tailTrace_7405444
  have hstable : (prefixWord ++ tailWord_7405444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405444).length < 2 ^ (prefixWord ++ tailWord_7405444).sum := by decide
  have hdescent : baseEnd_7405444 < baseStart_7405444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405468 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7405468 : Nat := 118140960795 + 7405468 * 2 ^ 59
def prefixEnd_7405468 : Nat := 4983230072969 + 3 ^ 40 * 7405468 * 2
def baseEnd_7405468 : Nat := 3802564555489937306092879

theorem tailTrace_7405468 : CollatzResearch.WordTrace tailWord_7405468 prefixEnd_7405468 3802564555489937306092879 := by
  unfold tailWord_7405468
  simp only [CollatzResearch.WordTrace]
  refine ⟨135049803767630832043680529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180066405023507776058240705 135049803767630832043680529)
  ·
    refine ⟨101287352825723124032760397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135049803767630832043680529 101287352825723124032760397)
    ·
      refine ⟨37982757309646171512285149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101287352825723124032760397 37982757309646171512285149)
      ·
        refine ⟨14243533991117314317106931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37982757309646171512285149 14243533991117314317106931)
        ·
          refine ⟨21365300986675971475660397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14243533991117314317106931 21365300986675971475660397)
          ·
            refine ⟨8011987870003489303372649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21365300986675971475660397 8011987870003489303372649)
            ·
              refine ⟨6008990902502616977529487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8011987870003489303372649 6008990902502616977529487)
              ·
                refine ⟨9013486353753925466294231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6008990902502616977529487 9013486353753925466294231)
                ·
                  refine ⟨13520229530630888199441347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013486353753925466294231 13520229530630888199441347)
                  ·
                    refine ⟨20280344295946332299162021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13520229530630888199441347 20280344295946332299162021)
                    ·
                      refine ⟨3802564555489937306092879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20280344295946332299162021 3802564555489937306092879)
                      ·
                        rfl

theorem cell23_7405468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7405468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405468 prefixEnd_7405468 := by exact prefixLift 7405468
  have htrace : WordTrace (prefixWord ++ tailWord_7405468) baseStart_7405468 baseEnd_7405468 := by
    simpa [prefixWord, tailWord_7405468, baseEnd_7405468] using wordTrace_append hprefix tailTrace_7405468
  have hstable : (prefixWord ++ tailWord_7405468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405468).length < 2 ^ (prefixWord ++ tailWord_7405468).sum := by decide
  have hdescent : baseEnd_7405468 < baseStart_7405468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405471 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 3]
def baseStart_7405471 : Nat := 118140960795 + 7405471 * 2 ^ 59
def prefixEnd_7405471 : Nat := 4983230072969 + 3 ^ 40 * 7405471 * 2
def baseEnd_7405471 : Nat := 3802566095931900794355365

theorem tailTrace_7405471 : CollatzResearch.WordTrace tailWord_7405471 prefixEnd_7405471 3802566095931900794355365 := by
  unfold tailWord_7405471
  simp only [CollatzResearch.WordTrace]
  refine ⟨270099716954250795599720267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180066477969500530399813511 270099716954250795599720267)
  ·
    refine ⟨405149575431376193399580401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270099716954250795599720267 405149575431376193399580401)
    ·
      refine ⟨303862181573532145049685301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405149575431376193399580401 303862181573532145049685301)
      ·
        refine ⟨28487079522518638598407997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303862181573532145049685301 28487079522518638598407997)
        ·
          refine ⟨10682654820944489474402999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28487079522518638598407997 10682654820944489474402999)
          ·
            refine ⟨16023982231416734211604499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10682654820944489474402999 16023982231416734211604499)
            ·
              refine ⟨24035973347125101317406749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16023982231416734211604499 24035973347125101317406749)
              ·
                refine ⟨9013490005171912994027531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24035973347125101317406749 9013490005171912994027531)
                ·
                  refine ⟨13520235007757869491041297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013490005171912994027531 13520235007757869491041297)
                  ·
                    refine ⟨10140176255818402118280973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13520235007757869491041297 10140176255818402118280973)
                    ·
                      refine ⟨3802566095931900794355365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10140176255818402118280973 3802566095931900794355365)
                      ·
                        rfl

theorem cell23_7405471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_7405471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405471 prefixEnd_7405471 := by exact prefixLift 7405471
  have htrace : WordTrace (prefixWord ++ tailWord_7405471) baseStart_7405471 baseEnd_7405471 := by
    simpa [prefixWord, tailWord_7405471, baseEnd_7405471] using wordTrace_append hprefix tailTrace_7405471
  have hstable : (prefixWord ++ tailWord_7405471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405471).length < 2 ^ (prefixWord ++ tailWord_7405471).sum := by decide
  have hdescent : baseEnd_7405471 < baseStart_7405471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405501 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_7405501 : Nat := 118140960795 + 7405501 * 2 ^ 59
def prefixEnd_7405501 : Nat := 4983230072969 + 3 ^ 40 * 7405501 * 2
def baseEnd_7405501 : Nat := 3802581500351535676980227

theorem tailTrace_7405501 : CollatzResearch.WordTrace tailWord_7405501 prefixEnd_7405501 3802581500351535676980227 := by
  unfold tailWord_7405501
  simp only [CollatzResearch.WordTrace]
  refine ⟨270100811144142110723312357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180067207429428073815541571 270100811144142110723312357)
  ·
    refine ⟨50643902089526645760621067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270100811144142110723312357 50643902089526645760621067)
    ·
      refine ⟨75965853134289968640931601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50643902089526645760621067 75965853134289968640931601)
      ·
        refine ⟨56974389850717476480698701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75965853134289968640931601 56974389850717476480698701)
        ·
          refine ⟨21365396194019053680262013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56974389850717476480698701 21365396194019053680262013)
          ·
            refine ⟨8012023572757145130098255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21365396194019053680262013 8012023572757145130098255)
            ·
              refine ⟨12018035359135717695147383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8012023572757145130098255 12018035359135717695147383)
              ·
                refine ⟨18027053038703576542721075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12018035359135717695147383 18027053038703576542721075)
                ·
                  refine ⟨27040579558055364814081613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18027053038703576542721075 27040579558055364814081613)
                  ·
                    refine ⟨10140217334270761805280605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27040579558055364814081613 10140217334270761805280605)
                    ·
                      refine ⟨3802581500351535676980227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10140217334270761805280605 3802581500351535676980227)
                      ·
                        rfl

theorem cell23_7405501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_7405501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405501 prefixEnd_7405501 := by exact prefixLift 7405501
  have htrace : WordTrace (prefixWord ++ tailWord_7405501) baseStart_7405501 baseEnd_7405501 := by
    simpa [prefixWord, tailWord_7405501, baseEnd_7405501] using wordTrace_append hprefix tailTrace_7405501
  have hstable : (prefixWord ++ tailWord_7405501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405501).length < 2 ^ (prefixWord ++ tailWord_7405501).sum := by decide
  have hdescent : baseEnd_7405501 < baseStart_7405501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405527 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_7405527 : Nat := 118140960795 + 7405527 * 2 ^ 59
def prefixEnd_7405527 : Nat := 4983230072969 + 3 ^ 40 * 7405527 * 2
def baseEnd_7405527 : Nat := 3802594850848552575255107

theorem tailTrace_7405527 : CollatzResearch.WordTrace tailWord_7405527 prefixEnd_7405527 3802594850848552575255107 := by
  unfold tailWord_7405527
  simp only [CollatzResearch.WordTrace]
  refine ⟨270101759442047917163758835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180067839628031944775839223 270101759442047917163758835)
  ·
    refine ⟨405152639163071875745638253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270101759442047917163758835 405152639163071875745638253)
    ·
      refine ⟨151932239686151953404614345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405152639163071875745638253 151932239686151953404614345)
      ·
        refine ⟨113949179764613965053460759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151932239686151953404614345 113949179764613965053460759)
        ·
          refine ⟨170923769646920947580191139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113949179764613965053460759 170923769646920947580191139)
          ·
            refine ⟨256385654470381421370286709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170923769646920947580191139 256385654470381421370286709)
            ·
              refine ⟨24036155106598258253464379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256385654470381421370286709 24036155106598258253464379)
              ·
                refine ⟨36054232659897387380196569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24036155106598258253464379 36054232659897387380196569)
                ·
                  refine ⟨27040674494923040535147427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36054232659897387380196569 27040674494923040535147427)
                  ·
                    refine ⟨40561011742384560802721141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27040674494923040535147427 40561011742384560802721141)
                    ·
                      refine ⟨3802594850848552575255107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40561011742384560802721141 3802594850848552575255107)
                      ·
                        rfl

theorem cell23_7405527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_7405527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405527 prefixEnd_7405527 := by exact prefixLift 7405527
  have htrace : WordTrace (prefixWord ++ tailWord_7405527) baseStart_7405527 baseEnd_7405527 := by
    simpa [prefixWord, tailWord_7405527, baseEnd_7405527] using wordTrace_append hprefix tailTrace_7405527
  have hstable : (prefixWord ++ tailWord_7405527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405527).length < 2 ^ (prefixWord ++ tailWord_7405527).sum := by decide
  have hdescent : baseEnd_7405527 < baseStart_7405527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405537 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_7405537 : Nat := 118140960795 + 7405537 * 2 ^ 59
def prefixEnd_7405537 : Nat := 4983230072969 + 3 ^ 40 * 7405537 * 2
def baseEnd_7405537 : Nat := 3802599985655097536130061

theorem tailTrace_7405537 : CollatzResearch.WordTrace tailWord_7405537 prefixEnd_7405537 3802599985655097536130061 := by
  unfold tailWord_7405537
  simp only [CollatzResearch.WordTrace]
  refine ⟨270102124172011688871622865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180068082781341125914415243 270102124172011688871622865)
  ·
    refine ⟨202576593129008766653717149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270102124172011688871622865 202576593129008766653717149)
    ·
      refine ⟨75966222423378287495143931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202576593129008766653717149 75966222423378287495143931)
      ·
        refine ⟨113949333635067431242715897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75966222423378287495143931 113949333635067431242715897)
        ·
          refine ⟨85462000226300573432036923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113949333635067431242715897 85462000226300573432036923)
          ·
            refine ⟨128193000339450860148055385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85462000226300573432036923 128193000339450860148055385)
            ·
              refine ⟨96144750254588145111041539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128193000339450860148055385 96144750254588145111041539)
              ·
                refine ⟨144217125381882217666562309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96144750254588145111041539 144217125381882217666562309)
                ·
                  refine ⟨27040711009102915812480433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144217125381882217666562309 27040711009102915812480433)
                  ·
                    refine ⟨20280533256827186859360325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27040711009102915812480433 20280533256827186859360325)
                    ·
                      refine ⟨3802599985655097536130061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20280533256827186859360325 3802599985655097536130061)
                      ·
                        rfl

theorem cell23_7405537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_7405537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405537 prefixEnd_7405537 := by exact prefixLift 7405537
  have htrace : WordTrace (prefixWord ++ tailWord_7405537) baseStart_7405537 baseEnd_7405537 := by
    simpa [prefixWord, tailWord_7405537, baseEnd_7405537] using wordTrace_append hprefix tailTrace_7405537
  have hstable : (prefixWord ++ tailWord_7405537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405537).length < 2 ^ (prefixWord ++ tailWord_7405537).sum := by decide
  have hdescent : baseEnd_7405537 < baseStart_7405537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405587 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 5]
def baseStart_7405587 : Nat := 118140960795 + 7405587 * 2 ^ 59
def prefixEnd_7405587 : Nat := 4983230072969 + 3 ^ 40 * 7405587 * 2
def baseEnd_7405587 : Nat := 3802625659687822340504831

theorem tailTrace_7405587 : CollatzResearch.WordTrace tailWord_7405587 prefixEnd_7405587 3802625659687822340504831 := by
  unfold tailWord_7405587
  simp only [CollatzResearch.WordTrace]
  refine ⟨270103947821830547410943015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180069298547887031607295343 270103947821830547410943015)
  ·
    refine ⟨405155921732745821116414523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270103947821830547410943015 405155921732745821116414523)
    ·
      refine ⟨607733882599118731674621785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405155921732745821116414523 607733882599118731674621785)
      ·
        refine ⟨455800411949339048755966339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607733882599118731674621785 455800411949339048755966339)
        ·
          refine ⟨683700617924008573133949509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455800411949339048755966339 683700617924008573133949509)
          ·
            refine ⟨128193865860751607462615533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 683700617924008573133949509 128193865860751607462615533)
            ·
              refine ⟨48072699697781852798480825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128193865860751607462615533 48072699697781852798480825)
              ·
                refine ⟨36054524773336389598860619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48072699697781852798480825 36054524773336389598860619)
                ·
                  refine ⟨54081787160004584398290929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36054524773336389598860619 54081787160004584398290929)
                  ·
                    refine ⟨40561340370003438298718197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54081787160004584398290929 40561340370003438298718197)
                    ·
                      refine ⟨3802625659687822340504831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40561340370003438298718197 3802625659687822340504831)
                      ·
                        rfl

theorem cell23_7405587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_7405587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405587 prefixEnd_7405587 := by exact prefixLift 7405587
  have htrace : WordTrace (prefixWord ++ tailWord_7405587) baseStart_7405587 baseEnd_7405587 := by
    simpa [prefixWord, tailWord_7405587, baseEnd_7405587] using wordTrace_append hprefix tailTrace_7405587
  have hstable : (prefixWord ++ tailWord_7405587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405587).length < 2 ^ (prefixWord ++ tailWord_7405587).sum := by decide
  have hdescent : baseEnd_7405587 < baseStart_7405587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405594 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_7405594 : Nat := 118140960795 + 7405594 * 2 ^ 59
def prefixEnd_7405594 : Nat := 4983230072969 + 3 ^ 40 * 7405594 * 2
def baseEnd_7405594 : Nat := 1267543084684134604372433

theorem tailTrace_7405594 : CollatzResearch.WordTrace tailWord_7405594 prefixEnd_7405594 1267543084684134604372433 := by
  unfold tailWord_7405594
  simp only [CollatzResearch.WordTrace]
  refine ⟨67526050783201296901611959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180069468755203458404298557 67526050783201296901611959)
  ·
    refine ⟨101289076174801945352417939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67526050783201296901611959 101289076174801945352417939)
    ·
      refine ⟨151933614262202918028626909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101289076174801945352417939 151933614262202918028626909)
      ·
        refine ⟨56975105348326094260735091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151933614262202918028626909 56975105348326094260735091)
        ·
          refine ⟨85462658022489141391102637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56975105348326094260735091 85462658022489141391102637)
          ·
            refine ⟨32048496758433428021663489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85462658022489141391102637 32048496758433428021663489)
            ·
              refine ⟨24036372568825071016247617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32048496758433428021663489 24036372568825071016247617)
              ·
                refine ⟨18027279426618803262185713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24036372568825071016247617 18027279426618803262185713)
                ·
                  refine ⟨13520459569964102446639285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18027279426618803262185713 13520459569964102446639285)
                  ·
                    refine ⟨1267543084684134604372433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13520459569964102446639285 1267543084684134604372433)
                    ·
                      rfl

theorem cell23_7405594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_7405594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405594 prefixEnd_7405594 := by exact prefixLift 7405594
  have htrace : WordTrace (prefixWord ++ tailWord_7405594) baseStart_7405594 baseEnd_7405594 := by
    simpa [prefixWord, tailWord_7405594, baseEnd_7405594] using wordTrace_append hprefix tailTrace_7405594
  have hstable : (prefixWord ++ tailWord_7405594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405594).length < 2 ^ (prefixWord ++ tailWord_7405594).sum := by decide
  have hdescent : baseEnd_7405594 < baseStart_7405594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405608 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7405608 : Nat := 118140960795 + 7405608 * 2 ^ 59
def prefixEnd_7405608 : Nat := 4983230072969 + 3 ^ 40 * 7405608 * 2
def baseEnd_7405608 : Nat := 3802636442781566758342235

theorem tailTrace_7405608 : CollatzResearch.WordTrace tailWord_7405608 prefixEnd_7405608 3802636442781566758342235 := by
  unfold tailWord_7405608
  simp only [CollatzResearch.WordTrace]
  refine ⟨135052356877377233998728739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180069809169836311998304985 135052356877377233998728739)
  ·
    refine ⟨202578535316065850998093109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135052356877377233998728739 202578535316065850998093109)
    ·
      refine ⟨18991737685881173531071229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202578535316065850998093109 18991737685881173531071229)
      ·
        refine ⟨7121901632205440074151711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18991737685881173531071229 7121901632205440074151711)
        ·
          refine ⟨10682852448308160111227567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121901632205440074151711 10682852448308160111227567)
          ·
            refine ⟨16024278672462240166841351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10682852448308160111227567 16024278672462240166841351)
            ·
              refine ⟨24036418008693360250262027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16024278672462240166841351 24036418008693360250262027)
              ·
                refine ⟨36054627013040040375393041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24036418008693360250262027 36054627013040040375393041)
                ·
                  refine ⟨27040970259780030281544781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36054627013040040375393041 27040970259780030281544781)
                  ·
                    refine ⟨10140363847417511355579293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27040970259780030281544781 10140363847417511355579293)
                    ·
                      refine ⟨3802636442781566758342235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10140363847417511355579293 3802636442781566758342235)
                      ·
                        rfl

theorem cell23_7405608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7405608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405608 prefixEnd_7405608 := by exact prefixLift 7405608
  have htrace : WordTrace (prefixWord ++ tailWord_7405608) baseStart_7405608 baseEnd_7405608 := by
    simpa [prefixWord, tailWord_7405608, baseEnd_7405608] using wordTrace_append hprefix tailTrace_7405608
  have hstable : (prefixWord ++ tailWord_7405608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405608).length < 2 ^ (prefixWord ++ tailWord_7405608).sum := by decide
  have hdescent : baseEnd_7405608 < baseStart_7405608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405627 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 4]
def baseStart_7405627 : Nat := 118140960795 + 7405627 * 2 ^ 59
def prefixEnd_7405627 : Nat := 4983230072969 + 3 ^ 40 * 7405627 * 2
def baseEnd_7405627 : Nat := 3802646198914002184004647

theorem tailTrace_7405627 : CollatzResearch.WordTrace tailWord_7405627 prefixEnd_7405627 3802646198914002184004647 := by
  unfold tailWord_7405627
  simp only [CollatzResearch.WordTrace]
  refine ⟨270105406741685634242399135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180070271161123756161599423 270105406741685634242399135)
  ·
    refine ⟨405158110112528451363598703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270105406741685634242399135 405158110112528451363598703)
    ·
      refine ⟨607737165168792677045398055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405158110112528451363598703 607737165168792677045398055)
      ·
        refine ⟨911605747753189015568097083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607737165168792677045398055 911605747753189015568097083)
        ·
          refine ⟨1367408621629783523352145625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911605747753189015568097083 1367408621629783523352145625)
          ·
            refine ⟨1025556466222337642514109219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367408621629783523352145625 1025556466222337642514109219)
            ·
              refine ⟨1538334699333506463771163829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025556466222337642514109219 1538334699333506463771163829)
              ·
                refine ⟨144218878062516230978546609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1538334699333506463771163829 144218878062516230978546609)
                ·
                  refine ⟨108164158546887173233909957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144218878062516230978546609 108164158546887173233909957)
                  ·
                    refine ⟨20280779727541344981358117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108164158546887173233909957 20280779727541344981358117)
                    ·
                      refine ⟨3802646198914002184004647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20280779727541344981358117 3802646198914002184004647)
                      ·
                        rfl

theorem cell23_7405627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 4].length) (baseStart_7405627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405627 prefixEnd_7405627 := by exact prefixLift 7405627
  have htrace : WordTrace (prefixWord ++ tailWord_7405627) baseStart_7405627 baseEnd_7405627 := by
    simpa [prefixWord, tailWord_7405627, baseEnd_7405627] using wordTrace_append hprefix tailTrace_7405627
  have hstable : (prefixWord ++ tailWord_7405627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405627).length < 2 ^ (prefixWord ++ tailWord_7405627).sum := by decide
  have hdescent : baseEnd_7405627 < baseStart_7405627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405637 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 8]
def baseStart_7405637 : Nat := 118140960795 + 7405637 * 2 ^ 59
def prefixEnd_7405637 : Nat := 4983230072969 + 3 ^ 40 * 7405637 * 2
def baseEnd_7405637 : Nat := 422516814857838571653289

theorem tailTrace_7405637 : CollatzResearch.WordTrace tailWord_7405637 prefixEnd_7405637 422516814857838571653289 := by
  unfold tailWord_7405637
  simp only [CollatzResearch.WordTrace]
  refine ⟨270105771471649405950263165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180070514314432937300175443 270105771471649405950263165)
  ·
    refine ⟨101289664301868527231348687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270105771471649405950263165 101289664301868527231348687)
    ·
      refine ⟨151934496452802790847023031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101289664301868527231348687 151934496452802790847023031)
      ·
        refine ⟨227901744679204186270534547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151934496452802790847023031 227901744679204186270534547)
        ·
          refine ⟨341852617018806279405801821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227901744679204186270534547 341852617018806279405801821)
          ·
            refine ⟨128194731382052354777175683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341852617018806279405801821 128194731382052354777175683)
            ·
              refine ⟨192292097073078532165763525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128194731382052354777175683 192292097073078532165763525)
              ·
                refine ⟨36054768201202224781080661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192292097073078532165763525 36054768201202224781080661)
                ·
                  refine ⟨422516814857838571653289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36054768201202224781080661 422516814857838571653289)
                  ·
                    rfl

theorem cell23_7405637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_7405637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405637 prefixEnd_7405637 := by exact prefixLift 7405637
  have htrace : WordTrace (prefixWord ++ tailWord_7405637) baseStart_7405637 baseEnd_7405637 := by
    simpa [prefixWord, tailWord_7405637, baseEnd_7405637] using wordTrace_append hprefix tailTrace_7405637
  have hstable : (prefixWord ++ tailWord_7405637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405637).length < 2 ^ (prefixWord ++ tailWord_7405637).sum := by decide
  have hdescent : baseEnd_7405637 < baseStart_7405637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405657 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_7405657 : Nat := 118140960795 + 7405657 * 2 ^ 59
def prefixEnd_7405657 : Nat := 4983230072969 + 3 ^ 40 * 7405657 * 2
def baseEnd_7405657 : Nat := 3802661603333637066629509

theorem tailTrace_7405657 : CollatzResearch.WordTrace tailWord_7405657 prefixEnd_7405657 3802661603333637066629509 := by
  unfold tailWord_7405657
  simp only [CollatzResearch.WordTrace]
  refine ⟨270106500931576949365991225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180071000621051299577327483 270106500931576949365991225)
  ·
    refine ⟨202579875698682712024493419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270106500931576949365991225 202579875698682712024493419)
    ·
      refine ⟨303869813548024068036740129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202579875698682712024493419 303869813548024068036740129)
      ·
        refine ⟨227902360161018051027555097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303869813548024068036740129 227902360161018051027555097)
        ·
          refine ⟨170926770120763538270666323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227902360161018051027555097 170926770120763538270666323)
          ·
            refine ⟨256390155181145307405999485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170926770120763538270666323 256390155181145307405999485)
            ·
              refine ⟨96146308192929490277249807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256390155181145307405999485 96146308192929490277249807)
              ·
                refine ⟨144219462289394235415874711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96146308192929490277249807 144219462289394235415874711)
                ·
                  refine ⟨216329193434091353123812067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144219462289394235415874711 216329193434091353123812067)
                  ·
                    refine ⟨324493790151137029685718101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216329193434091353123812067 324493790151137029685718101)
                    ·
                      refine ⟨3802661603333637066629509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 324493790151137029685718101 3802661603333637066629509)
                      ·
                        rfl

theorem cell23_7405657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_7405657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405657 prefixEnd_7405657 := by exact prefixLift 7405657
  have htrace : WordTrace (prefixWord ++ tailWord_7405657) baseStart_7405657 baseEnd_7405657 := by
    simpa [prefixWord, tailWord_7405657, baseEnd_7405657] using wordTrace_append hprefix tailTrace_7405657
  have hstable : (prefixWord ++ tailWord_7405657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405657).length < 2 ^ (prefixWord ++ tailWord_7405657).sum := by decide
  have hdescent : baseEnd_7405657 < baseStart_7405657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405671 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 6]
def baseStart_7405671 : Nat := 118140960795 + 7405671 * 2 ^ 59
def prefixEnd_7405671 : Nat := 4983230072969 + 3 ^ 40 * 7405671 * 2
def baseEnd_7405671 : Nat := 422518754673644445761605

theorem tailTrace_7405671 : CollatzResearch.WordTrace tailWord_7405671 prefixEnd_7405671 422518754673644445761605 := by
  unfold tailWord_7405671
  simp only [CollatzResearch.WordTrace]
  refine ⟨270107011553526229757000867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180071341035684153171333911 270107011553526229757000867)
  ·
    refine ⟨405160517330289344635501301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270107011553526229757000867 405160517330289344635501301)
    ·
      refine ⟨37983798499714626059578247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 405160517330289344635501301 37983798499714626059578247)
      ·
        refine ⟨56975697749571939089367371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37983798499714626059578247 56975697749571939089367371)
        ·
          refine ⟨85463546624357908634051057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56975697749571939089367371 85463546624357908634051057)
          ·
            refine ⟨64097659968268431475538293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85463546624357908634051057 64097659968268431475538293)
            ·
              refine ⟨6009155622025165450831715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64097659968268431475538293 6009155622025165450831715)
              ·
                refine ⟨9013733433037748176247573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009155622025165450831715 9013733433037748176247573)
                ·
                  refine ⟨422518754673644445761605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9013733433037748176247573 422518754673644445761605)
                  ·
                    rfl

theorem cell23_7405671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 6].length) (baseStart_7405671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405671 prefixEnd_7405671 := by exact prefixLift 7405671
  have htrace : WordTrace (prefixWord ++ tailWord_7405671) baseStart_7405671 baseEnd_7405671 := by
    simpa [prefixWord, tailWord_7405671, baseEnd_7405671] using wordTrace_append hprefix tailTrace_7405671
  have hstable : (prefixWord ++ tailWord_7405671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405671).length < 2 ^ (prefixWord ++ tailWord_7405671).sum := by decide
  have hdescent : baseEnd_7405671 < baseStart_7405671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405681 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_7405681 : Nat := 118140960795 + 7405681 * 2 ^ 59
def prefixEnd_7405681 : Nat := 4983230072969 + 3 ^ 40 * 7405681 * 2
def baseEnd_7405681 : Nat := 3802673926869344972729399

theorem tailTrace_7405681 : CollatzResearch.WordTrace tailWord_7405681 prefixEnd_7405681 3802673926869344972729399 := by
  unfold tailWord_7405681
  simp only [CollatzResearch.WordTrace]
  refine ⟨270107376283490001464864897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180071584188993334309909931 270107376283490001464864897)
  ·
    refine ⟨202580532212617501098648673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270107376283490001464864897 202580532212617501098648673)
    ·
      refine ⟨151935399159463125823986505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202580532212617501098648673 151935399159463125823986505)
      ·
        refine ⟨113951549369597344367989879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151935399159463125823986505 113951549369597344367989879)
        ·
          refine ⟨170927324054396016551984819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113951549369597344367989879 170927324054396016551984819)
          ·
            refine ⟨256390986081594024827977229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170927324054396016551984819 256390986081594024827977229)
            ·
              refine ⟨96146619780597759310491461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256390986081594024827977229 96146619780597759310491461)
              ·
                refine ⟨18027491208862079870717149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96146619780597759310491461 18027491208862079870717149)
                ·
                  refine ⟨6760309203323279951518931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18027491208862079870717149 6760309203323279951518931)
                  ·
                    refine ⟨10140463804984919927278397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6760309203323279951518931 10140463804984919927278397)
                    ·
                      refine ⟨3802673926869344972729399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10140463804984919927278397 3802673926869344972729399)
                      ·
                        rfl

theorem cell23_7405681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_7405681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405681 prefixEnd_7405681 := by exact prefixLift 7405681
  have htrace : WordTrace (prefixWord ++ tailWord_7405681) baseStart_7405681 baseEnd_7405681 := by
    simpa [prefixWord, tailWord_7405681, baseEnd_7405681] using wordTrace_append hprefix tailTrace_7405681
  have hstable : (prefixWord ++ tailWord_7405681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405681).length < 2 ^ (prefixWord ++ tailWord_7405681).sum := by decide
  have hdescent : baseEnd_7405681 < baseStart_7405681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405701 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_7405701 : Nat := 118140960795 + 7405701 * 2 ^ 59
def prefixEnd_7405701 : Nat := 4983230072969 + 3 ^ 40 * 7405701 * 2
def baseEnd_7405701 : Nat := 1267561398827478298159769

theorem tailTrace_7405701 : CollatzResearch.WordTrace tailWord_7405701 prefixEnd_7405701 1267561398827478298159769 := by
  unfold tailWord_7405701
  simp only [CollatzResearch.WordTrace]
  refine ⟨270108105743417544880592957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180072070495611696587061971 270108105743417544880592957)
  ·
    refine ⟨101290539653781579330222359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270108105743417544880592957 101290539653781579330222359)
    ·
      refine ⟨151935809480672368995333539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101290539653781579330222359 151935809480672368995333539)
      ·
        refine ⟨227903714221008553493000309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151935809480672368995333539 227903714221008553493000309)
        ·
          refine ⟨21365973208219551889968779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227903714221008553493000309 21365973208219551889968779)
          ·
            refine ⟨32048959812329327834953169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21365973208219551889968779 32048959812329327834953169)
            ·
              refine ⟨24036719859246995876214877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32048959812329327834953169 24036719859246995876214877)
              ·
                refine ⟨9013769947217623453580579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24036719859246995876214877 9013769947217623453580579)
                ·
                  refine ⟨13520654920826435180370869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013769947217623453580579 13520654920826435180370869)
                  ·
                    refine ⟨1267561398827478298159769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13520654920826435180370869 1267561398827478298159769)
                    ·
                      rfl

theorem cell23_7405701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_7405701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405701 prefixEnd_7405701 := by exact prefixLift 7405701
  have htrace : WordTrace (prefixWord ++ tailWord_7405701) baseStart_7405701 baseEnd_7405701 := by
    simpa [prefixWord, tailWord_7405701, baseEnd_7405701] using wordTrace_append hprefix tailTrace_7405701
  have hstable : (prefixWord ++ tailWord_7405701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405701).length < 2 ^ (prefixWord ++ tailWord_7405701).sum := by decide
  have hdescent : baseEnd_7405701 < baseStart_7405701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405735 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 1, 5]
def baseStart_7405735 : Nat := 118140960795 + 7405735 * 2 ^ 59
def prefixEnd_7405735 : Nat := 4983230072969 + 3 ^ 40 * 7405735 * 2
def baseEnd_7405735 : Nat := 1267567218274895920484717

theorem tailTrace_7405735 : CollatzResearch.WordTrace tailWord_7405735 prefixEnd_7405735 1267567218274895920484717 := by
  unfold tailWord_7405735
  simp only [CollatzResearch.WordTrace]
  refine ⟨270109345825294368687330659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180072897216862912458220439 270109345825294368687330659)
  ·
    refine ⟨405164018737941553030995989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270109345825294368687330659 405164018737941553030995989)
    ·
      refine ⟨18992063378341010298327937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405164018737941553030995989 18992063378341010298327937)
      ·
        refine ⟨14244047533755757723745953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18992063378341010298327937 14244047533755757723745953)
        ·
          refine ⟨10683035650316818292809465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14244047533755757723745953 10683035650316818292809465)
          ·
            refine ⟨8012276737737613719607099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10683035650316818292809465 8012276737737613719607099)
            ·
              refine ⟨12018415106606420579410649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8012276737737613719607099 12018415106606420579410649)
              ·
                refine ⟨9013811329954815434557987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12018415106606420579410649 9013811329954815434557987)
                ·
                  refine ⟨13520716994932223151836981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9013811329954815434557987 13520716994932223151836981)
                  ·
                    refine ⟨1267567218274895920484717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13520716994932223151836981 1267567218274895920484717)
                    ·
                      rfl

theorem cell23_7405735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_7405735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405735 prefixEnd_7405735 := by exact prefixLift 7405735
  have htrace : WordTrace (prefixWord ++ tailWord_7405735) baseStart_7405735 baseEnd_7405735 := by
    simpa [prefixWord, tailWord_7405735, baseEnd_7405735] using wordTrace_append hprefix tailTrace_7405735
  have hstable : (prefixWord ++ tailWord_7405735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405735).length < 2 ^ (prefixWord ++ tailWord_7405735).sum := by decide
  have hdescent : baseEnd_7405735 < baseStart_7405735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405751 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_7405751 : Nat := 118140960795 + 7405751 * 2 ^ 59
def prefixEnd_7405751 : Nat := 4983230072969 + 3 ^ 40 * 7405751 * 2
def baseEnd_7405751 : Nat := 3802709870515159698854077

theorem tailTrace_7405751 : CollatzResearch.WordTrace tailWord_7405751 prefixEnd_7405751 3802709870515159698854077 := by
  unfold tailWord_7405751
  simp only [CollatzResearch.WordTrace]
  refine ⟨270109929393236403419913107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180073286262157602279942071 270109929393236403419913107)
  ·
    refine ⟨405164894089854605129869661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270109929393236403419913107 405164894089854605129869661)
    ·
      refine ⟨151936835283695476923701123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405164894089854605129869661 151936835283695476923701123)
      ·
        refine ⟨227905252925543215385551685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151936835283695476923701123 227905252925543215385551685)
        ·
          refine ⟨42732234923539352884790941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227905252925543215385551685 42732234923539352884790941)
          ·
            refine ⟨16024588096327257331796603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42732234923539352884790941 16024588096327257331796603)
            ·
              refine ⟨24036882144490885997694905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16024588096327257331796603 24036882144490885997694905)
              ·
                refine ⟨18027661608368164498271179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24036882144490885997694905 18027661608368164498271179)
                ·
                  refine ⟨27041492412552246747406769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18027661608368164498271179 27041492412552246747406769)
                  ·
                    refine ⟨20281119309414185060555077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27041492412552246747406769 20281119309414185060555077)
                    ·
                      refine ⟨3802709870515159698854077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20281119309414185060555077 3802709870515159698854077)
                      ·
                        rfl

theorem cell23_7405751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_7405751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405751 prefixEnd_7405751 := by exact prefixLift 7405751
  have htrace : WordTrace (prefixWord ++ tailWord_7405751) baseStart_7405751 baseEnd_7405751 := by
    simpa [prefixWord, tailWord_7405751, baseEnd_7405751] using wordTrace_append hprefix tailTrace_7405751
  have hstable : (prefixWord ++ tailWord_7405751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405751).length < 2 ^ (prefixWord ++ tailWord_7405751).sum := by decide
  have hdescent : baseEnd_7405751 < baseStart_7405751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405755 : List Nat := [1, 1, 1, 1, 1, 2, 6, 5, 1, 2, 2]
def baseStart_7405755 : Nat := 118140960795 + 7405755 * 2 ^ 59
def prefixEnd_7405755 : Nat := 4983230072969 + 3 ^ 40 * 7405755 * 2
def baseEnd_7405755 : Nat := 3802711924437777683204059

theorem tailTrace_7405755 : CollatzResearch.WordTrace tailWord_7405755 prefixEnd_7405755 3802711924437777683204059 := by
  unfold tailWord_7405755
  simp only [CollatzResearch.WordTrace]
  refine ⟨270110075285221912103058719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180073383523481274735372479 270110075285221912103058719)
  ·
    refine ⟨405165112927832868154588079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270110075285221912103058719 405165112927832868154588079)
    ·
      refine ⟨607747669391749302231882119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405165112927832868154588079 607747669391749302231882119)
      ·
        refine ⟨911621504087623953347823179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607747669391749302231882119 911621504087623953347823179)
        ·
          refine ⟨1367432256131435930021734769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911621504087623953347823179 1367432256131435930021734769)
          ·
            refine ⟨1025574192098576947516301077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367432256131435930021734769 1025574192098576947516301077)
            ·
              refine ⟨48073790254620794414826613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1025574192098576947516301077 48073790254620794414826613)
              ·
                refine ⟨4506917836370699476389995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48073790254620794414826613 4506917836370699476389995)
                ·
                  refine ⟨6760376754556049214584993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506917836370699476389995 6760376754556049214584993)
                  ·
                    refine ⟨5070282565917036910938745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6760376754556049214584993 5070282565917036910938745)
                    ·
                      refine ⟨3802711924437777683204059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070282565917036910938745 3802711924437777683204059)
                      ·
                        rfl

theorem cell23_7405755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 2, 2].length) (baseStart_7405755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405755 prefixEnd_7405755 := by exact prefixLift 7405755
  have htrace : WordTrace (prefixWord ++ tailWord_7405755) baseStart_7405755 baseEnd_7405755 := by
    simpa [prefixWord, tailWord_7405755, baseEnd_7405755] using wordTrace_append hprefix tailTrace_7405755
  have hstable : (prefixWord ++ tailWord_7405755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405755).length < 2 ^ (prefixWord ++ tailWord_7405755).sum := by decide
  have hdescent : baseEnd_7405755 < baseStart_7405755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405761 : List Nat := [1, 2, 6, 1, 2, 11]
def baseStart_7405761 : Nat := 118140960795 + 7405761 * 2 ^ 59
def prefixEnd_7405761 : Nat := 4983230072969 + 3 ^ 40 * 7405761 * 2
def baseEnd_7405761 : Nat := 15649032943710718764317

theorem tailTrace_7405761 : CollatzResearch.WordTrace tailWord_7405761 prefixEnd_7405761 15649032943710718764317 := by
  unfold tailWord_7405761
  simp only [CollatzResearch.WordTrace]
  refine ⟨270110294123200175127777137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180073529415466783418518091 270110294123200175127777137)
  ·
    refine ⟨202582720592400131345832853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270110294123200175127777137 202582720592400131345832853)
    ·
      refine ⟨9496065027768756156835915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202582720592400131345832853 9496065027768756156835915)
      ·
        refine ⟨14244097541653134235253873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496065027768756156835915 14244097541653134235253873)
        ·
          refine ⟨10683073156239850676440405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14244097541653134235253873 10683073156239850676440405)
          ·
            refine ⟨15649032943710718764317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10683073156239850676440405 15649032943710718764317)
            ·
              rfl

theorem cell23_7405761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 11].length) (baseStart_7405761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405761 prefixEnd_7405761 := by exact prefixLift 7405761
  have htrace : WordTrace (prefixWord ++ tailWord_7405761) baseStart_7405761 baseEnd_7405761 := by
    simpa [prefixWord, tailWord_7405761, baseEnd_7405761] using wordTrace_append hprefix tailTrace_7405761
  have hstable : (prefixWord ++ tailWord_7405761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405761).length < 2 ^ (prefixWord ++ tailWord_7405761).sum := by decide
  have hdescent : baseEnd_7405761 < baseStart_7405761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405804 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_7405804 : Nat := 118140960795 + 7405804 * 2 ^ 59
def prefixEnd_7405804 : Nat := 4983230072969 + 3 ^ 40 * 7405804 * 2
def baseEnd_7405804 : Nat := 1267579028329949330497111

theorem tailTrace_7405804 : CollatzResearch.WordTrace tailWord_7405804 prefixEnd_7405804 1267579028329949330497111 := by
  unfold tailWord_7405804
  simp only [CollatzResearch.WordTrace]
  refine ⟨135055931231022196735796233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180074574974696262314394977 135055931231022196735796233)
  ·
    refine ⟨101291948423266647551847175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135055931231022196735796233 101291948423266647551847175)
    ·
      refine ⟨151937922634899971327770763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101291948423266647551847175 151937922634899971327770763)
      ·
        refine ⟨227906883952349956991656145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151937922634899971327770763 227906883952349956991656145)
        ·
          refine ⟨170930162964262467743742109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227906883952349956991656145 170930162964262467743742109)
          ·
            refine ⟨64098811111598425403903291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170930162964262467743742109 64098811111598425403903291)
            ·
              refine ⟨96148216667397638105854937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64098811111598425403903291 96148216667397638105854937)
              ·
                refine ⟨72111162500548228579391203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96148216667397638105854937 72111162500548228579391203)
                ·
                  refine ⟨108166743750822342869086805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72111162500548228579391203 108166743750822342869086805)
                  ·
                    refine ⟨1267579028329949330497111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108166743750822342869086805 1267579028329949330497111)
                    ·
                      rfl

theorem cell23_7405804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_7405804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405804 prefixEnd_7405804 := by exact prefixLift 7405804
  have htrace : WordTrace (prefixWord ++ tailWord_7405804) baseStart_7405804 baseEnd_7405804 := by
    simpa [prefixWord, tailWord_7405804, baseEnd_7405804] using wordTrace_append hprefix tailTrace_7405804
  have hstable : (prefixWord ++ tailWord_7405804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405804).length < 2 ^ (prefixWord ++ tailWord_7405804).sum := by decide
  have hdescent : baseEnd_7405804 < baseStart_7405804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405841 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_7405841 : Nat := 118140960795 + 7405841 * 2 ^ 59
def prefixEnd_7405841 : Nat := 4983230072969 + 3 ^ 40 * 7405841 * 2
def baseEnd_7405841 : Nat := 3802756083774064346728663

theorem tailTrace_7405841 : CollatzResearch.WordTrace tailWord_7405841 prefixEnd_7405841 3802756083774064346728663 := by
  unfold tailWord_7405841
  simp only [CollatzResearch.WordTrace]
  refine ⟨270113211962910348790689377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180075474641940232527126251 270113211962910348790689377)
  ·
    refine ⟨202584908972182761593017033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270113211962910348790689377 202584908972182761593017033)
    ·
      refine ⟨151938681729137071194762775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202584908972182761593017033 151938681729137071194762775)
      ·
        refine ⟨227908022593705606792144163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151938681729137071194762775 227908022593705606792144163)
        ·
          refine ⟨341862033890558410188216245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227908022593705606792144163 341862033890558410188216245)
          ·
            refine ⟨32049565677239850955145273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341862033890558410188216245 32049565677239850955145273)
            ·
              refine ⟨24037174257929888216358955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32049565677239850955145273 24037174257929888216358955)
              ·
                refine ⟨36055761386894832324538433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24037174257929888216358955 36055761386894832324538433)
                ·
                  refine ⟨27041821040171124243403825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36055761386894832324538433 27041821040171124243403825)
                  ·
                    refine ⟨20281365780128343182552869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27041821040171124243403825 20281365780128343182552869)
                    ·
                      refine ⟨3802756083774064346728663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20281365780128343182552869 3802756083774064346728663)
                      ·
                        rfl

theorem cell23_7405841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_7405841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405841 prefixEnd_7405841 := by exact prefixLift 7405841
  have htrace : WordTrace (prefixWord ++ tailWord_7405841) baseStart_7405841 baseEnd_7405841 := by
    simpa [prefixWord, tailWord_7405841, baseEnd_7405841] using wordTrace_append hprefix tailTrace_7405841
  have hstable : (prefixWord ++ tailWord_7405841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405841).length < 2 ^ (prefixWord ++ tailWord_7405841).sum := by decide
  have hdescent : baseEnd_7405841 < baseStart_7405841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405845 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_7405845 : Nat := 118140960795 + 7405845 * 2 ^ 59
def prefixEnd_7405845 : Nat := 4983230072969 + 3 ^ 40 * 7405845 * 2
def baseEnd_7405845 : Nat := 3802758137696682331078645

theorem tailTrace_7405845 : CollatzResearch.WordTrace tailWord_7405845 prefixEnd_7405845 3802758137696682331078645 := by
  unfold tailWord_7405845
  simp only [CollatzResearch.WordTrace]
  refine ⟨270113357854895857473834989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180075571903263904982556659 270113357854895857473834989)
  ·
    refine ⟨101292509195585946552688121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270113357854895857473834989 101292509195585946552688121)
    ·
      refine ⟨75969381896689459914516091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101292509195585946552688121 75969381896689459914516091)
      ·
        refine ⟨113954072845034189871774137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75969381896689459914516091 113954072845034189871774137)
        ·
          refine ⟨85465554633775642403830603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113954072845034189871774137 85465554633775642403830603)
          ·
            refine ⟨128198331950663463605745905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85465554633775642403830603 128198331950663463605745905)
            ·
              refine ⟨96148748962997597704309429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128198331950663463605745905 96148748962997597704309429)
              ·
                refine ⟨9013945215281024784779009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96148748962997597704309429 9013945215281024784779009)
                ·
                  refine ⟨6760458911460768588584257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9013945215281024784779009 6760458911460768588584257)
                  ·
                    refine ⟨5070344183595576441438193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6760458911460768588584257 5070344183595576441438193)
                    ·
                      refine ⟨3802758137696682331078645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070344183595576441438193 3802758137696682331078645)
                      ·
                        rfl

theorem cell23_7405845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_7405845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405845 prefixEnd_7405845 := by exact prefixLift 7405845
  have htrace : WordTrace (prefixWord ++ tailWord_7405845) baseStart_7405845 baseEnd_7405845 := by
    simpa [prefixWord, tailWord_7405845, baseEnd_7405845] using wordTrace_append hprefix tailTrace_7405845
  have hstable : (prefixWord ++ tailWord_7405845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405845).length < 2 ^ (prefixWord ++ tailWord_7405845).sum := by decide
  have hdescent : baseEnd_7405845 < baseStart_7405845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405868 : List Nat := [2, 2, 1, 1, 1, 3, 5, 3, 5]
def baseStart_7405868 : Nat := 118140960795 + 7405868 * 2 ^ 59
def prefixEnd_7405868 : Nat := 4983230072969 + 3 ^ 40 * 7405868 * 2
def baseEnd_7405868 : Nat := 422529994194637304565671

theorem tailTrace_7405868 : CollatzResearch.WordTrace tailWord_7405868 prefixEnd_7405868 422529994194637304565671 := by
  unfold tailWord_7405868
  simp only [CollatzResearch.WordTrace]
  refine ⟨135057098366906266200961129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180076131155875021601281505 135057098366906266200961129)
  ·
    refine ⟨101292823775179699650720847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135057098366906266200961129 101292823775179699650720847)
    ·
      refine ⟨151939235662769549476081271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101292823775179699650720847 151939235662769549476081271)
      ·
        refine ⟨227908853494154324214121907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151939235662769549476081271 227908853494154324214121907)
        ·
          refine ⟨341863280241231486321182861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227908853494154324214121907 341863280241231486321182861)
          ·
            refine ⟨128198730090461807370443573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341863280241231486321182861 128198730090461807370443573)
            ·
              refine ⟨12018630945980794440979085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128198730090461807370443573 12018630945980794440979085)
              ·
                refine ⟨4506986604742797915367157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12018630945980794440979085 4506986604742797915367157)
                ·
                  refine ⟨422529994194637304565671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4506986604742797915367157 422529994194637304565671)
                  ·
                    rfl

theorem cell23_7405868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_7405868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405868 prefixEnd_7405868 := by exact prefixLift 7405868
  have htrace : WordTrace (prefixWord ++ tailWord_7405868) baseStart_7405868 baseEnd_7405868 := by
    simpa [prefixWord, tailWord_7405868, baseEnd_7405868] using wordTrace_append hprefix tailTrace_7405868
  have hstable : (prefixWord ++ tailWord_7405868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405868).length < 2 ^ (prefixWord ++ tailWord_7405868).sum := by decide
  have hdescent : baseEnd_7405868 < baseStart_7405868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405962 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_7405962 : Nat := 118140960795 + 7405962 * 2 ^ 59
def prefixEnd_7405962 : Nat := 4983230072969 + 3 ^ 40 * 7405962 * 2
def baseEnd_7405962 : Nat := 1267606071644419457771869

theorem tailTrace_7405962 : CollatzResearch.WordTrace tailWord_7405962 prefixEnd_7405962 1267606071644419457771869 := by
  unfold tailWord_7405962
  simp only [CollatzResearch.WordTrace]
  refine ⟨67529406298867996613961035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180078416796981324303896093 67529406298867996613961035)
  ·
    refine ⟨101294109448301994920941553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67529406298867996613961035 101294109448301994920941553)
    ·
      refine ⟨75970582086226496190706165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101294109448301994920941553 75970582086226496190706165)
      ·
        refine ⟨7122242070583734017878703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75970582086226496190706165 7122242070583734017878703)
        ·
          refine ⟨10683363105875601026818055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7122242070583734017878703 10683363105875601026818055)
          ·
            refine ⟨16025044658813401540227083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683363105875601026818055 16025044658813401540227083)
            ·
              refine ⟨24037566988220102310340625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16025044658813401540227083 24037566988220102310340625)
              ·
                refine ⟨18028175241165076732755469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24037566988220102310340625 18028175241165076732755469)
                ·
                  refine ⟨6760565715436903774783301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18028175241165076732755469 6760565715436903774783301)
                  ·
                    refine ⟨1267606071644419457771869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6760565715436903774783301 1267606071644419457771869)
                    ·
                      rfl

theorem cell23_7405962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_7405962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405962 prefixEnd_7405962 := by exact prefixLift 7405962
  have htrace : WordTrace (prefixWord ++ tailWord_7405962) baseStart_7405962 baseEnd_7405962 := by
    simpa [prefixWord, tailWord_7405962, baseEnd_7405962] using wordTrace_append hprefix tailTrace_7405962
  have hstable : (prefixWord ++ tailWord_7405962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405962).length < 2 ^ (prefixWord ++ tailWord_7405962).sum := by decide
  have hdescent : baseEnd_7405962 < baseStart_7405962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7405992 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 6]
def baseStart_7405992 : Nat := 118140960795 + 7405992 * 2 ^ 59
def prefixEnd_7405992 : Nat := 4983230072969 + 3 ^ 40 * 7405992 * 2
def baseEnd_7405992 : Nat := 422537068816988139548941

theorem tailTrace_7405992 : CollatzResearch.WordTrace tailWord_7405992 prefixEnd_7405992 422537068816988139548941 := by
  unfold tailWord_7405992
  simp only [CollatzResearch.WordTrace]
  refine ⟨135059359692681650789718115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180079146256908867719624153 135059359692681650789718115)
  ·
    refine ⟨202589039539022476184577173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135059359692681650789718115 202589039539022476184577173)
    ·
      refine ⟨9496361228391678571152055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202589039539022476184577173 9496361228391678571152055)
      ·
        refine ⟨14244541842587517856728083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496361228391678571152055 14244541842587517856728083)
        ·
          refine ⟨21366812763881276785092125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14244541842587517856728083 21366812763881276785092125)
          ·
            refine ⟨8012554786455478794409547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21366812763881276785092125 8012554786455478794409547)
            ·
              refine ⟨12018832179683218191614321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8012554786455478794409547 12018832179683218191614321)
              ·
                refine ⟨9014124134762413643710741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12018832179683218191614321 9014124134762413643710741)
                ·
                  refine ⟨422537068816988139548941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9014124134762413643710741 422537068816988139548941)
                  ·
                    rfl

theorem cell23_7405992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 6].length) (baseStart_7405992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7405992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7405992 prefixEnd_7405992 := by exact prefixLift 7405992
  have htrace : WordTrace (prefixWord ++ tailWord_7405992) baseStart_7405992 baseEnd_7405992 := by
    simpa [prefixWord, tailWord_7405992, baseEnd_7405992] using wordTrace_append hprefix tailTrace_7405992
  have hstable : (prefixWord ++ tailWord_7405992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7405992).length < 2 ^ (prefixWord ++ tailWord_7405992).sum := by decide
  have hdescent : baseEnd_7405992 < baseStart_7405992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7405992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406002 : List Nat := [3, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_7406002 : Nat := 118140960795 + 7406002 * 2 ^ 59
def prefixEnd_7406002 : Nat := 4983230072969 + 3 ^ 40 * 7406002 * 2
def baseEnd_7406002 : Nat := 3802838754159438216815423

theorem tailTrace_7406002 : CollatzResearch.WordTrace tailWord_7406002 prefixEnd_7406002 3802838754159438216815423 := by
  unfold tailWord_7406002
  simp only [CollatzResearch.WordTrace]
  refine ⟨67529771028831768321825065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180079389410218048858200173 67529771028831768321825065)
  ·
    refine ⟨50647328271623826241368799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67529771028831768321825065 50647328271623826241368799)
    ·
      refine ⟨75970992407435739362053199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50647328271623826241368799 75970992407435739362053199)
      ·
        refine ⟨113956488611153609043079799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75970992407435739362053199 113956488611153609043079799)
        ·
          refine ⟨170934732916730413564619699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113956488611153609043079799 170934732916730413564619699)
          ·
            refine ⟨256402099375095620346929549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170934732916730413564619699 256402099375095620346929549)
            ·
              refine ⟨96150787265660857630098581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256402099375095620346929549 96150787265660857630098581)
              ·
                refine ⟨4507068153077852701410871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96150787265660857630098581 4507068153077852701410871)
                ·
                  refine ⟨6760602229616779052116307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507068153077852701410871 6760602229616779052116307)
                  ·
                    refine ⟨10140903344425168578174461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6760602229616779052116307 10140903344425168578174461)
                    ·
                      refine ⟨3802838754159438216815423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10140903344425168578174461 3802838754159438216815423)
                      ·
                        rfl

theorem cell23_7406002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_7406002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406002 prefixEnd_7406002 := by exact prefixLift 7406002
  have htrace : WordTrace (prefixWord ++ tailWord_7406002) baseStart_7406002 baseEnd_7406002 := by
    simpa [prefixWord, tailWord_7406002, baseEnd_7406002] using wordTrace_append hprefix tailTrace_7406002
  have hstable : (prefixWord ++ tailWord_7406002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406002).length < 2 ^ (prefixWord ++ tailWord_7406002).sum := by decide
  have hdescent : baseEnd_7406002 < baseStart_7406002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406036 : List Nat := [2, 4, 1, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_7406036 : Nat := 118140960795 + 7406036 * 2 ^ 59
def prefixEnd_7406036 : Nat := 4983230072969 + 3 ^ 40 * 7406036 * 2
def baseEnd_7406036 : Nat := 3802856212501691083790267

theorem tailTrace_7406036 : CollatzResearch.WordTrace tailWord_7406036 prefixEnd_7406036 3802856212501691083790267 := by
  unfold tailWord_7406036
  simp only [CollatzResearch.WordTrace]
  refine ⟨135060162098601948547018981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180080216131469264729358641 135060162098601948547018981)
  ·
    refine ⟨25323780393487865352566059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135060162098601948547018981 25323780393487865352566059)
    ·
      refine ⟨37985670590231798028849089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25323780393487865352566059 37985670590231798028849089)
      ·
        refine ⟨28489252942673848521636817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37985670590231798028849089 28489252942673848521636817)
        ·
          refine ⟨21366939707005386391227613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28489252942673848521636817 21366939707005386391227613)
          ·
            refine ⟨8012602390127019896710355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21366939707005386391227613 8012602390127019896710355)
            ·
              refine ⟨12018903585190529845065533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8012602390127019896710355 12018903585190529845065533)
              ·
                refine ⟨4507088844446448691899575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12018903585190529845065533 4507088844446448691899575)
                ·
                  refine ⟨6760633266669673037849363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507088844446448691899575 6760633266669673037849363)
                  ·
                    refine ⟨10140949900004509556774045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6760633266669673037849363 10140949900004509556774045)
                    ·
                      refine ⟨3802856212501691083790267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10140949900004509556774045 3802856212501691083790267)
                      ·
                        rfl

theorem cell23_7406036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_7406036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406036 prefixEnd_7406036 := by exact prefixLift 7406036
  have htrace : WordTrace (prefixWord ++ tailWord_7406036) baseStart_7406036 baseEnd_7406036 := by
    simpa [prefixWord, tailWord_7406036, baseEnd_7406036] using wordTrace_append hprefix tailTrace_7406036
  have hstable : (prefixWord ++ tailWord_7406036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406036).length < 2 ^ (prefixWord ++ tailWord_7406036).sum := by decide
  have hdescent : baseEnd_7406036 < baseStart_7406036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406045 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_7406045 : Nat := 118140960795 + 7406045 * 2 ^ 59
def prefixEnd_7406045 : Nat := 4983230072969 + 3 ^ 40 * 7406045 * 2
def baseEnd_7406045 : Nat := 3802860833827581548577725

theorem tailTrace_7406045 : CollatzResearch.WordTrace tailWord_7406045 prefixEnd_7406045 3802860833827581548577725 := by
  unfold tailWord_7406045
  simp only [CollatzResearch.WordTrace]
  refine ⟨270120652454171291631115589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180080434969447527754077059 270120652454171291631115589)
  ·
    refine ⟨50647622335157117180834173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270120652454171291631115589 50647622335157117180834173)
    ·
      refine ⟨18992858375683918942812815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50647622335157117180834173 18992858375683918942812815)
      ·
        refine ⟨28489287563525878414219223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18992858375683918942812815 28489287563525878414219223)
        ·
          refine ⟨42733931345288817621328835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28489287563525878414219223 42733931345288817621328835)
          ·
            refine ⟨64100897017933226431993253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42733931345288817621328835 64100897017933226431993253)
            ·
              refine ⟨12018918190862479955998735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64100897017933226431993253 12018918190862479955998735)
              ·
                refine ⟨18028377286293719933998103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12018918190862479955998735 18028377286293719933998103)
                ·
                  refine ⟨27042565929440579900997155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18028377286293719933998103 27042565929440579900997155)
                  ·
                    refine ⟨40563848894160869851495733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27042565929440579900997155 40563848894160869851495733)
                    ·
                      refine ⟨3802860833827581548577725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40563848894160869851495733 3802860833827581548577725)
                      ·
                        rfl

theorem cell23_7406045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_7406045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406045 prefixEnd_7406045 := by exact prefixLift 7406045
  have htrace : WordTrace (prefixWord ++ tailWord_7406045) baseStart_7406045 baseEnd_7406045 := by
    simpa [prefixWord, tailWord_7406045, baseEnd_7406045] using wordTrace_append hprefix tailTrace_7406045
  have hstable : (prefixWord ++ tailWord_7406045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406045).length < 2 ^ (prefixWord ++ tailWord_7406045).sum := by decide
  have hdescent : baseEnd_7406045 < baseStart_7406045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406069 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7406069 : Nat := 118140960795 + 7406069 * 2 ^ 59
def prefixEnd_7406069 : Nat := 4983230072969 + 3 ^ 40 * 7406069 * 2
def baseEnd_7406069 : Nat := 1267624385787763151559205

theorem tailTrace_7406069 : CollatzResearch.WordTrace tailWord_7406069 prefixEnd_7406069 1267624385787763151559205 := by
  unfold tailWord_7406069
  simp only [CollatzResearch.WordTrace]
  refine ⟨270121527806084343729989261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180081018537389562486659507 270121527806084343729989261)
  ·
    refine ⟨101295572927281628898745973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270121527806084343729989261 101295572927281628898745973)
    ·
      refine ⟨9496459961932652709257435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101295572927281628898745973 9496459961932652709257435)
      ·
        refine ⟨14244689942898979063886153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496459961932652709257435 14244689942898979063886153)
        ·
          refine ⟨10683517457174234297914615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14244689942898979063886153 10683517457174234297914615)
          ·
            refine ⟨16025276185761351446871923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683517457174234297914615 16025276185761351446871923)
            ·
              refine ⟨24037914278642027170307885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16025276185761351446871923 24037914278642027170307885)
              ·
                refine ⟨9014217854490760188865457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24037914278642027170307885 9014217854490760188865457)
                ·
                  refine ⟨6760663390868070141649093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9014217854490760188865457 6760663390868070141649093)
                  ·
                    refine ⟨1267624385787763151559205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6760663390868070141649093 1267624385787763151559205)
                    ·
                      rfl

theorem cell23_7406069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7406069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406069 prefixEnd_7406069 := by exact prefixLift 7406069
  have htrace : WordTrace (prefixWord ++ tailWord_7406069) baseStart_7406069 baseEnd_7406069 := by
    simpa [prefixWord, tailWord_7406069, baseEnd_7406069] using wordTrace_append hprefix tailTrace_7406069
  have hstable : (prefixWord ++ tailWord_7406069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406069).length < 2 ^ (prefixWord ++ tailWord_7406069).sum := by decide
  have hdescent : baseEnd_7406069 < baseStart_7406069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406109 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_7406109 : Nat := 118140960795 + 7406109 * 2 ^ 59
def prefixEnd_7406109 : Nat := 4983230072969 + 3 ^ 40 * 7406109 * 2
def baseEnd_7406109 : Nat := 3802893696589469298177431

theorem tailTrace_7406109 : CollatzResearch.WordTrace tailWord_7406109 prefixEnd_7406109 3802893696589469298177431 := by
  unfold tailWord_7406109
  simp only [CollatzResearch.WordTrace]
  refine ⟨270122986725939430561445381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180081991150626287040963587 270122986725939430561445381)
  ·
    refine ⟨50648060011113643230271009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270122986725939430561445381 50648060011113643230271009)
    ·
      refine ⟨37986045008335232422703257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50648060011113643230271009 37986045008335232422703257)
      ·
        refine ⟨28489533756251424317027443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37986045008335232422703257 28489533756251424317027443)
        ·
          refine ⟨42734300634377136475541165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28489533756251424317027443 42734300634377136475541165)
          ·
            refine ⟨16025362737891426178327937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42734300634377136475541165 16025362737891426178327937)
            ·
              refine ⟨12019022053418569633745953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16025362737891426178327937 12019022053418569633745953)
              ·
                refine ⟨9014266540063927225309465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12019022053418569633745953 9014266540063927225309465)
                ·
                  refine ⟨6760699905047945418982099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9014266540063927225309465 6760699905047945418982099)
                  ·
                    refine ⟨10141049857571918128473149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6760699905047945418982099 10141049857571918128473149)
                    ·
                      refine ⟨3802893696589469298177431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10141049857571918128473149 3802893696589469298177431)
                      ·
                        rfl

theorem cell23_7406109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_7406109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406109 prefixEnd_7406109 := by exact prefixLift 7406109
  have htrace : WordTrace (prefixWord ++ tailWord_7406109) baseStart_7406109 baseEnd_7406109 := by
    simpa [prefixWord, tailWord_7406109, baseEnd_7406109] using wordTrace_append hprefix tailTrace_7406109
  have hstable : (prefixWord ++ tailWord_7406109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406109).length < 2 ^ (prefixWord ++ tailWord_7406109).sum := by decide
  have hdescent : baseEnd_7406109 < baseStart_7406109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406128 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_7406128 : Nat := 118140960795 + 7406128 * 2 ^ 59
def prefixEnd_7406128 : Nat := 4983230072969 + 3 ^ 40 * 7406128 * 2
def baseEnd_7406128 : Nat := 3802903452721904723839843

theorem tailTrace_7406128 : CollatzResearch.WordTrace tailWord_7406128 prefixEnd_7406128 3802903452721904723839843 := by
  unfold tailWord_7406128
  simp only [CollatzResearch.WordTrace]
  refine ⟨135061839856435298403193519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180082453141913731204258025 135061839856435298403193519)
  ·
    refine ⟨202592759784652947604790279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135061839856435298403193519 202592759784652947604790279)
    ·
      refine ⟨303889139676979421407185419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202592759784652947604790279 303889139676979421407185419)
      ·
        refine ⟨455833709515469132110778129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303889139676979421407185419 455833709515469132110778129)
        ·
          refine ⟨341875282136601849083083597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455833709515469132110778129 341875282136601849083083597)
          ·
            refine ⟨128203230801225693406156349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341875282136601849083083597 128203230801225693406156349)
            ·
              refine ⟨48076211550459635027308631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128203230801225693406156349 48076211550459635027308631)
              ·
                refine ⟨72114317325689452540962947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48076211550459635027308631 72114317325689452540962947)
                ·
                  refine ⟨108171475988534178811444421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72114317325689452540962947 108171475988534178811444421)
                  ·
                    refine ⟨20282151747850158527145829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108171475988534178811444421 20282151747850158527145829)
                    ·
                      refine ⟨3802903452721904723839843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20282151747850158527145829 3802903452721904723839843)
                      ·
                        rfl

theorem cell23_7406128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_7406128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406128 prefixEnd_7406128 := by exact prefixLift 7406128
  have htrace : WordTrace (prefixWord ++ tailWord_7406128) baseStart_7406128 baseEnd_7406128 := by
    simpa [prefixWord, tailWord_7406128, baseEnd_7406128] using wordTrace_append hprefix tailTrace_7406128
  have hstable : (prefixWord ++ tailWord_7406128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406128).length < 2 ^ (prefixWord ++ tailWord_7406128).sum := by decide
  have hdescent : baseEnd_7406128 < baseStart_7406128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406138 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 9]
def baseStart_7406138 : Nat := 118140960795 + 7406138 * 2 ^ 59
def prefixEnd_7406138 : Nat := 4983230072969 + 3 ^ 40 * 7406138 * 2
def baseEnd_7406138 : Nat := 422545398614272187190533

theorem tailTrace_7406138 : CollatzResearch.WordTrace tailWord_7406138 prefixEnd_7406138 422545398614272187190533 := by
  unfold tailWord_7406138
  simp only [CollatzResearch.WordTrace]
  refine ⟨67531011110708592128562767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180082696295222912342834045 67531011110708592128562767)
  ·
    refine ⟨101296516666062888192844151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67531011110708592128562767 101296516666062888192844151)
    ·
      refine ⟨151944774999094332289266227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101296516666062888192844151 151944774999094332289266227)
      ·
        refine ⟨227917162498641498433899341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151944774999094332289266227 227917162498641498433899341)
        ·
          refine ⟨85468935936990561912712253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227917162498641498433899341 85468935936990561912712253)
          ·
            refine ⟨32050850976371460717267095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85468935936990561912712253 32050850976371460717267095)
            ·
              refine ⟨48076276464557191075900643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32050850976371460717267095 48076276464557191075900643)
              ·
                refine ⟨72114414696835786613850965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48076276464557191075900643 72114414696835786613850965)
                ·
                  refine ⟨422545398614272187190533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72114414696835786613850965 422545398614272187190533)
                  ·
                    rfl

theorem cell23_7406138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_7406138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406138 prefixEnd_7406138 := by exact prefixLift 7406138
  have htrace : WordTrace (prefixWord ++ tailWord_7406138) baseStart_7406138 baseEnd_7406138 := by
    simpa [prefixWord, tailWord_7406138, baseEnd_7406138] using wordTrace_append hprefix tailTrace_7406138
  have hstable : (prefixWord ++ tailWord_7406138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406138).length < 2 ^ (prefixWord ++ tailWord_7406138).sum := by decide
  have hdescent : baseEnd_7406138 < baseStart_7406138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406155 : List Nat := [1, 1, 1, 1, 3, 1, 5, 5, 5]
def baseStart_7406155 : Nat := 118140960795 + 7406155 * 2 ^ 59
def prefixEnd_7406155 : Nat := 4983230072969 + 3 ^ 40 * 7406155 * 2
def baseEnd_7406155 : Nat := 422546368522175124244691

theorem tailTrace_7406155 : CollatzResearch.WordTrace tailWord_7406155 prefixEnd_7406155 422546368522175124244691 := by
  unfold tailWord_7406155
  simp only [CollatzResearch.WordTrace]
  refine ⟨270124664483772780417619919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180083109655848520278413279 270124664483772780417619919)
  ·
    refine ⟨405186996725659170626429879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270124664483772780417619919 405186996725659170626429879)
    ·
      refine ⟨607780495088488755939644819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405186996725659170626429879 607780495088488755939644819)
      ·
        refine ⟨911670742632733133909467229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607780495088488755939644819 911670742632733133909467229)
        ·
          refine ⟨341876528487274925216050211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 911670742632733133909467229 341876528487274925216050211)
          ·
            refine ⟨512814792730912387824075317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341876528487274925216050211 512814792730912387824075317)
            ·
              refine ⟨48076386818523036358507061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 512814792730912387824075317 48076386818523036358507061)
              ·
                refine ⟨4507161264236534658610037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48076386818523036358507061 4507161264236534658610037)
                ·
                  refine ⟨422546368522175124244691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4507161264236534658610037 422546368522175124244691)
                  ·
                    rfl

theorem cell23_7406155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 5].length) (baseStart_7406155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406155 prefixEnd_7406155 := by exact prefixLift 7406155
  have htrace : WordTrace (prefixWord ++ tailWord_7406155) baseStart_7406155 baseEnd_7406155 := by
    simpa [prefixWord, tailWord_7406155, baseEnd_7406155] using wordTrace_append hprefix tailTrace_7406155
  have hstable : (prefixWord ++ tailWord_7406155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406155).length < 2 ^ (prefixWord ++ tailWord_7406155).sum := by decide
  have hdescent : baseEnd_7406155 < baseStart_7406155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406165 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_7406165 : Nat := 118140960795 + 7406165 * 2 ^ 59
def prefixEnd_7406165 : Nat := 4983230072969 + 3 ^ 40 * 7406165 * 2
def baseEnd_7406165 : Nat := 3802922451506121079077173

theorem tailTrace_7406165 : CollatzResearch.WordTrace tailWord_7406165 prefixEnd_7406165 3802922451506121079077173 := by
  unfold tailWord_7406165
  simp only [CollatzResearch.WordTrace]
  refine ⟨270125029213736552125483949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180083352809157701416989299 270125029213736552125483949)
  ·
    refine ⟨101296885955151207047056481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270125029213736552125483949 101296885955151207047056481)
    ·
      refine ⟨75972664466363405285292361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101296885955151207047056481 75972664466363405285292361)
      ·
        refine ⟨56979498349772553963969271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75972664466363405285292361 56979498349772553963969271)
        ·
          refine ⟨85469247524658830945953907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56979498349772553963969271 85469247524658830945953907)
          ·
            refine ⟨128203871286988246418930861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85469247524658830945953907 128203871286988246418930861)
            ·
              refine ⟨48076451732620592407099073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128203871286988246418930861 48076451732620592407099073)
              ·
                refine ⟨36057338799465444305324305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48076451732620592407099073 36057338799465444305324305)
                ·
                  refine ⟨27043004099599083228993229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36057338799465444305324305 27043004099599083228993229)
                  ·
                    refine ⟨10141126537349656210872461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27043004099599083228993229 10141126537349656210872461)
                    ·
                      refine ⟨3802922451506121079077173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10141126537349656210872461 3802922451506121079077173)
                      ·
                        rfl

theorem cell23_7406165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_7406165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406165 prefixEnd_7406165 := by exact prefixLift 7406165
  have htrace : WordTrace (prefixWord ++ tailWord_7406165) baseStart_7406165 baseEnd_7406165 := by
    simpa [prefixWord, tailWord_7406165, baseEnd_7406165] using wordTrace_append hprefix tailTrace_7406165
  have hstable : (prefixWord ++ tailWord_7406165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406165).length < 2 ^ (prefixWord ++ tailWord_7406165).sum := by decide
  have hdescent : baseEnd_7406165 < baseStart_7406165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406172 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 7]
def baseStart_7406172 : Nat := 118140960795 + 7406172 * 2 ^ 59
def prefixEnd_7406172 : Nat := 4983230072969 + 3 ^ 40 * 7406172 * 2
def baseEnd_7406172 : Nat := 422547338430078061298849

theorem tailTrace_7406172 : CollatzResearch.WordTrace tailWord_7406172 prefixEnd_7406172 422547338430078061298849 := by
  unfold tailWord_7406172
  simp only [CollatzResearch.WordTrace]
  refine ⟨135062642262355596160494385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180083523016474128213992513 135062642262355596160494385)
  ·
    refine ⟨101296981696766697120370789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135062642262355596160494385 101296981696766697120370789)
    ·
      refine ⟨18993184068143755710069523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101296981696766697120370789 18993184068143755710069523)
      ·
        refine ⟨28489776102215633565104285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18993184068143755710069523 28489776102215633565104285)
        ·
          refine ⟨10683666038330862586914107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28489776102215633565104285 10683666038330862586914107)
          ·
            refine ⟨16025499057496293880371161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683666038330862586914107 16025499057496293880371161)
            ·
              refine ⟨12019124293122220410278371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16025499057496293880371161 12019124293122220410278371)
              ·
                refine ⟨18028686439683330615417557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12019124293122220410278371 18028686439683330615417557)
                ·
                  refine ⟨422547338430078061298849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18028686439683330615417557 422547338430078061298849)
                  ·
                    rfl

theorem cell23_7406172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_7406172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406172 prefixEnd_7406172 := by exact prefixLift 7406172
  have htrace : WordTrace (prefixWord ++ tailWord_7406172) baseStart_7406172 baseEnd_7406172 := by
    simpa [prefixWord, tailWord_7406172, baseEnd_7406172] using wordTrace_append hprefix tailTrace_7406172
  have hstable : (prefixWord ++ tailWord_7406172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406172).length < 2 ^ (prefixWord ++ tailWord_7406172).sum := by decide
  have hdescent : baseEnd_7406172 < baseStart_7406172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406175 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 1, 7, 2]
def baseStart_7406175 : Nat := 118140960795 + 7406175 * 2 ^ 59
def prefixEnd_7406175 : Nat := 4983230072969 + 3 ^ 40 * 7406175 * 2
def baseEnd_7406175 : Nat := 3802927586312666039952127

theorem tailTrace_7406175 : CollatzResearch.WordTrace tailWord_7406175 prefixEnd_7406175 3802927586312666039952127 := by
  unfold tailWord_7406175
  simp only [CollatzResearch.WordTrace]
  refine ⟨270125393943700323833347979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180083595962466882555565319 270125393943700323833347979)
  ·
    refine ⟨405188090915550485750021969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270125393943700323833347979 405188090915550485750021969)
    ·
      refine ⟨303891068186662864312516477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405188090915550485750021969 303891068186662864312516477)
      ·
        refine ⟨113959150569998574117193679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303891068186662864312516477 113959150569998574117193679)
        ·
          refine ⟨170938725854997861175790519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113959150569998574117193679 170938725854997861175790519)
          ·
            refine ⟨256408088782496791763685779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170938725854997861175790519 256408088782496791763685779)
            ·
              refine ⟨384612133173745187645528669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256408088782496791763685779 384612133173745187645528669)
              ·
                refine ⟨144229549940154445367073251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384612133173745187645528669 144229549940154445367073251)
                ·
                  refine ⟨216344324910231668050609877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144229549940154445367073251 216344324910231668050609877)
                  ·
                    refine ⟨5070570115083554719936169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 216344324910231668050609877 5070570115083554719936169)
                    ·
                      refine ⟨3802927586312666039952127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070570115083554719936169 3802927586312666039952127)
                      ·
                        rfl

theorem cell23_7406175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_7406175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406175 prefixEnd_7406175 := by exact prefixLift 7406175
  have htrace : WordTrace (prefixWord ++ tailWord_7406175) baseStart_7406175 baseEnd_7406175 := by
    simpa [prefixWord, tailWord_7406175, baseEnd_7406175] using wordTrace_append hprefix tailTrace_7406175
  have hstable : (prefixWord ++ tailWord_7406175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406175).length < 2 ^ (prefixWord ++ tailWord_7406175).sum := by decide
  have hdescent : baseEnd_7406175 < baseStart_7406175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406222 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7406222 : Nat := 118140960795 + 7406222 * 2 ^ 59
def prefixEnd_7406222 : Nat := 4983230072969 + 3 ^ 40 * 7406222 * 2
def baseEnd_7406222 : Nat := 3802951719903427356064411

theorem tailTrace_7406222 : CollatzResearch.WordTrace tailWord_7406222 prefixEnd_7406222 3802951719903427356064411 := by
  unfold tailWord_7406222
  simp only [CollatzResearch.WordTrace]
  refine ⟨33765888521816256357538615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180084738783020033906872613 33765888521816256357538615)
  ·
    refine ⟨50648832782724384536307923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33765888521816256357538615 50648832782724384536307923)
    ·
      refine ⟨75973249174086576804461885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50648832782724384536307923 75973249174086576804461885)
      ·
        refine ⟨28489968440282466301673207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75973249174086576804461885 28489968440282466301673207)
        ·
          refine ⟨42734952660423699452509811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28489968440282466301673207 42734952660423699452509811)
          ·
            refine ⟨64102428990635549178764717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42734952660423699452509811 64102428990635549178764717)
            ·
              refine ⟨24038410871488330942036769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64102428990635549178764717 24038410871488330942036769)
              ·
                refine ⟨18028808153616248206527577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24038410871488330942036769 18028808153616248206527577)
                ·
                  refine ⟨13521606115212186154895683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18028808153616248206527577 13521606115212186154895683)
                  ·
                    refine ⟨20282409172818279232343525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13521606115212186154895683 20282409172818279232343525)
                    ·
                      refine ⟨3802951719903427356064411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20282409172818279232343525 3802951719903427356064411)
                      ·
                        rfl

theorem cell23_7406222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7406222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406222 prefixEnd_7406222 := by exact prefixLift 7406222
  have htrace : WordTrace (prefixWord ++ tailWord_7406222) baseStart_7406222 baseEnd_7406222 := by
    simpa [prefixWord, tailWord_7406222, baseEnd_7406222] using wordTrace_append hprefix tailTrace_7406222
  have hstable : (prefixWord ++ tailWord_7406222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406222).length < 2 ^ (prefixWord ++ tailWord_7406222).sum := by decide
  have hdescent : baseEnd_7406222 < baseStart_7406222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406322 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_7406322 : Nat := 118140960795 + 7406322 * 2 ^ 59
def prefixEnd_7406322 : Nat := 4983230072969 + 3 ^ 40 * 7406322 * 2
def baseEnd_7406322 : Nat := 1267667689322958988271317

theorem tailTrace_7406322 : CollatzResearch.WordTrace tailWord_7406322 prefixEnd_7406322 1267667689322958988271317 := by
  unfold tailWord_7406322
  simp only [CollatzResearch.WordTrace]
  refine ⟨67532688868541941984737305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180087170316111845292632813 67532688868541941984737305)
  ·
    refine ⟨50649516651406456488552979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67532688868541941984737305 50649516651406456488552979)
    ·
      refine ⟨75974274977109684732829469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50649516651406456488552979 75974274977109684732829469)
      ·
        refine ⟨28490353116416131774811051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75974274977109684732829469 28490353116416131774811051)
        ·
          refine ⟨42735529674624197662216577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28490353116416131774811051 42735529674624197662216577)
          ·
            refine ⟨32051647255968148246662433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42735529674624197662216577 32051647255968148246662433)
            ·
              refine ⟨24038735441976111184996825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32051647255968148246662433 24038735441976111184996825)
              ·
                refine ⟨18029051581482083388747619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24038735441976111184996825 18029051581482083388747619)
                ·
                  refine ⟨27043577372223125083121429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18029051581482083388747619 27043577372223125083121429)
                  ·
                    refine ⟨1267667689322958988271317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27043577372223125083121429 1267667689322958988271317)
                    ·
                      rfl

theorem cell23_7406322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_7406322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406322 prefixEnd_7406322 := by exact prefixLift 7406322
  have htrace : WordTrace (prefixWord ++ tailWord_7406322) baseStart_7406322 baseEnd_7406322 := by
    simpa [prefixWord, tailWord_7406322, baseEnd_7406322] using wordTrace_append hprefix tailTrace_7406322
  have hstable : (prefixWord ++ tailWord_7406322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406322).length < 2 ^ (prefixWord ++ tailWord_7406322).sum := by decide
  have hdescent : baseEnd_7406322 < baseStart_7406322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406346 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_7406346 : Nat := 118140960795 + 7406346 * 2 ^ 59
def prefixEnd_7406346 : Nat := 4983230072969 + 3 ^ 40 * 7406346 * 2
def baseEnd_7406346 : Nat := 3803015391504584870913841

theorem tailTrace_7406346 : CollatzResearch.WordTrace tailWord_7406346 prefixEnd_7406346 3803015391504584870913841 := by
  unfold tailWord_7406346
  simp only [CollatzResearch.WordTrace]
  refine ⟨67532907706520205009455723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180087753884053880025215261 67532907706520205009455723)
  ·
    refine ⟨101299361559780307514183585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67532907706520205009455723 101299361559780307514183585)
    ·
      refine ⟨75974521169835230635637689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101299361559780307514183585 75974521169835230635637689)
      ·
        refine ⟨56980890877376422976728267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75974521169835230635637689 56980890877376422976728267)
        ·
          refine ⟨85471336316064634465092401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56980890877376422976728267 85471336316064634465092401)
          ·
            refine ⟨64103502237048475848819301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85471336316064634465092401 64103502237048475848819301)
            ·
              refine ⟨12019406669446589221653619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64103502237048475848819301 12019406669446589221653619)
              ·
                refine ⟨18029110004169883832480429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12019406669446589221653619 18029110004169883832480429)
                ·
                  refine ⟨6760916251563706437180161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18029110004169883832480429 6760916251563706437180161)
                  ·
                    refine ⟨5070687188672779827885121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6760916251563706437180161 5070687188672779827885121)
                    ·
                      refine ⟨3803015391504584870913841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070687188672779827885121 3803015391504584870913841)
                      ·
                        rfl

theorem cell23_7406346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_7406346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406346 prefixEnd_7406346 := by exact prefixLift 7406346
  have htrace : WordTrace (prefixWord ++ tailWord_7406346) baseStart_7406346 baseEnd_7406346 := by
    simpa [prefixWord, tailWord_7406346, baseEnd_7406346] using wordTrace_append hprefix tailTrace_7406346
  have hstable : (prefixWord ++ tailWord_7406346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406346).length < 2 ^ (prefixWord ++ tailWord_7406346).sum := by decide
  have hdescent : baseEnd_7406346 < baseStart_7406346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406397 : List Nat := [1, 4, 1, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7406397 : Nat := 118140960795 + 7406397 * 2 ^ 59
def prefixEnd_7406397 : Nat := 4983230072969 + 3 ^ 40 * 7406397 * 2
def baseEnd_7406397 : Nat := 3803041579017964171376107

theorem tailTrace_7406397 : CollatzResearch.WordTrace tailWord_7406397 prefixEnd_7406397 3803041579017964171376107 := by
  unfold tailWord_7406397
  simp only [CollatzResearch.WordTrace]
  refine ⟨270133490948896055747929445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180088993965930703831952963 270133490948896055747929445)
  ·
    refine ⟨50650029552918010452736771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270133490948896055747929445 50650029552918010452736771)
    ·
      refine ⟨75975044329377015679105157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50650029552918010452736771 75975044329377015679105157)
      ·
        refine ⟨14245320811758190439832217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75975044329377015679105157 14245320811758190439832217)
        ·
          refine ⟨10683990608818642829874163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14245320811758190439832217 10683990608818642829874163)
          ·
            refine ⟨16025985913227964244811245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683990608818642829874163 16025985913227964244811245)
            ·
              refine ⟨6009744717460486591804217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16025985913227964244811245 6009744717460486591804217)
              ·
                refine ⟨4507308538095364943853163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6009744717460486591804217 4507308538095364943853163)
                ·
                  refine ⟨6760962807143047415779745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507308538095364943853163 6760962807143047415779745)
                  ·
                    refine ⟨5070722105357285561834809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6760962807143047415779745 5070722105357285561834809)
                    ·
                      refine ⟨3803041579017964171376107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070722105357285561834809 3803041579017964171376107)
                      ·
                        rfl

theorem cell23_7406397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7406397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406397 prefixEnd_7406397 := by exact prefixLift 7406397
  have htrace : WordTrace (prefixWord ++ tailWord_7406397) baseStart_7406397 baseEnd_7406397 := by
    simpa [prefixWord, tailWord_7406397, baseEnd_7406397] using wordTrace_append hprefix tailTrace_7406397
  have hstable : (prefixWord ++ tailWord_7406397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406397).length < 2 ^ (prefixWord ++ tailWord_7406397).sum := by decide
  have hdescent : baseEnd_7406397 < baseStart_7406397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406415 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_7406415 : Nat := 118140960795 + 7406415 * 2 ^ 59
def prefixEnd_7406415 : Nat := 4983230072969 + 3 ^ 40 * 7406415 * 2
def baseEnd_7406415 : Nat := 3803050821669745100951023

theorem tailTrace_7406415 : CollatzResearch.WordTrace tailWord_7406415 prefixEnd_7406415 3803050821669745100951023 := by
  unfold tailWord_7406415
  simp only [CollatzResearch.WordTrace]
  refine ⟨270134147462830844822084699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180089431641887229881389799 270134147462830844822084699)
  ·
    refine ⟨405201221194246267233127049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270134147462830844822084699 405201221194246267233127049)
    ·
      refine ⟨303900915895684700424845287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405201221194246267233127049 303900915895684700424845287)
      ·
        refine ⟨455851373843527050637267931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303900915895684700424845287 455851373843527050637267931)
        ·
          refine ⟨683777060765290575955901897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455851373843527050637267931 683777060765290575955901897)
          ·
            refine ⟨512832795573967931966926423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683777060765290575955901897 512832795573967931966926423)
            ·
              refine ⟨769249193360951897950389635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512832795573967931966926423 769249193360951897950389635)
              ·
                refine ⟨1153873790041427846925584453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769249193360951897950389635 1153873790041427846925584453)
                ·
                  refine ⟨216351335632767721298547085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1153873790041427846925584453 216351335632767721298547085)
                  ·
                    refine ⟨81131750862287895486955157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216351335632767721298547085 81131750862287895486955157)
                    ·
                      refine ⟨3803050821669745100951023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81131750862287895486955157 3803050821669745100951023)
                      ·
                        rfl

theorem cell23_7406415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_7406415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406415 prefixEnd_7406415 := by exact prefixLift 7406415
  have htrace : WordTrace (prefixWord ++ tailWord_7406415) baseStart_7406415 baseEnd_7406415 := by
    simpa [prefixWord, tailWord_7406415, baseEnd_7406415] using wordTrace_append hprefix tailTrace_7406415
  have hstable : (prefixWord ++ tailWord_7406415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406415).length < 2 ^ (prefixWord ++ tailWord_7406415).sum := by decide
  have hdescent : baseEnd_7406415 < baseStart_7406415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406423 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 1, 3, 2]
def baseStart_7406423 : Nat := 118140960795 + 7406423 * 2 ^ 59
def prefixEnd_7406423 : Nat := 4983230072969 + 3 ^ 40 * 7406423 * 2
def baseEnd_7406423 : Nat := 3803054929514981069650987

theorem tailTrace_7406423 : CollatzResearch.WordTrace tailWord_7406423 prefixEnd_7406423 3803054929514981069650987 := by
  unfold tailWord_7406423
  simp only [CollatzResearch.WordTrace]
  refine ⟨270134439246801862188375923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180089626164534574792250615 270134439246801862188375923)
  ·
    refine ⟨405201658870202793282563885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270134439246801862188375923 405201658870202793282563885)
    ·
      refine ⟨151950622076326047480961457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405201658870202793282563885 151950622076326047480961457)
      ·
        refine ⟨113962966557244535610721093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151950622076326047480961457 113962966557244535610721093)
        ·
          refine ⟨21368056229483350427010205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113962966557244535610721093 21368056229483350427010205)
          ·
            refine ⟨8013021086056256410128827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21368056229483350427010205 8013021086056256410128827)
            ·
              refine ⟨12019531629084384615193241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8013021086056256410128827 12019531629084384615193241)
              ·
                refine ⟨9014648721813288461394931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12019531629084384615193241 9014648721813288461394931)
                ·
                  refine ⟨13521973082719932692092397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9014648721813288461394931 13521973082719932692092397)
                  ·
                    refine ⟨5070739906019974759534649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13521973082719932692092397 5070739906019974759534649)
                    ·
                      refine ⟨3803054929514981069650987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070739906019974759534649 3803054929514981069650987)
                      ·
                        rfl

theorem cell23_7406423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_7406423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406423 prefixEnd_7406423 := by exact prefixLift 7406423
  have htrace : WordTrace (prefixWord ++ tailWord_7406423) baseStart_7406423 baseEnd_7406423 := by
    simpa [prefixWord, tailWord_7406423, baseEnd_7406423] using wordTrace_append hprefix tailTrace_7406423
  have hstable : (prefixWord ++ tailWord_7406423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406423).length < 2 ^ (prefixWord ++ tailWord_7406423).sum := by decide
  have hdescent : baseEnd_7406423 < baseStart_7406423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406436 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_7406436 : Nat := 118140960795 + 7406436 * 2 ^ 59
def prefixEnd_7406436 : Nat := 4983230072969 + 3 ^ 40 * 7406436 * 2
def baseEnd_7406436 : Nat := 3803061604763489518788427

theorem tailTrace_7406436 : CollatzResearch.WordTrace tailWord_7406436 prefixEnd_7406436 3803061604763489518788427 := by
  unfold tailWord_7406436
  simp only [CollatzResearch.WordTrace]
  refine ⟨135067456697877382704299581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180089942263836510272399441 135067456697877382704299581)
  ·
    refine ⟨50650296261704018514112343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135067456697877382704299581 50650296261704018514112343)
    ·
      refine ⟨75975444392556027771168515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50650296261704018514112343 75975444392556027771168515)
      ·
        refine ⟨113963166588834041656752773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75975444392556027771168515 113963166588834041656752773)
        ·
          refine ⟨21368093735406382810641145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113963166588834041656752773 21368093735406382810641145)
          ·
            refine ⟨16026070301554787107980859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21368093735406382810641145 16026070301554787107980859)
            ·
              refine ⟨24039105452332180661971289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16026070301554787107980859 24039105452332180661971289)
              ·
                refine ⟨18029329089249135496478467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24039105452332180661971289 18029329089249135496478467)
                ·
                  refine ⟨27043993633873703244717701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18029329089249135496478467 27043993633873703244717701)
                  ·
                    refine ⟨5070748806351319358384569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27043993633873703244717701 5070748806351319358384569)
                    ·
                      refine ⟨3803061604763489518788427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070748806351319358384569 3803061604763489518788427)
                      ·
                        rfl

theorem cell23_7406436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_7406436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406436 prefixEnd_7406436 := by exact prefixLift 7406436
  have htrace : WordTrace (prefixWord ++ tailWord_7406436) baseStart_7406436 baseEnd_7406436 := by
    simpa [prefixWord, tailWord_7406436, baseEnd_7406436] using wordTrace_append hprefix tailTrace_7406436
  have hstable : (prefixWord ++ tailWord_7406436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406436).length < 2 ^ (prefixWord ++ tailWord_7406436).sum := by decide
  have hdescent : baseEnd_7406436 < baseStart_7406436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406453 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7406453 : Nat := 118140960795 + 7406453 * 2 ^ 59
def prefixEnd_7406453 : Nat := 4983230072969 + 3 ^ 40 * 7406453 * 2
def baseEnd_7406453 : Nat := 3803070333934615952275849

theorem tailTrace_7406453 : CollatzResearch.WordTrace tailWord_7406453 prefixEnd_7406453 3803070333934615952275849 := by
  unfold tailWord_7406453
  simp only [CollatzResearch.WordTrace]
  refine ⟨270135533436693177311968013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180090355624462118207978675 270135533436693177311968013)
  ·
    refine ⟨101300825038759941491988005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270135533436693177311968013 101300825038759941491988005)
    ·
      refine ⟨18993904694767489029747751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101300825038759941491988005 18993904694767489029747751)
      ·
        refine ⟨28490857042151233544621627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18993904694767489029747751 28490857042151233544621627)
        ·
          refine ⟨42736285563226850316932441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28490857042151233544621627 42736285563226850316932441)
          ·
            refine ⟨32052214172420137737699331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42736285563226850316932441 32052214172420137737699331)
            ·
              refine ⟨48078321258630206606548997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32052214172420137737699331 48078321258630206606548997)
              ·
                refine ⟨9014685235993163738727937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48078321258630206606548997 9014685235993163738727937)
                ·
                  refine ⟨6761013926994872804045953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9014685235993163738727937 6761013926994872804045953)
                  ·
                    refine ⟨5070760445246154603034465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6761013926994872804045953 5070760445246154603034465)
                    ·
                      refine ⟨3803070333934615952275849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070760445246154603034465 3803070333934615952275849)
                      ·
                        rfl

theorem cell23_7406453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7406453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406453 prefixEnd_7406453 := by exact prefixLift 7406453
  have htrace : WordTrace (prefixWord ++ tailWord_7406453) baseStart_7406453 baseEnd_7406453 := by
    simpa [prefixWord, tailWord_7406453, baseEnd_7406453] using wordTrace_append hprefix tailTrace_7406453
  have hstable : (prefixWord ++ tailWord_7406453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406453).length < 2 ^ (prefixWord ++ tailWord_7406453).sum := by decide
  have hdescent : baseEnd_7406453 < baseStart_7406453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406469 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_7406469 : Nat := 118140960795 + 7406469 * 2 ^ 59
def prefixEnd_7406469 : Nat := 4983230072969 + 3 ^ 40 * 7406469 * 2
def baseEnd_7406469 : Nat := 3803078549625087889675775

theorem tailTrace_7406469 : CollatzResearch.WordTrace tailWord_7406469 prefixEnd_7406469 3803078549625087889675775 := by
  unfold tailWord_7406469
  simp only [CollatzResearch.WordTrace]
  refine ⟨270136117004635212044550461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180090744669756808029700307 270136117004635212044550461)
  ·
    refine ⟨101301043876738204516706423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270136117004635212044550461 101301043876738204516706423)
    ·
      refine ⟨151951565815107306775059635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101301043876738204516706423 151951565815107306775059635)
      ·
        refine ⟨227927348722660960162589453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151951565815107306775059635 227927348722660960162589453)
        ·
          refine ⟨85472755770997860060971045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227927348722660960162589453 85472755770997860060971045)
          ·
            refine ⟨16026141707062098761432071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85472755770997860060971045 16026141707062098761432071)
            ·
              refine ⟨24039212560593148142148107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16026141707062098761432071 24039212560593148142148107)
              ·
                refine ⟨36058818840889722213222161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24039212560593148142148107 36058818840889722213222161)
                ·
                  refine ⟨27044114130667291659916621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36058818840889722213222161 27044114130667291659916621)
                  ·
                    refine ⟨10141542799000234372468733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27044114130667291659916621 10141542799000234372468733)
                    ·
                      refine ⟨3803078549625087889675775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10141542799000234372468733 3803078549625087889675775)
                      ·
                        rfl

theorem cell23_7406469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_7406469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406469 prefixEnd_7406469 := by exact prefixLift 7406469
  have htrace : WordTrace (prefixWord ++ tailWord_7406469) baseStart_7406469 baseEnd_7406469 := by
    simpa [prefixWord, tailWord_7406469, baseEnd_7406469] using wordTrace_append hprefix tailTrace_7406469
  have hstable : (prefixWord ++ tailWord_7406469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406469).length < 2 ^ (prefixWord ++ tailWord_7406469).sum := by decide
  have hdescent : baseEnd_7406469 < baseStart_7406469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406519 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 3, 4]
def baseStart_7406519 : Nat := 118140960795 + 7406519 * 2 ^ 59
def prefixEnd_7406519 : Nat := 4983230072969 + 3 ^ 40 * 7406519 * 2
def baseEnd_7406519 : Nat := 1267701407885937564683515

theorem tailTrace_7406519 : CollatzResearch.WordTrace tailWord_7406519 prefixEnd_7406519 1267701407885937564683515 := by
  unfold tailWord_7406519
  simp only [CollatzResearch.WordTrace]
  refine ⟨270137940654454070583870611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180091960436302713722580407 270137940654454070583870611)
  ·
    refine ⟨405206910981681105875805917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270137940654454070583870611 405206910981681105875805917)
    ·
      refine ⟨151952591618130414703427219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405206910981681105875805917 151952591618130414703427219)
      ·
        refine ⟨227928887427195622055140829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151952591618130414703427219 227928887427195622055140829)
        ·
          refine ⟨85473332785198358270677811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227928887427195622055140829 85473332785198358270677811)
          ·
            refine ⟨128209999177797537406016717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85473332785198358270677811 128209999177797537406016717)
            ·
              refine ⟨48078749691674076527256269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128209999177797537406016717 48078749691674076527256269)
              ·
                refine ⟨18029531134377778697721101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48078749691674076527256269 18029531134377778697721101)
                ·
                  refine ⟨6761074175391667011645413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18029531134377778697721101 6761074175391667011645413)
                  ·
                    refine ⟨1267701407885937564683515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761074175391667011645413 1267701407885937564683515)
                    ·
                      rfl

theorem cell23_7406519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_7406519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406519 prefixEnd_7406519 := by exact prefixLift 7406519
  have htrace : WordTrace (prefixWord ++ tailWord_7406519) baseStart_7406519 baseEnd_7406519 := by
    simpa [prefixWord, tailWord_7406519, baseEnd_7406519] using wordTrace_append hprefix tailTrace_7406519
  have hstable : (prefixWord ++ tailWord_7406519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406519).length < 2 ^ (prefixWord ++ tailWord_7406519).sum := by decide
  have hdescent : baseEnd_7406519 < baseStart_7406519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406522 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_7406522 : Nat := 118140960795 + 7406522 * 2 ^ 59
def prefixEnd_7406522 : Nat := 4983230072969 + 3 ^ 40 * 7406522 * 2
def baseEnd_7406522 : Nat := 3803105764099776182313031

theorem tailTrace_7406522 : CollatzResearch.WordTrace tailWord_7406522 prefixEnd_7406522 3803105764099776182313031 := by
  unfold tailWord_7406522
  simp only [CollatzResearch.WordTrace]
  refine ⟨67534512518360800524057455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180092033382295468064153213 67534512518360800524057455)
  ·
    refine ⟨101301768777541200786086183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67534512518360800524057455 101301768777541200786086183)
    ·
      refine ⟨151952653166311801179129275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101301768777541200786086183 151952653166311801179129275)
      ·
        refine ⟨227928979749467701768693913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151952653166311801179129275 227928979749467701768693913)
        ·
          refine ⟨170946734812100776326520435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227928979749467701768693913 170946734812100776326520435)
          ·
            refine ⟨256420102218151164489780653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170946734812100776326520435 256420102218151164489780653)
            ·
              refine ⟨96157538331806686683667745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256420102218151164489780653 96157538331806686683667745)
              ·
                refine ⟨72118153748855015012750809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96157538331806686683667745 72118153748855015012750809)
                ·
                  refine ⟨54088615311641261259563107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72118153748855015012750809 54088615311641261259563107)
                  ·
                    refine ⟨81132922967461891889344661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54088615311641261259563107 81132922967461891889344661)
                    ·
                      refine ⟨3803105764099776182313031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81132922967461891889344661 3803105764099776182313031)
                      ·
                        rfl

theorem cell23_7406522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_7406522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406522 prefixEnd_7406522 := by exact prefixLift 7406522
  have htrace : WordTrace (prefixWord ++ tailWord_7406522) baseStart_7406522 baseEnd_7406522 := by
    simpa [prefixWord, tailWord_7406522, baseEnd_7406522] using wordTrace_append hprefix tailTrace_7406522
  have hstable : (prefixWord ++ tailWord_7406522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406522).length < 2 ^ (prefixWord ++ tailWord_7406522).sum := by decide
  have hdescent : baseEnd_7406522 < baseStart_7406522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406526 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_7406526 : Nat := 118140960795 + 7406526 * 2 ^ 59
def prefixEnd_7406526 : Nat := 4983230072969 + 3 ^ 40 * 7406526 * 2
def baseEnd_7406526 : Nat := 3803107818022394166663013

theorem tailTrace_7406526 : CollatzResearch.WordTrace tailWord_7406526 prefixEnd_7406526 3803107818022394166663013 := by
  unfold tailWord_7406526
  simp only [CollatzResearch.WordTrace]
  refine ⟨33767274495678588847421929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180092130643619140519583621 33767274495678588847421929)
  ·
    refine ⟨25325455871758941635566447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33767274495678588847421929 25325455871758941635566447)
    ·
      refine ⟨37988183807638412453349671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25325455871758941635566447 37988183807638412453349671)
      ·
        refine ⟨56982275711457618680024507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37988183807638412453349671 56982275711457618680024507)
        ·
          refine ⟨85473413567186428020036761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56982275711457618680024507 85473413567186428020036761)
          ·
            refine ⟨64105060175389821015027571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85473413567186428020036761 64105060175389821015027571)
            ·
              refine ⟨96157590263084731522541357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64105060175389821015027571 96157590263084731522541357)
              ·
                refine ⟨36059096348656774320953009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96157590263084731522541357 36059096348656774320953009)
                ·
                  refine ⟨27044322261492580740714757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36059096348656774320953009 27044322261492580740714757)
                  ·
                    refine ⟨5070810424029858888884017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27044322261492580740714757 5070810424029858888884017)
                    ·
                      refine ⟨3803107818022394166663013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070810424029858888884017 3803107818022394166663013)
                      ·
                        rfl

theorem cell23_7406526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_7406526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406526 prefixEnd_7406526 := by exact prefixLift 7406526
  have htrace : WordTrace (prefixWord ++ tailWord_7406526) baseStart_7406526 baseEnd_7406526 := by
    simpa [prefixWord, tailWord_7406526, baseEnd_7406526] using wordTrace_append hprefix tailTrace_7406526
  have hstable : (prefixWord ++ tailWord_7406526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406526).length < 2 ^ (prefixWord ++ tailWord_7406526).sum := by decide
  have hdescent : baseEnd_7406526 < baseStart_7406526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406546 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_7406546 : Nat := 118140960795 + 7406546 * 2 ^ 59
def prefixEnd_7406546 : Nat := 4983230072969 + 3 ^ 40 * 7406546 * 2
def baseEnd_7406546 : Nat := 3803118087635484088412921

theorem tailTrace_7406546 : CollatzResearch.WordTrace tailWord_7406546 prefixEnd_7406546 3803118087635484088412921 := by
  unfold tailWord_7406546
  simp only [CollatzResearch.WordTrace]
  refine ⟨67534731356339063548775873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180092616950237502796735661 67534731356339063548775873)
  ·
    refine ⟨50651048517254297661581905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67534731356339063548775873 50651048517254297661581905)
    ·
      refine ⟨37988286387940723246186429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50651048517254297661581905 37988286387940723246186429)
      ·
        refine ⟨14245607395477771217319911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37988286387940723246186429 14245607395477771217319911)
        ·
          refine ⟨21368411093216656825979867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14245607395477771217319911 21368411093216656825979867)
          ·
            refine ⟨32052616639824985238969801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21368411093216656825979867 32052616639824985238969801)
            ·
              refine ⟨24039462479868738929227351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32052616639824985238969801 24039462479868738929227351)
              ·
                refine ⟨36059193719803108393841027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24039462479868738929227351 36059193719803108393841027)
                ·
                  refine ⟨54088790579704662590761541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36059193719803108393841027 54088790579704662590761541)
                  ·
                    refine ⟨10141648233694624235767789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54088790579704662590761541 10141648233694624235767789)
                    ·
                      refine ⟨3803118087635484088412921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10141648233694624235767789 3803118087635484088412921)
                      ·
                        rfl

theorem cell23_7406546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_7406546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406546 prefixEnd_7406546 := by exact prefixLift 7406546
  have htrace : WordTrace (prefixWord ++ tailWord_7406546) baseStart_7406546 baseEnd_7406546 := by
    simpa [prefixWord, tailWord_7406546, baseEnd_7406546] using wordTrace_append hprefix tailTrace_7406546
  have hstable : (prefixWord ++ tailWord_7406546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406546).length < 2 ^ (prefixWord ++ tailWord_7406546).sum := by decide
  have hdescent : baseEnd_7406546 < baseStart_7406546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406553 : List Nat := [1, 2, 1, 2, 5, 1, 3, 3, 1, 4]
def baseStart_7406553 : Nat := 118140960795 + 7406553 * 2 ^ 59
def prefixEnd_7406553 : Nat := 4983230072969 + 3 ^ 40 * 7406553 * 2
def baseEnd_7406553 : Nat := 1267707227333355187008463

theorem tailTrace_7406553 : CollatzResearch.WordTrace tailWord_7406553 prefixEnd_7406553 1267707227333355187008463 := by
  unfold tailWord_7406553
  simp only [CollatzResearch.WordTrace]
  refine ⟨270139180736330894390608313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180092787157553929593738875 270139180736330894390608313)
  ·
    refine ⟨202604385552248170792956235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270139180736330894390608313 202604385552248170792956235)
    ·
      refine ⟨303906578328372256189434353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202604385552248170792956235 303906578328372256189434353)
      ·
        refine ⟨227929933746279192142075765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303906578328372256189434353 227929933746279192142075765)
        ·
          refine ⟨21368431288713674263319603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227929933746279192142075765 21368431288713674263319603)
          ·
            refine ⟨32052646933070511394979405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21368431288713674263319603 32052646933070511394979405)
            ·
              refine ⟨12019742599901441773117277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32052646933070511394979405 12019742599901441773117277)
              ·
                refine ⟨4507403474963040664918979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12019742599901441773117277 4507403474963040664918979)
                ·
                  refine ⟨6761105212444560997378469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507403474963040664918979 6761105212444560997378469)
                  ·
                    refine ⟨1267707227333355187008463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761105212444560997378469 1267707227333355187008463)
                    ·
                      rfl

theorem cell23_7406553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 4].length) (baseStart_7406553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406553 prefixEnd_7406553 := by exact prefixLift 7406553
  have htrace : WordTrace (prefixWord ++ tailWord_7406553) baseStart_7406553 baseEnd_7406553 := by
    simpa [prefixWord, tailWord_7406553, baseEnd_7406553] using wordTrace_append hprefix tailTrace_7406553
  have hstable : (prefixWord ++ tailWord_7406553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406553).length < 2 ^ (prefixWord ++ tailWord_7406553).sum := by decide
  have hdescent : baseEnd_7406553 < baseStart_7406553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406569 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 9, 2]
def baseStart_7406569 : Nat := 118140960795 + 7406569 * 2 ^ 59
def prefixEnd_7406569 : Nat := 4983230072969 + 3 ^ 40 * 7406569 * 2
def baseEnd_7406569 : Nat := 3803129897690537498425315

theorem tailTrace_7406569 : CollatzResearch.WordTrace tailWord_7406569 prefixEnd_7406569 3803129897690537498425315 := by
  unfold tailWord_7406569
  simp only [CollatzResearch.WordTrace]
  refine ⟨270139764304272929123190761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180093176202848619415460507 270139764304272929123190761)
  ·
    refine ⟨202604823228204696842393071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270139764304272929123190761 202604823228204696842393071)
    ·
      refine ⟨303907234842307045263589607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202604823228204696842393071 303907234842307045263589607)
      ·
        refine ⟨455860852263460567895384411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303907234842307045263589607 455860852263460567895384411)
        ·
          refine ⟨683791278395190851843076617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455860852263460567895384411 683791278395190851843076617)
          ·
            refine ⟨512843458796393138882307463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683791278395190851843076617 512843458796393138882307463)
            ·
              refine ⟨769265188194589708323461195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512843458796393138882307463 769265188194589708323461195)
              ·
                refine ⟨1153897782291884562485191793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769265188194589708323461195 1153897782291884562485191793)
                ·
                  refine ⟨865423336718913421863893845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1153897782291884562485191793 865423336718913421863893845)
                  ·
                    refine ⟨5070839863587383331233753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 865423336718913421863893845 5070839863587383331233753)
                    ·
                      refine ⟨3803129897690537498425315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070839863587383331233753 3803129897690537498425315)
                      ·
                        rfl

theorem cell23_7406569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 9, 2].length) (baseStart_7406569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406569 prefixEnd_7406569 := by exact prefixLift 7406569
  have htrace : WordTrace (prefixWord ++ tailWord_7406569) baseStart_7406569 baseEnd_7406569 := by
    simpa [prefixWord, tailWord_7406569, baseEnd_7406569] using wordTrace_append hprefix tailTrace_7406569
  have hstable : (prefixWord ++ tailWord_7406569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406569).length < 2 ^ (prefixWord ++ tailWord_7406569).sum := by decide
  have hdescent : baseEnd_7406569 < baseStart_7406569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406570 : List Nat := [3, 1, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_7406570 : Nat := 118140960795 + 7406570 * 2 ^ 59
def prefixEnd_7406570 : Nat := 4983230072969 + 3 ^ 40 * 7406570 * 2
def baseEnd_7406570 : Nat := 1267710137057063998170937

theorem tailTrace_7406570 : CollatzResearch.WordTrace tailWord_7406570 prefixEnd_7406570 1267710137057063998170937 := by
  unfold tailWord_7406570
  simp only [CollatzResearch.WordTrace]
  refine ⟨67534950194317326573494291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180093200518179537529318109 67534950194317326573494291)
  ·
    refine ⟨101302425291475989860241437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67534950194317326573494291 101302425291475989860241437)
    ·
      refine ⟨37988409484303496197590539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101302425291475989860241437 37988409484303496197590539)
      ·
        refine ⟨56982614226455244296385809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37988409484303496197590539 56982614226455244296385809)
        ·
          refine ⟨42736960669841433222289357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56982614226455244296385809 42736960669841433222289357)
          ·
            refine ⟨16026360251190537458358509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42736960669841433222289357 16026360251190537458358509)
            ·
              refine ⟨6009885094196451546884441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16026360251190537458358509 6009885094196451546884441)
              ·
                refine ⟨4507413820647338660163331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6009885094196451546884441 4507413820647338660163331)
                ·
                  refine ⟨6761120730971007990244997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507413820647338660163331 6761120730971007990244997)
                  ·
                    refine ⟨1267710137057063998170937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761120730971007990244997 1267710137057063998170937)
                    ·
                      rfl

theorem cell23_7406570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_7406570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406570 prefixEnd_7406570 := by exact prefixLift 7406570
  have htrace : WordTrace (prefixWord ++ tailWord_7406570) baseStart_7406570 baseEnd_7406570 := by
    simpa [prefixWord, tailWord_7406570, baseEnd_7406570] using wordTrace_append hprefix tailTrace_7406570
  have hstable : (prefixWord ++ tailWord_7406570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406570).length < 2 ^ (prefixWord ++ tailWord_7406570).sum := by decide
  have hdescent : baseEnd_7406570 < baseStart_7406570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406572 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_7406572 : Nat := 118140960795 + 7406572 * 2 ^ 59
def prefixEnd_7406572 : Nat := 4983230072969 + 3 ^ 40 * 7406572 * 2
def baseEnd_7406572 : Nat := 3803131438132500986687801

theorem tailTrace_7406572 : CollatzResearch.WordTrace tailWord_7406572 prefixEnd_7406572 3803131438132500986687801 := by
  unfold tailWord_7406572
  simp only [CollatzResearch.WordTrace]
  refine ⟨135069936861631030317774985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180093249148841373757033313 135069936861631030317774985)
  ·
    refine ⟨101302452646223272738331239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135069936861631030317774985 101302452646223272738331239)
    ·
      refine ⟨151953678969334909107496859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101302452646223272738331239 151953678969334909107496859)
      ·
        refine ⟨227930518454002363661245289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151953678969334909107496859 227930518454002363661245289)
        ·
          refine ⟨170947888840501772745933967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227930518454002363661245289 170947888840501772745933967)
          ·
            refine ⟨256421833260752659118900951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170947888840501772745933967 256421833260752659118900951)
            ·
              refine ⟨384632749891128988678351427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256421833260752659118900951 384632749891128988678351427)
              ·
                refine ⟨576949124836693483017527141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384632749891128988678351427 576949124836693483017527141)
                ·
                  refine ⟨108177960906880028065786339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576949124836693483017527141 108177960906880028065786339)
                  ·
                    refine ⟨162266941360320042098679509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108177960906880028065786339 162266941360320042098679509)
                    ·
                      refine ⟨3803131438132500986687801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162266941360320042098679509 3803131438132500986687801)
                      ·
                        rfl

theorem cell23_7406572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_7406572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406572 prefixEnd_7406572 := by exact prefixLift 7406572
  have htrace : WordTrace (prefixWord ++ tailWord_7406572) baseStart_7406572 baseEnd_7406572 := by
    simpa [prefixWord, tailWord_7406572, baseEnd_7406572] using wordTrace_append hprefix tailTrace_7406572
  have hstable : (prefixWord ++ tailWord_7406572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406572).length < 2 ^ (prefixWord ++ tailWord_7406572).sum := by decide
  have hdescent : baseEnd_7406572 < baseStart_7406572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406603 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 2, 3, 2]
def baseStart_7406603 : Nat := 118140960795 + 7406603 * 2 ^ 59
def prefixEnd_7406603 : Nat := 4983230072969 + 3 ^ 40 * 7406603 * 2
def baseEnd_7406603 : Nat := 3803147356032790365400159

theorem tailTrace_7406603 : CollatzResearch.WordTrace tailWord_7406603 prefixEnd_7406603 3803147356032790365400159 := by
  unfold tailWord_7406603
  simp only [CollatzResearch.WordTrace]
  refine ⟨270141004386149752929928463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180094002924099835286618975 270141004386149752929928463)
  ·
    refine ⟨405211506579224629394892695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270141004386149752929928463 405211506579224629394892695)
    ·
      refine ⟨607817259868836944092339043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405211506579224629394892695 607817259868836944092339043)
      ·
        refine ⟨911725889803255416138508565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607817259868836944092339043 911725889803255416138508565)
        ·
          refine ⟨42737151084527597631492589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 911725889803255416138508565 42737151084527597631492589)
          ·
            refine ⟨16026431656697849111809721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42737151084527597631492589 16026431656697849111809721)
            ·
              refine ⟨12019823742523386833857291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16026431656697849111809721 12019823742523386833857291)
              ·
                refine ⟨18029735613785080250785937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12019823742523386833857291 18029735613785080250785937)
                ·
                  refine ⟨13522301710338810188089453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18029735613785080250785937 13522301710338810188089453)
                  ·
                    refine ⟨5070863141377053820533545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13522301710338810188089453 5070863141377053820533545)
                    ·
                      refine ⟨3803147356032790365400159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070863141377053820533545 3803147356032790365400159)
                      ·
                        rfl

theorem cell23_7406603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 3, 2].length) (baseStart_7406603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406603 prefixEnd_7406603 := by exact prefixLift 7406603
  have htrace : WordTrace (prefixWord ++ tailWord_7406603) baseStart_7406603 baseEnd_7406603 := by
    simpa [prefixWord, tailWord_7406603, baseEnd_7406603] using wordTrace_append hprefix tailTrace_7406603
  have hstable : (prefixWord ++ tailWord_7406603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406603).length < 2 ^ (prefixWord ++ tailWord_7406603).sum := by decide
  have hdescent : baseEnd_7406603 < baseStart_7406603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406609 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 6, 4]
def baseStart_7406609 : Nat := 118140960795 + 7406609 * 2 ^ 59
def prefixEnd_7406609 : Nat := 4983230072969 + 3 ^ 40 * 7406609 * 2
def baseEnd_7406609 : Nat := 1267716812305572447308377

theorem tailTrace_7406609 : CollatzResearch.WordTrace tailWord_7406609 prefixEnd_7406609 1267716812305572447308377 := by
  unfold tailWord_7406609
  simp only [CollatzResearch.WordTrace]
  refine ⟨270141223224128015954646881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180094148816085343969764587 270141223224128015954646881)
  ·
    refine ⟨202605917418096011965985161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270141223224128015954646881 202605917418096011965985161)
    ·
      refine ⟨151954438063572008974488871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202605917418096011965985161 151954438063572008974488871)
      ·
        refine ⟨227931657095358013461733307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151954438063572008974488871 227931657095358013461733307)
        ·
          refine ⟨341897485643037020192599961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227931657095358013461733307 341897485643037020192599961)
          ·
            refine ⟨256423114232277765144449971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341897485643037020192599961 256423114232277765144449971)
            ·
              refine ⟨384634671348416647716674957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256423114232277765144449971 384634671348416647716674957)
              ·
                refine ⟨144238001755656242893753109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384634671348416647716674957 144238001755656242893753109)
                ·
                  refine ⟨6761156332296386385644677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144238001755656242893753109 6761156332296386385644677)
                  ·
                    refine ⟨1267716812305572447308377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761156332296386385644677 1267716812305572447308377)
                    ·
                      rfl

theorem cell23_7406609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_7406609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406609 prefixEnd_7406609 := by exact prefixLift 7406609
  have htrace : WordTrace (prefixWord ++ tailWord_7406609) baseStart_7406609 baseEnd_7406609 := by
    simpa [prefixWord, tailWord_7406609, baseEnd_7406609] using wordTrace_append hprefix tailTrace_7406609
  have hstable : (prefixWord ++ tailWord_7406609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406609).length < 2 ^ (prefixWord ++ tailWord_7406609).sum := by decide
  have hdescent : baseEnd_7406609 < baseStart_7406609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406613 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_7406613 : Nat := 118140960795 + 7406613 * 2 ^ 59
def prefixEnd_7406613 : Nat := 4983230072969 + 3 ^ 40 * 7406613 * 2
def baseEnd_7406613 : Nat := 1267717496946445108758371

theorem tailTrace_7406613 : CollatzResearch.WordTrace tailWord_7406613 prefixEnd_7406613 1267717496946445108758371 := by
  unfold tailWord_7406613
  simp only [CollatzResearch.WordTrace]
  refine ⟨270141369116113524637792493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180094246077409016425194995 270141369116113524637792493)
  ·
    refine ⟨101303013418542571739172185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270141369116113524637792493 101303013418542571739172185)
    ·
      refine ⟨75977260063906928804379139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101303013418542571739172185 75977260063906928804379139)
      ·
        refine ⟨113965890095860393206568709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75977260063906928804379139 113965890095860393206568709)
        ·
          refine ⟨21368604392973823726231633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113965890095860393206568709 21368604392973823726231633)
          ·
            refine ⟨16026453294730367794673725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21368604392973823726231633 16026453294730367794673725)
            ·
              refine ⟨6009919985523887923002647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16026453294730367794673725 6009919985523887923002647)
              ·
                refine ⟨9014879978285831884503971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009919985523887923002647 9014879978285831884503971)
                ·
                  refine ⟨13522319967428747826755957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9014879978285831884503971 13522319967428747826755957)
                  ·
                    refine ⟨1267717496946445108758371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13522319967428747826755957 1267717496946445108758371)
                    ·
                      rfl

theorem cell23_7406613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_7406613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406613 prefixEnd_7406613 := by exact prefixLift 7406613
  have htrace : WordTrace (prefixWord ++ tailWord_7406613) baseStart_7406613 baseEnd_7406613 := by
    simpa [prefixWord, tailWord_7406613, baseEnd_7406613] using wordTrace_append hprefix tailTrace_7406613
  have hstable : (prefixWord ++ tailWord_7406613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406613).length < 2 ^ (prefixWord ++ tailWord_7406613).sum := by decide
  have hdescent : baseEnd_7406613 < baseStart_7406613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406627 : List Nat := [1, 1, 1, 4, 3, 4, 2, 2, 1, 1, 3]
def baseStart_7406627 : Nat := 118140960795 + 7406627 * 2 ^ 59
def prefixEnd_7406627 : Nat := 4983230072969 + 3 ^ 40 * 7406627 * 2
def baseEnd_7406627 : Nat := 3803159679568498271500049

theorem tailTrace_7406627 : CollatzResearch.WordTrace tailWord_7406627 prefixEnd_7406627 3803159679568498271500049 := by
  unfold tailWord_7406627
  simp only [CollatzResearch.WordTrace]
  refine ⟨270141879738062805028802135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180094586492041870019201423 270141879738062805028802135)
  ·
    refine ⟨405212819607094207543203203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270141879738062805028802135 405212819607094207543203203)
    ·
      refine ⟨607819229410641311314804805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405212819607094207543203203 607819229410641311314804805)
      ·
        refine ⟨113966105514495245871525901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 607819229410641311314804805 113966105514495245871525901)
        ·
          refine ⟨42737289567935717201822213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113966105514495245871525901 42737289567935717201822213)
          ·
            refine ⟨8013241793987946975341665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42737289567935717201822213 8013241793987946975341665)
            ·
              refine ⟨6009931345490960231506249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8013241793987946975341665 6009931345490960231506249)
              ·
                refine ⟨4507448509118220173629687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6009931345490960231506249 4507448509118220173629687)
                ·
                  refine ⟨6761172763677330260444531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507448509118220173629687 6761172763677330260444531)
                  ·
                    refine ⟨10141759145515995390666797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6761172763677330260444531 10141759145515995390666797)
                    ·
                      refine ⟨3803159679568498271500049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10141759145515995390666797 3803159679568498271500049)
                      ·
                        rfl

theorem cell23_7406627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_7406627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406627 prefixEnd_7406627 := by exact prefixLift 7406627
  have htrace : WordTrace (prefixWord ++ tailWord_7406627) baseStart_7406627 baseEnd_7406627 := by
    simpa [prefixWord, tailWord_7406627, baseEnd_7406627] using wordTrace_append hprefix tailTrace_7406627
  have hstable : (prefixWord ++ tailWord_7406627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406627).length < 2 ^ (prefixWord ++ tailWord_7406627).sum := by decide
  have hdescent : baseEnd_7406627 < baseStart_7406627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406629 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_7406629 : Nat := 118140960795 + 7406629 * 2 ^ 59
def prefixEnd_7406629 : Nat := 4983230072969 + 3 ^ 40 * 7406629 * 2
def baseEnd_7406629 : Nat := 3803160706529807263675039

theorem tailTrace_7406629 : CollatzResearch.WordTrace tailWord_7406629 prefixEnd_7406629 3803160706529807263675039 := by
  unfold tailWord_7406629
  simp only [CollatzResearch.WordTrace]
  refine ⟨270141952684055559370374941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180094635122703706246916627 270141952684055559370374941)
  ·
    refine ⟨101303232256520834763890603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270141952684055559370374941 101303232256520834763890603)
    ·
      refine ⟨151954848384781252145835905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101303232256520834763890603 151954848384781252145835905)
      ·
        refine ⟨113966136288585939109376929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151954848384781252145835905 113966136288585939109376929)
        ·
          refine ⟨85474602216439454332032697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113966136288585939109376929 85474602216439454332032697)
          ·
            refine ⟨64105951662329590749024523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85474602216439454332032697 64105951662329590749024523)
            ·
              refine ⟨96158927493494386123536785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64105951662329590749024523 96158927493494386123536785)
              ·
                refine ⟨72119195620120789592652589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96158927493494386123536785 72119195620120789592652589)
                ·
                  refine ⟨27044698357545296097244721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72119195620120789592652589 27044698357545296097244721)
                  ·
                    refine ⟨20283523768158972072933541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27044698357545296097244721 20283523768158972072933541)
                    ·
                      refine ⟨3803160706529807263675039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20283523768158972072933541 3803160706529807263675039)
                      ·
                        rfl

theorem cell23_7406629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_7406629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406629 prefixEnd_7406629 := by exact prefixLift 7406629
  have htrace : WordTrace (prefixWord ++ tailWord_7406629) baseStart_7406629 baseEnd_7406629 := by
    simpa [prefixWord, tailWord_7406629, baseEnd_7406629] using wordTrace_append hprefix tailTrace_7406629
  have hstable : (prefixWord ++ tailWord_7406629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406629).length < 2 ^ (prefixWord ++ tailWord_7406629).sum := by decide
  have hdescent : baseEnd_7406629 < baseStart_7406629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406666 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_7406666 : Nat := 118140960795 + 7406666 * 2 ^ 59
def prefixEnd_7406666 : Nat := 4983230072969 + 3 ^ 40 * 7406666 * 2
def baseEnd_7406666 : Nat := 3803179705314023618912369

theorem tailTrace_7406666 : CollatzResearch.WordTrace tailWord_7406666 prefixEnd_7406666 3803179705314023618912369 := by
  unfold tailWord_7406666
  simp only [CollatzResearch.WordTrace]
  refine ⟨67535825546230378672367963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180095534789947676459647901 67535825546230378672367963)
  ·
    refine ⟨101303738319345568008551945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67535825546230378672367963 101303738319345568008551945)
    ·
      refine ⟨75977803739509176006413959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101303738319345568008551945 75977803739509176006413959)
      ·
        refine ⟨113966705609263764009620939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75977803739509176006413959 113966705609263764009620939)
        ·
          refine ⟨170950058413895646014431409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113966705609263764009620939 170950058413895646014431409)
          ·
            refine ⟨128212543810421734510823557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170950058413895646014431409 128212543810421734510823557)
            ·
              refine ⟨24039851964454075220779417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128212543810421734510823557 24039851964454075220779417)
              ·
                refine ⟨18029888973340556415584563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24039851964454075220779417 18029888973340556415584563)
                ·
                  refine ⟨27044833460010834623376845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18029888973340556415584563 27044833460010834623376845)
                  ·
                    refine ⟨10141812547504062983766317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27044833460010834623376845 10141812547504062983766317)
                    ·
                      refine ⟨3803179705314023618912369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10141812547504062983766317 3803179705314023618912369)
                      ·
                        rfl

theorem cell23_7406666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_7406666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406666 prefixEnd_7406666 := by exact prefixLift 7406666
  have htrace : WordTrace (prefixWord ++ tailWord_7406666) baseStart_7406666 baseEnd_7406666 := by
    simpa [prefixWord, tailWord_7406666, baseEnd_7406666] using wordTrace_append hprefix tailTrace_7406666
  have hstable : (prefixWord ++ tailWord_7406666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406666).length < 2 ^ (prefixWord ++ tailWord_7406666).sum := by decide
  have hdescent : baseEnd_7406666 < baseStart_7406666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406689 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_7406689 : Nat := 118140960795 + 7406689 * 2 ^ 59
def prefixEnd_7406689 : Nat := 4983230072969 + 3 ^ 40 * 7406689 * 2
def baseEnd_7406689 : Nat := 3803191515369077028924763

theorem tailTrace_7406689 : CollatzResearch.WordTrace tailWord_7406689 prefixEnd_7406689 3803191515369077028924763 := by
  unfold tailWord_7406689
  simp only [CollatzResearch.WordTrace]
  refine ⟨270144141063838189617559121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180096094042558793078372747 270144141063838189617559121)
  ·
    refine ⟨202608105797878642213169341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270144141063838189617559121 202608105797878642213169341)
    ·
      refine ⟨75978039674204490829938503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202608105797878642213169341 75978039674204490829938503)
      ·
        refine ⟨113967059511306736244907755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75978039674204490829938503 113967059511306736244907755)
        ·
          refine ⟨170950589266960104367361633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113967059511306736244907755 170950589266960104367361633)
          ·
            refine ⟨128212941950220078275521225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170950589266960104367361633 128212941950220078275521225)
            ·
              refine ⟨96159706462665058706640919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128212941950220078275521225 96159706462665058706640919)
              ·
                refine ⟨144239559693997588059961379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96159706462665058706640919 144239559693997588059961379)
                ·
                  refine ⟨216359339540996382089942069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144239559693997588059961379 216359339540996382089942069)
                  ·
                    refine ⟨20283688081968410820932069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216359339540996382089942069 20283688081968410820932069)
                    ·
                      refine ⟨3803191515369077028924763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20283688081968410820932069 3803191515369077028924763)
                      ·
                        rfl

theorem cell23_7406689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_7406689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406689 prefixEnd_7406689 := by exact prefixLift 7406689
  have htrace : WordTrace (prefixWord ++ tailWord_7406689) baseStart_7406689 baseEnd_7406689 := by
    simpa [prefixWord, tailWord_7406689, baseEnd_7406689] using wordTrace_append hprefix tailTrace_7406689
  have hstable : (prefixWord ++ tailWord_7406689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406689).length < 2 ^ (prefixWord ++ tailWord_7406689).sum := by decide
  have hdescent : baseEnd_7406689 < baseStart_7406689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406700 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 3]
def baseStart_7406700 : Nat := 118140960795 + 7406700 * 2 ^ 59
def prefixEnd_7406700 : Nat := 4983230072969 + 3 ^ 40 * 7406700 * 2
def baseEnd_7406700 : Nat := 3803197163656276485887213

theorem tailTrace_7406700 : CollatzResearch.WordTrace tailWord_7406700 prefixEnd_7406700 3803197163656276485887213 := by
  unfold tailWord_7406700
  simp only [CollatzResearch.WordTrace]
  refine ⟨135072271133399169248104777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180096361511198892330806369 135072271133399169248104777)
  ·
    refine ⟨101304203350049376936078583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135072271133399169248104777 101304203350049376936078583)
    ·
      refine ⟨151956305025074065404117875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101304203350049376936078583 151956305025074065404117875)
      ·
        refine ⟨227934457537611098106176813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151956305025074065404117875 227934457537611098106176813)
        ·
          refine ⟨85475421576604161789816305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227934457537611098106176813 85475421576604161789816305)
          ·
            refine ⟨64106566182453121342362229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85475421576604161789816305 64106566182453121342362229)
            ·
              refine ⟨6009990579604980125846459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64106566182453121342362229 6009990579604980125846459)
              ·
                refine ⟨9014985869407470188769689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009990579604980125846459 9014985869407470188769689)
                ·
                  refine ⟨6761239402055602641577267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9014985869407470188769689 6761239402055602641577267)
                  ·
                    refine ⟨10141859103083403962365901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6761239402055602641577267 10141859103083403962365901)
                    ·
                      refine ⟨3803197163656276485887213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10141859103083403962365901 3803197163656276485887213)
                      ·
                        rfl

theorem cell23_7406700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_7406700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406700 prefixEnd_7406700 := by exact prefixLift 7406700
  have htrace : WordTrace (prefixWord ++ tailWord_7406700) baseStart_7406700 baseEnd_7406700 := by
    simpa [prefixWord, tailWord_7406700, baseEnd_7406700] using wordTrace_append hprefix tailTrace_7406700
  have hstable : (prefixWord ++ tailWord_7406700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406700).length < 2 ^ (prefixWord ++ tailWord_7406700).sum := by decide
  have hdescent : baseEnd_7406700 < baseStart_7406700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406723 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 6, 2, 2]
def baseStart_7406723 : Nat := 118140960795 + 7406723 * 2 ^ 59
def prefixEnd_7406723 : Nat := 4983230072969 + 3 ^ 40 * 7406723 * 2
def baseEnd_7406723 : Nat := 3803208973711329895899607

theorem tailTrace_7406723 : CollatzResearch.WordTrace tailWord_7406723 prefixEnd_7406723 3803208973711329895899607 := by
  unfold tailWord_7406723
  simp only [CollatzResearch.WordTrace]
  refine ⟨270145381145715013424296823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180096920763810008949531215 270145381145715013424296823)
  ·
    refine ⟨405218071718572520136445235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270145381145715013424296823 405218071718572520136445235)
    ·
      refine ⟨607827107577858780204667853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405218071718572520136445235 607827107577858780204667853)
      ·
        refine ⟨227935165341697042576750445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607827107577858780204667853 227935165341697042576750445)
        ·
          refine ⟨85475687003136390966281417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227935165341697042576750445 85475687003136390966281417)
          ·
            refine ⟨64106765252352293224711063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85475687003136390966281417 64106765252352293224711063)
            ·
              refine ⟨96160147878528439837066595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64106765252352293224711063 96160147878528439837066595)
              ·
                refine ⟨144240221817792659755599893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96160147878528439837066595 144240221817792659755599893)
                ·
                  refine ⟨6761260397709030926043745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144240221817792659755599893 6761260397709030926043745)
                  ·
                    refine ⟨5070945298281773194532809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6761260397709030926043745 5070945298281773194532809)
                    ·
                      refine ⟨3803208973711329895899607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070945298281773194532809 3803208973711329895899607)
                      ·
                        rfl

theorem cell23_7406723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_7406723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406723 prefixEnd_7406723 := by exact prefixLift 7406723
  have htrace : WordTrace (prefixWord ++ tailWord_7406723) baseStart_7406723 baseEnd_7406723 := by
    simpa [prefixWord, tailWord_7406723, baseEnd_7406723] using wordTrace_append hprefix tailTrace_7406723
  have hstable : (prefixWord ++ tailWord_7406723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406723).length < 2 ^ (prefixWord ++ tailWord_7406723).sum := by decide
  have hdescent : baseEnd_7406723 < baseStart_7406723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406757 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 2, 2, 2]
def baseStart_7406757 : Nat := 118140960795 + 7406757 * 2 ^ 59
def prefixEnd_7406757 : Nat := 4983230072969 + 3 ^ 40 * 7406757 * 2
def baseEnd_7406757 : Nat := 3803226432053582762874451

theorem tailTrace_7406757 : CollatzResearch.WordTrace tailWord_7406757 prefixEnd_7406757 3803226432053582762874451 := by
  unfold tailWord_7406757
  simp only [CollatzResearch.WordTrace]
  refine ⟨270146621227591837231034525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180097747485061224820689683 270146621227591837231034525)
  ·
    refine ⟨101304982960346938961637947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270146621227591837231034525 101304982960346938961637947)
    ·
      refine ⟨151957474440520408442456921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101304982960346938961637947 151957474440520408442456921)
      ·
        refine ⟨113968105830390306331842691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151957474440520408442456921 113968105830390306331842691)
        ·
          refine ⟨170952158745585459497764037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113968105830390306331842691 170952158745585459497764037)
          ·
            refine ⟨32053529764797273655830757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170952158745585459497764037 32053529764797273655830757)
            ·
              refine ⟨6010036830899488810468267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32053529764797273655830757 6010036830899488810468267)
              ·
                refine ⟨9015055246349233215702401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6010036830899488810468267 9015055246349233215702401)
                ·
                  refine ⟨6761291434761924911776801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9015055246349233215702401 6761291434761924911776801)
                  ·
                    refine ⟨5070968576071443683832601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6761291434761924911776801 5070968576071443683832601)
                    ·
                      refine ⟨3803226432053582762874451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070968576071443683832601 3803226432053582762874451)
                      ·
                        rfl

theorem cell23_7406757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_7406757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406757 prefixEnd_7406757 := by exact prefixLift 7406757
  have htrace : WordTrace (prefixWord ++ tailWord_7406757) baseStart_7406757 baseEnd_7406757 := by
    simpa [prefixWord, tailWord_7406757, baseEnd_7406757] using wordTrace_append hprefix tailTrace_7406757
  have hstable : (prefixWord ++ tailWord_7406757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406757).length < 2 ^ (prefixWord ++ tailWord_7406757).sum := by decide
  have hdescent : baseEnd_7406757 < baseStart_7406757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406774 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7406774 : Nat := 118140960795 + 7406774 * 2 ^ 59
def prefixEnd_7406774 : Nat := 4983230072969 + 3 ^ 40 * 7406774 * 2
def baseEnd_7406774 : Nat := 3803235161224709196361873

theorem tailTrace_7406774 : CollatzResearch.WordTrace tailWord_7406774 prefixEnd_7406774 3803235161224709196361873 := by
  unfold tailWord_7406774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16884202579283140570900211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180098160845686832756268917 16884202579283140570900211)
  ·
    refine ⟨25326303868924710856350317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16884202579283140570900211 25326303868924710856350317)
    ·
      refine ⟨9497363950846766571131369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25326303868924710856350317 9497363950846766571131369)
      ·
        refine ⟨7123022963135074928348527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9497363950846766571131369 7123022963135074928348527)
        ·
          refine ⟨10684534444702612392522791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123022963135074928348527 10684534444702612392522791)
          ·
            refine ⟨16026801667053918588784187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10684534444702612392522791 16026801667053918588784187)
            ·
              refine ⟨24040202500580877883176281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16026801667053918588784187 24040202500580877883176281)
              ·
                refine ⟨18030151875435658412382211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24040202500580877883176281 18030151875435658412382211)
                ·
                  refine ⟨27045227813153487618573317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18030151875435658412382211 27045227813153487618573317)
                  ·
                    refine ⟨5070980214966278928482497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27045227813153487618573317 5070980214966278928482497)
                    ·
                      refine ⟨3803235161224709196361873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5070980214966278928482497 3803235161224709196361873)
                      ·
                        rfl

theorem cell23_7406774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7406774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406774 prefixEnd_7406774 := by exact prefixLift 7406774
  have htrace : WordTrace (prefixWord ++ tailWord_7406774) baseStart_7406774 baseEnd_7406774 := by
    simpa [prefixWord, tailWord_7406774, baseEnd_7406774] using wordTrace_append hprefix tailTrace_7406774
  have hstable : (prefixWord ++ tailWord_7406774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406774).length < 2 ^ (prefixWord ++ tailWord_7406774).sum := by decide
  have hdescent : baseEnd_7406774 < baseStart_7406774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406876 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7406876 : Nat := 118140960795 + 7406876 * 2 ^ 59
def prefixEnd_7406876 : Nat := 4983230072969 + 3 ^ 40 * 7406876 * 2
def baseEnd_7406876 : Nat := 3803287536251467797286403

theorem tailTrace_7406876 : CollatzResearch.WordTrace tailWord_7406876 prefixEnd_7406876 3803287536251467797286403 := by
  unfold tailWord_7406876
  simp only [CollatzResearch.WordTrace]
  refine ⟨135075480757080360277308241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180100641009440480369744321 135075480757080360277308241)
  ·
    refine ⟨101306610567810270207981181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135075480757080360277308241 101306610567810270207981181)
    ·
      refine ⟨37989978962928851327992943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101306610567810270207981181 37989978962928851327992943)
      ·
        refine ⟨56984968444393276991989415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37989978962928851327992943 56984968444393276991989415)
        ·
          refine ⟨85477452666589915487984123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56984968444393276991989415 85477452666589915487984123)
          ·
            refine ⟨128216178999884873231976185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85477452666589915487984123 128216178999884873231976185)
            ·
              refine ⟨96162134249913654923982139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128216178999884873231976185 96162134249913654923982139)
              ·
                refine ⟨144243201374870482385973209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96162134249913654923982139 144243201374870482385973209)
                ·
                  refine ⟨108182401031152861789479907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144243201374870482385973209 108182401031152861789479907)
                  ·
                    refine ⟨162273601546729292684219861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108182401031152861789479907 162273601546729292684219861)
                    ·
                      refine ⟨3803287536251467797286403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162273601546729292684219861 3803287536251467797286403)
                      ·
                        rfl

theorem cell23_7406876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7406876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406876 prefixEnd_7406876 := by exact prefixLift 7406876
  have htrace : WordTrace (prefixWord ++ tailWord_7406876) baseStart_7406876 baseEnd_7406876 := by
    simpa [prefixWord, tailWord_7406876, baseEnd_7406876] using wordTrace_append hprefix tailTrace_7406876
  have hstable : (prefixWord ++ tailWord_7406876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406876).length < 2 ^ (prefixWord ++ tailWord_7406876).sum := by decide
  have hdescent : baseEnd_7406876 < baseStart_7406876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406883 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 1, 5]
def baseStart_7406883 : Nat := 118140960795 + 7406883 * 2 ^ 59
def prefixEnd_7406883 : Nat := 4983230072969 + 3 ^ 40 * 7406883 * 2
def baseEnd_7406883 : Nat := 1267763710205349756632957

theorem tailTrace_7406883 : CollatzResearch.WordTrace tailWord_7406883 prefixEnd_7406883 1267763710205349756632957 := by
  unfold tailWord_7406883
  simp only [CollatzResearch.WordTrace]
  refine ⟨270151216825135360750121303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180100811216756907166747535 270151216825135360750121303)
  ·
    refine ⟨405226825237703041125181955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270151216825135360750121303 405226825237703041125181955)
    ·
      refine ⟨607840237856554561687772933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405226825237703041125181955 607840237856554561687772933)
      ·
        refine ⟨113970044598103980316457425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 607840237856554561687772933 113970044598103980316457425)
        ·
          refine ⟨85477533448577985237343069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113970044598103980316457425 85477533448577985237343069)
          ·
            refine ⟨32054075043216744464003651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85477533448577985237343069 32054075043216744464003651)
            ·
              refine ⟨48081112564825116696005477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32054075043216744464003651 48081112564825116696005477)
              ·
                refine ⟨9015208605904709380501027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48081112564825116696005477 9015208605904709380501027)
                ·
                  refine ⟨13522812908857064070751541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9015208605904709380501027 13522812908857064070751541)
                  ·
                    refine ⟨1267763710205349756632957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13522812908857064070751541 1267763710205349756632957)
                    ·
                      rfl

theorem cell23_7406883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 5].length) (baseStart_7406883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406883 prefixEnd_7406883 := by exact prefixLift 7406883
  have htrace : WordTrace (prefixWord ++ tailWord_7406883) baseStart_7406883 baseEnd_7406883 := by
    simpa [prefixWord, tailWord_7406883, baseEnd_7406883] using wordTrace_append hprefix tailTrace_7406883
  have hstable : (prefixWord ++ tailWord_7406883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406883).length < 2 ^ (prefixWord ++ tailWord_7406883).sum := by decide
  have hdescent : baseEnd_7406883 < baseStart_7406883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406896 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 3, 6]
def baseStart_7406896 : Nat := 118140960795 + 7406896 * 2 ^ 59
def prefixEnd_7406896 : Nat := 4983230072969 + 3 ^ 40 * 7406896 * 2
def baseEnd_7406896 : Nat := 1267765935288185906345437

theorem tailTrace_7406896 : CollatzResearch.WordTrace tailWord_7406896 prefixEnd_7406896 1267765935288185906345437 := by
  unfold tailWord_7406896
  simp only [CollatzResearch.WordTrace]
  refine ⟨135075845487044131985172271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180101127316058842646896361 135075845487044131985172271)
  ·
    refine ⟨202613768230566197977758407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135075845487044131985172271 202613768230566197977758407)
    ·
      refine ⟨303920652345849296966637611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202613768230566197977758407 303920652345849296966637611)
      ·
        refine ⟨455880978518773945449956417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303920652345849296966637611 455880978518773945449956417)
        ·
          refine ⟨341910733889080459087467313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455880978518773945449956417 341910733889080459087467313)
          ·
            refine ⟨256433050416810344315600485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341910733889080459087467313 256433050416810344315600485)
            ·
              refine ⟨48081196953151939559175091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256433050416810344315600485 48081196953151939559175091)
              ·
                refine ⟨72121795429727909338762637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48081196953151939559175091 72121795429727909338762637)
                ·
                  refine ⟨27045673286147966002035989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72121795429727909338762637 27045673286147966002035989)
                  ·
                    refine ⟨1267765935288185906345437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27045673286147966002035989 1267765935288185906345437)
                    ·
                      rfl

theorem cell23_7406896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_7406896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406896 prefixEnd_7406896 := by exact prefixLift 7406896
  have htrace : WordTrace (prefixWord ++ tailWord_7406896) baseStart_7406896 baseEnd_7406896 := by
    simpa [prefixWord, tailWord_7406896, baseEnd_7406896] using wordTrace_append hprefix tailTrace_7406896
  have hstable : (prefixWord ++ tailWord_7406896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406896).length < 2 ^ (prefixWord ++ tailWord_7406896).sum := by decide
  have hdescent : baseEnd_7406896 < baseStart_7406896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406900 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_7406900 : Nat := 118140960795 + 7406900 * 2 ^ 59
def prefixEnd_7406900 : Nat := 4983230072969 + 3 ^ 40 * 7406900 * 2
def baseEnd_7406900 : Nat := 1267766619929058567795431

theorem tailTrace_7406900 : CollatzResearch.WordTrace tailWord_7406900 prefixEnd_7406900 1267766619929058567795431 := by
  unfold tailWord_7406900
  simp only [CollatzResearch.WordTrace]
  refine ⟨135075918433036886326745077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180101224577382515102326769 135075918433036886326745077)
  ·
    refine ⟨12663367353097208093132351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135075918433036886326745077 12663367353097208093132351)
    ·
      refine ⟨18995051029645812139698527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12663367353097208093132351 18995051029645812139698527)
      ·
        refine ⟨28492576544468718209547791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18995051029645812139698527 28492576544468718209547791)
        ·
          refine ⟨42738864816703077314321687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28492576544468718209547791 42738864816703077314321687)
          ·
            refine ⟨64108297225054615971482531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42738864816703077314321687 64108297225054615971482531)
            ·
              refine ⟨96162445837581923957223797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64108297225054615971482531 96162445837581923957223797)
              ·
                refine ⟨9015229297273305370989731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96162445837581923957223797 9015229297273305370989731)
                ·
                  refine ⟨13522843945909958056484597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9015229297273305370989731 13522843945909958056484597)
                  ·
                    refine ⟨1267766619929058567795431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13522843945909958056484597 1267766619929058567795431)
                    ·
                      rfl

theorem cell23_7406900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_7406900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406900 prefixEnd_7406900 := by exact prefixLift 7406900
  have htrace : WordTrace (prefixWord ++ tailWord_7406900) baseStart_7406900 baseEnd_7406900 := by
    simpa [prefixWord, tailWord_7406900, baseEnd_7406900] using wordTrace_append hprefix tailTrace_7406900
  have hstable : (prefixWord ++ tailWord_7406900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406900).length < 2 ^ (prefixWord ++ tailWord_7406900).sum := by decide
  have hdescent : baseEnd_7406900 < baseStart_7406900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406933 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7406933 : Nat := 118140960795 + 7406933 * 2 ^ 59
def prefixEnd_7406933 : Nat := 4983230072969 + 3 ^ 40 * 7406933 * 2
def baseEnd_7406933 : Nat := 3803316804648774074273641

theorem tailTrace_7406933 : CollatzResearch.WordTrace tailWord_7406933 prefixEnd_7406933 3803316804648774074273641 := by
  unfold tailWord_7406933
  simp only [CollatzResearch.WordTrace]
  refine ⟨270153040474954219289441453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180102026983302812859627635 270153040474954219289441453)
  ·
    refine ⟨101307390178107832233540545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270153040474954219289441453 101307390178107832233540545)
    ·
      refine ⟨75980542633580874175155409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101307390178107832233540545 75980542633580874175155409)
      ·
        refine ⟨56985406975185655631366557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75980542633580874175155409 56985406975185655631366557)
        ·
          refine ⟨21369527615694620861762459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56985406975185655631366557 21369527615694620861762459)
          ·
            refine ⟨32054291423541931292643689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21369527615694620861762459 32054291423541931292643689)
            ·
              refine ⟨24040718567656448469482767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32054291423541931292643689 24040718567656448469482767)
              ·
                refine ⟨36061077851484672704224151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24040718567656448469482767 36061077851484672704224151)
                ·
                  refine ⟨54091616777227009056336227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36061077851484672704224151 54091616777227009056336227)
                  ·
                    refine ⟨81137425165840513584504341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54091616777227009056336227 81137425165840513584504341)
                    ·
                      refine ⟨3803316804648774074273641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81137425165840513584504341 3803316804648774074273641)
                      ·
                        rfl

theorem cell23_7406933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7406933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406933 prefixEnd_7406933 := by exact prefixLift 7406933
  have htrace : WordTrace (prefixWord ++ tailWord_7406933) baseStart_7406933 baseEnd_7406933 := by
    simpa [prefixWord, tailWord_7406933, baseEnd_7406933] using wordTrace_append hprefix tailTrace_7406933
  have hstable : (prefixWord ++ tailWord_7406933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406933).length < 2 ^ (prefixWord ++ tailWord_7406933).sum := by decide
  have hdescent : baseEnd_7406933 < baseStart_7406933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406954 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7406954 : Nat := 118140960795 + 7406954 * 2 ^ 59
def prefixEnd_7406954 : Nat := 4983230072969 + 3 ^ 40 * 7406954 * 2
def baseEnd_7406954 : Nat := 3803327587742518492111045

theorem tailTrace_7406954 : CollatzResearch.WordTrace tailWord_7406954 prefixEnd_7406954 3803327587742518492111045 := by
  unfold tailWord_7406954
  simp only [CollatzResearch.WordTrace]
  refine ⟨67538451601969534968988979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180102537605252093250637277 67538451601969534968988979)
  ·
    refine ⟨101307677402954302453483469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67538451601969534968988979 101307677402954302453483469)
    ·
      refine ⟨37990379026107863420056301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101307677402954302453483469 37990379026107863420056301)
      ·
        refine ⟨14246392134790448782521113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37990379026107863420056301 14246392134790448782521113)
        ·
          refine ⟨10684794101092836586890835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14246392134790448782521113 10684794101092836586890835)
          ·
            refine ⟨16027191151639254880336253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10684794101092836586890835 16027191151639254880336253)
            ·
              refine ⟨6010196681864720580126095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16027191151639254880336253 6010196681864720580126095)
              ·
                refine ⟨9015295022797080870189143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6010196681864720580126095 9015295022797080870189143)
                ·
                  refine ⟨13522942534195621305283715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9015295022797080870189143 13522942534195621305283715)
                  ·
                    refine ⟨20284413801293431957925573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13522942534195621305283715 20284413801293431957925573)
                    ·
                      refine ⟨3803327587742518492111045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20284413801293431957925573 3803327587742518492111045)
                      ·
                        rfl

theorem cell23_7406954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7406954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406954 prefixEnd_7406954 := by exact prefixLift 7406954
  have htrace : WordTrace (prefixWord ++ tailWord_7406954) baseStart_7406954 baseEnd_7406954 := by
    simpa [prefixWord, tailWord_7406954, baseEnd_7406954] using wordTrace_append hprefix tailTrace_7406954
  have hstable : (prefixWord ++ tailWord_7406954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406954).length < 2 ^ (prefixWord ++ tailWord_7406954).sum := by decide
  have hdescent : baseEnd_7406954 < baseStart_7406954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7406977 : List Nat := [1, 2, 4, 3, 3, 1, 1, 8]
def baseStart_7406977 : Nat := 118140960795 + 7406977 * 2 ^ 59
def prefixEnd_7406977 : Nat := 4983230072969 + 3 ^ 40 * 7406977 * 2
def baseEnd_7406977 : Nat := 140864422140650811189757

theorem tailTrace_7406977 : CollatzResearch.WordTrace tailWord_7406977 prefixEnd_7406977 140864422140650811189757 := by
  unfold tailWord_7406977
  simp only [CollatzResearch.WordTrace]
  refine ⟨270154645286794814804043185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180103096857863209869362123 270154645286794814804043185)
  ·
    refine ⟨202615983965096111103032389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270154645286794814804043185 202615983965096111103032389)
    ·
      refine ⟨37990496993455520831818573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202615983965096111103032389 37990496993455520831818573)
      ·
        refine ⟨14246436372545820311931965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37990496993455520831818573 14246436372545820311931965)
        ·
          refine ⟨5342413639704682616974487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14246436372545820311931965 5342413639704682616974487)
          ·
            refine ⟨8013620459557023925461731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342413639704682616974487 8013620459557023925461731)
            ·
              refine ⟨12020430689335535888192597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8013620459557023925461731 12020430689335535888192597)
              ·
                refine ⟨140864422140650811189757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12020430689335535888192597 140864422140650811189757)
                ·
                  rfl

theorem cell23_7406977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 8].length) (baseStart_7406977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7406977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7406977 prefixEnd_7406977 := by exact prefixLift 7406977
  have htrace : WordTrace (prefixWord ++ tailWord_7406977) baseStart_7406977 baseEnd_7406977 := by
    simpa [prefixWord, tailWord_7406977, baseEnd_7406977] using wordTrace_append hprefix tailTrace_7406977
  have hstable : (prefixWord ++ tailWord_7406977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7406977).length < 2 ^ (prefixWord ++ tailWord_7406977).sum := by decide
  have hdescent : baseEnd_7406977 < baseStart_7406977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7406977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407013 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_7407013 : Nat := 118140960795 + 7407013 * 2 ^ 59
def prefixEnd_7407013 : Nat := 4983230072969 + 3 ^ 40 * 7407013 * 2
def baseEnd_7407013 : Nat := 3803357883101133761273273

theorem tailTrace_7407013 : CollatzResearch.WordTrace tailWord_7407013 prefixEnd_7407013 3803357883101133761273273 := by
  unfold tailWord_7407013
  simp only [CollatzResearch.WordTrace]
  refine ⟨270155958314664392952353693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180103972209776261968235795 270155958314664392952353693)
  ·
    refine ⟨101308484367999147357132635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270155958314664392952353693 101308484367999147357132635)
    ·
      refine ⟨151962726551998721035698953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101308484367999147357132635 151962726551998721035698953)
      ·
        refine ⟨113972044913999040776774215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151962726551998721035698953 113972044913999040776774215)
        ·
          refine ⟨170958067370998561165161323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113972044913999040776774215 170958067370998561165161323)
          ·
            refine ⟨256437101056497841747741985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170958067370998561165161323 256437101056497841747741985)
            ·
              refine ⟨192327825792373381310806489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256437101056497841747741985 192327825792373381310806489)
              ·
                refine ⟨144245869344280035983104867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192327825792373381310806489 144245869344280035983104867)
                ·
                  refine ⟨216368804016420053974657301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144245869344280035983104867 216368804016420053974657301)
                  ·
                    refine ⟨10142287688269690030062061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 216368804016420053974657301 10142287688269690030062061)
                    ·
                      refine ⟨3803357883101133761273273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10142287688269690030062061 3803357883101133761273273)
                      ·
                        rfl

theorem cell23_7407013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_7407013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407013 prefixEnd_7407013 := by exact prefixLift 7407013
  have htrace : WordTrace (prefixWord ++ tailWord_7407013) baseStart_7407013 baseEnd_7407013 := by
    simpa [prefixWord, tailWord_7407013, baseEnd_7407013] using wordTrace_append hprefix tailTrace_7407013
  have hstable : (prefixWord ++ tailWord_7407013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407013).length < 2 ^ (prefixWord ++ tailWord_7407013).sum := by decide
  have hdescent : baseEnd_7407013 < baseStart_7407013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407021 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7407021 : Nat := 118140960795 + 7407021 * 2 ^ 59
def prefixEnd_7407021 : Nat := 4983230072969 + 3 ^ 40 * 7407021 * 2
def baseEnd_7407021 : Nat := 3803361990946369729973237

theorem tailTrace_7407021 : CollatzResearch.WordTrace tailWord_7407021 prefixEnd_7407021 3803361990946369729973237 := by
  unfold tailWord_7407021
  simp only [CollatzResearch.WordTrace]
  refine ⟨270156250098635410318644917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180104166732423606879096611 270156250098635410318644917)
  ·
    refine ⟨25327148446747069717372961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270156250098635410318644917 25327148446747069717372961)
    ·
      refine ⟨18995361335060302288029721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25327148446747069717372961 18995361335060302288029721)
      ·
        refine ⟨14246521001295226716022291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18995361335060302288029721 14246521001295226716022291)
        ·
          refine ⟨21369781501942840074033437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14246521001295226716022291 21369781501942840074033437)
          ·
            refine ⟨8013668063228565027762539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21369781501942840074033437 8013668063228565027762539)
            ·
              refine ⟨12020502094842847541643809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8013668063228565027762539 12020502094842847541643809)
              ·
                refine ⟨9015376571132135656232857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12020502094842847541643809 9015376571132135656232857)
                ·
                  refine ⟨6761532428349101742174643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9015376571132135656232857 6761532428349101742174643)
                  ·
                    refine ⟨10142298642523652613261965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6761532428349101742174643 10142298642523652613261965)
                    ·
                      refine ⟨3803361990946369729973237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10142298642523652613261965 3803361990946369729973237)
                      ·
                        rfl

theorem cell23_7407021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7407021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407021 prefixEnd_7407021 := by exact prefixLift 7407021
  have htrace : WordTrace (prefixWord ++ tailWord_7407021) baseStart_7407021 baseEnd_7407021 := by
    simpa [prefixWord, tailWord_7407021, baseEnd_7407021] using wordTrace_append hprefix tailTrace_7407021
  have hstable : (prefixWord ++ tailWord_7407021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407021).length < 2 ^ (prefixWord ++ tailWord_7407021).sum := by decide
  have hdescent : baseEnd_7407021 < baseStart_7407021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407044 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_7407044 : Nat := 118140960795 + 7407044 * 2 ^ 59
def prefixEnd_7407044 : Nat := 4983230072969 + 3 ^ 40 * 7407044 * 2
def baseEnd_7407044 : Nat := 3803373801001423139985631

theorem tailTrace_7407044 : CollatzResearch.WordTrace tailWord_7407044 prefixEnd_7407044 3803373801001423139985631 := by
  unfold tailWord_7407044
  simp only [CollatzResearch.WordTrace]
  refine ⟨135078544488776042623366093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180104725985034723497821457 135078544488776042623366093)
  ·
    refine ⟨50654454183291015983762285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135078544488776042623366093 50654454183291015983762285)
    ·
      refine ⟨18995420318734130993910857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50654454183291015983762285 18995420318734130993910857)
      ·
        refine ⟨14246565239050598245433143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18995420318734130993910857 14246565239050598245433143)
        ·
          refine ⟨21369847858575897368149715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14246565239050598245433143 21369847858575897368149715)
          ·
            refine ⟨32054771787863846052224573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21369847858575897368149715 32054771787863846052224573)
            ·
              refine ⟨12020539420448942269584215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32054771787863846052224573 12020539420448942269584215)
              ·
                refine ⟨18030809130673413404376323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12020539420448942269584215 18030809130673413404376323)
                ·
                  refine ⟨27046213696010120106564485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18030809130673413404376323 27046213696010120106564485)
                  ·
                    refine ⟨5071165068001897519980841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27046213696010120106564485 5071165068001897519980841)
                    ·
                      refine ⟨3803373801001423139985631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071165068001897519980841 3803373801001423139985631)
                      ·
                        rfl

theorem cell23_7407044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_7407044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407044 prefixEnd_7407044 := by exact prefixLift 7407044
  have htrace : WordTrace (prefixWord ++ tailWord_7407044) baseStart_7407044 baseEnd_7407044 := by
    simpa [prefixWord, tailWord_7407044, baseEnd_7407044] using wordTrace_append hprefix tailTrace_7407044
  have hstable : (prefixWord ++ tailWord_7407044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407044).length < 2 ^ (prefixWord ++ tailWord_7407044).sum := by decide
  have hdescent : baseEnd_7407044 < baseStart_7407044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407063 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 6, 5]
def baseStart_7407063 : Nat := 118140960795 + 7407063 * 2 ^ 59
def prefixEnd_7407063 : Nat := 4983230072969 + 3 ^ 40 * 7407063 * 2
def baseEnd_7407063 : Nat := 1267794519044619521882681

theorem tailTrace_7407063 : CollatzResearch.WordTrace tailWord_7407063 prefixEnd_7407063 1267794519044619521882681 := by
  unfold tailWord_7407063
  simp only [CollatzResearch.WordTrace]
  refine ⟨270157781964483251491673843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180105187976322167661115895 270157781964483251491673843)
  ·
    refine ⟨405236672946724877237510765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270157781964483251491673843 405236672946724877237510765)
    ·
      refine ⟨151963752355021828964066537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405236672946724877237510765 151963752355021828964066537)
      ·
        refine ⟨113972814266266371723049903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151963752355021828964066537 113972814266266371723049903)
        ·
          refine ⟨170959221399399557584574855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113972814266266371723049903 170959221399399557584574855)
          ·
            refine ⟨256438832099099336376862283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170959221399399557584574855 256438832099099336376862283)
            ·
              refine ⟨384658248148649004565293425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256438832099099336376862283 384658248148649004565293425)
              ·
                refine ⟨288493686111486753423970069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384658248148649004565293425 288493686111486753423970069)
                ·
                  refine ⟨13523141536475941566748597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 288493686111486753423970069 13523141536475941566748597)
                  ·
                    refine ⟨1267794519044619521882681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13523141536475941566748597 1267794519044619521882681)
                    ·
                      rfl

theorem cell23_7407063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_7407063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407063 prefixEnd_7407063 := by exact prefixLift 7407063
  have htrace : WordTrace (prefixWord ++ tailWord_7407063) baseStart_7407063 baseEnd_7407063 := by
    simpa [prefixWord, tailWord_7407063, baseEnd_7407063] using wordTrace_append hprefix tailTrace_7407063
  have hstable : (prefixWord ++ tailWord_7407063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407063).length < 2 ^ (prefixWord ++ tailWord_7407063).sum := by decide
  have hdescent : baseEnd_7407063 < baseStart_7407063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407080 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 2, 5]
def baseStart_7407080 : Nat := 118140960795 + 7407080 * 2 ^ 59
def prefixEnd_7407080 : Nat := 4983230072969 + 3 ^ 40 * 7407080 * 2
def baseEnd_7407080 : Nat := 1267797428768328333045155

theorem tailTrace_7407080 : CollatzResearch.WordTrace tailWord_7407080 prefixEnd_7407080 1267797428768328333045155 := by
  unfold tailWord_7407080
  simp only [CollatzResearch.WordTrace]
  refine ⟨135079201002710831697521347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180105601336947775596695129 135079201002710831697521347)
  ·
    refine ⟨202618801504066247546282021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135079201002710831697521347 202618801504066247546282021)
    ·
      refine ⟨37991025282012421414927879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202618801504066247546282021 37991025282012421414927879)
      ·
        refine ⟨56986537923018632122391819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37991025282012421414927879 56986537923018632122391819)
        ·
          refine ⟨85479806884527948183587729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56986537923018632122391819 85479806884527948183587729)
          ·
            refine ⟨64109855163395961137690797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85479806884527948183587729 64109855163395961137690797)
            ·
              refine ⟨24041195686273485426634049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64109855163395961137690797 24041195686273485426634049)
              ·
                refine ⟨18030896764705114069975537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24041195686273485426634049 18030896764705114069975537)
                ·
                  refine ⟨13523172573528835552481653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18030896764705114069975537 13523172573528835552481653)
                  ·
                    refine ⟨1267797428768328333045155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13523172573528835552481653 1267797428768328333045155)
                    ·
                      rfl

theorem cell23_7407080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_7407080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407080 prefixEnd_7407080 := by exact prefixLift 7407080
  have htrace : WordTrace (prefixWord ++ tailWord_7407080) baseStart_7407080 baseEnd_7407080 := by
    simpa [prefixWord, tailWord_7407080, baseEnd_7407080] using wordTrace_append hprefix tailTrace_7407080
  have hstable : (prefixWord ++ tailWord_7407080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407080).length < 2 ^ (prefixWord ++ tailWord_7407080).sum := by decide
  have hdescent : baseEnd_7407080 < baseStart_7407080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407083 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 4]
def baseStart_7407083 : Nat := 118140960795 + 7407083 * 2 ^ 59
def prefixEnd_7407083 : Nat := 4983230072969 + 3 ^ 40 * 7407083 * 2
def baseEnd_7407083 : Nat := 3803393826746948487397951

theorem tailTrace_7407083 : CollatzResearch.WordTrace tailWord_7407083 prefixEnd_7407083 3803393826746948487397951 := by
  unfold tailWord_7407083
  simp only [CollatzResearch.WordTrace]
  refine ⟨270158511424410794907401903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180105674282940529938267935 270158511424410794907401903)
  ·
    refine ⟨405237767136616192361102855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270158511424410794907401903 405237767136616192361102855)
    ·
      refine ⟨607856650704924288541654283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405237767136616192361102855 607856650704924288541654283)
      ·
        refine ⟨911784976057386432812481425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607856650704924288541654283 911784976057386432812481425)
        ·
          refine ⟨683838732043039824609361069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911784976057386432812481425 683838732043039824609361069)
          ·
            refine ⟨256439524516139934228510401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683838732043039824609361069 256439524516139934228510401)
            ·
              refine ⟨192329643387104950671382801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256439524516139934228510401 192329643387104950671382801)
              ·
                refine ⟨144247232540328713003537101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192329643387104950671382801 144247232540328713003537101)
                ·
                  refine ⟨54092712202623267376326413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144247232540328713003537101 54092712202623267376326413)
                  ·
                    refine ⟨20284767075983725266122405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54092712202623267376326413 20284767075983725266122405)
                    ·
                      refine ⟨3803393826746948487397951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20284767075983725266122405 3803393826746948487397951)
                      ·
                        rfl

theorem cell23_7407083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 4].length) (baseStart_7407083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407083 prefixEnd_7407083 := by exact prefixLift 7407083
  have htrace : WordTrace (prefixWord ++ tailWord_7407083) baseStart_7407083 baseEnd_7407083 := by
    simpa [prefixWord, tailWord_7407083, baseEnd_7407083] using wordTrace_append hprefix tailTrace_7407083
  have hstable : (prefixWord ++ tailWord_7407083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407083).length < 2 ^ (prefixWord ++ tailWord_7407083).sum := by decide
  have hdescent : baseEnd_7407083 < baseStart_7407083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407090 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7407090 : Nat := 118140960795 + 7407090 * 2 ^ 59
def prefixEnd_7407090 : Nat := 4983230072969 + 3 ^ 40 * 7407090 * 2
def baseEnd_7407090 : Nat := 3803397421111529960010419

theorem tailTrace_7407090 : CollatzResearch.WordTrace tailWord_7407090 prefixEnd_7407090 3803397421111529960010419 := by
  unfold tailWord_7407090
  simp only [CollatzResearch.WordTrace]
  refine ⟨67539691683846358775726681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180105844490256956735271149 67539691683846358775726681)
  ·
    refine ⟨50654768762884769081795011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67539691683846358775726681 50654768762884769081795011)
    ·
      refine ⟨75982153144327153622692517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50654768762884769081795011 75982153144327153622692517)
      ·
        refine ⟨14246653714561341304254847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75982153144327153622692517 14246653714561341304254847)
        ·
          refine ⟨21369980571842011956382271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14246653714561341304254847 21369980571842011956382271)
          ·
            refine ⟨32054970857763017934573407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21369980571842011956382271 32054970857763017934573407)
            ·
              refine ⟨48082456286644526901860111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32054970857763017934573407 48082456286644526901860111)
              ·
                refine ⟨72123684429966790352790167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48082456286644526901860111 72123684429966790352790167)
                ·
                  refine ⟨108185526644950185529185251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72123684429966790352790167 108185526644950185529185251)
                  ·
                    refine ⟨162278289967425278293777877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108185526644950185529185251 162278289967425278293777877)
                    ·
                      refine ⟨3803397421111529960010419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162278289967425278293777877 3803397421111529960010419)
                      ·
                        rfl

theorem cell23_7407090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7407090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407090 prefixEnd_7407090 := by exact prefixLift 7407090
  have htrace : WordTrace (prefixWord ++ tailWord_7407090) baseStart_7407090 baseEnd_7407090 := by
    simpa [prefixWord, tailWord_7407090, baseEnd_7407090] using wordTrace_append hprefix tailTrace_7407090
  have hstable : (prefixWord ++ tailWord_7407090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407090).length < 2 ^ (prefixWord ++ tailWord_7407090).sum := by decide
  have hdescent : baseEnd_7407090 < baseStart_7407090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407137 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_7407137 : Nat := 118140960795 + 7407137 * 2 ^ 59
def prefixEnd_7407137 : Nat := 4983230072969 + 3 ^ 40 * 7407137 * 2
def baseEnd_7407137 : Nat := 3803421554702291276122703

theorem tailTrace_7407137 : CollatzResearch.WordTrace tailWord_7407137 prefixEnd_7407137 3803421554702291276122703 := by
  unfold tailWord_7407137
  simp only [CollatzResearch.WordTrace]
  refine ⟨270160480966215162129867665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180106987310810108086578443 270160480966215162129867665)
  ·
    refine ⟨202620360724661371597400749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270160480966215162129867665 202620360724661371597400749)
    ·
      refine ⟨75982635271748014349025281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202620360724661371597400749 75982635271748014349025281)
      ·
        refine ⟨56986976453811010761768961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75982635271748014349025281 56986976453811010761768961)
        ·
          refine ⟨42740232340358258071326721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56986976453811010761768961 42740232340358258071326721)
          ·
            refine ⟨32055174255268693553495041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42740232340358258071326721 32055174255268693553495041)
            ·
              refine ⟨24041380691451520165121281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32055174255268693553495041 24041380691451520165121281)
              ·
                refine ⟨18031035518588640123840961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24041380691451520165121281 18031035518588640123840961)
                ·
                  refine ⟨13523276638941480092880721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18031035518588640123840961 13523276638941480092880721)
                  ·
                    refine ⟨10142457479206110069660541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13523276638941480092880721 10142457479206110069660541)
                    ·
                      refine ⟨3803421554702291276122703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10142457479206110069660541 3803421554702291276122703)
                      ·
                        rfl

theorem cell23_7407137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_7407137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407137 prefixEnd_7407137 := by exact prefixLift 7407137
  have htrace : WordTrace (prefixWord ++ tailWord_7407137) baseStart_7407137 baseEnd_7407137 := by
    simpa [prefixWord, tailWord_7407137, baseEnd_7407137] using wordTrace_append hprefix tailTrace_7407137
  have hstable : (prefixWord ++ tailWord_7407137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407137).length < 2 ^ (prefixWord ++ tailWord_7407137).sum := by decide
  have hdescent : baseEnd_7407137 < baseStart_7407137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407167 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 3]
def baseStart_7407167 : Nat := 118140960795 + 7407167 * 2 ^ 59
def prefixEnd_7407167 : Nat := 4983230072969 + 3 ^ 40 * 7407167 * 2
def baseEnd_7407167 : Nat := 3803436959121926158747565

theorem tailTrace_7407167 : CollatzResearch.WordTrace tailWord_7407167 prefixEnd_7407167 3803436959121926158747565 := by
  unfold tailWord_7407167
  simp only [CollatzResearch.WordTrace]
  refine ⟨270161575156106477253459755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180107716770737651502306503 270161575156106477253459755)
  ·
    refine ⟨405242362734159715880189633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270161575156106477253459755 405242362734159715880189633)
    ·
      refine ⟨303931772050619786910142225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405242362734159715880189633 303931772050619786910142225)
      ·
        refine ⟨227948829037964840182606669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303931772050619786910142225 227948829037964840182606669)
        ·
          refine ⟨85480810889236815068477501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227948829037964840182606669 85480810889236815068477501)
          ·
            refine ⟨32055304083463805650679063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85480810889236815068477501 32055304083463805650679063)
            ·
              refine ⟨48082956125195708476018595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32055304083463805650679063 48082956125195708476018595)
              ·
                refine ⟨72124434187793562714027893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48082956125195708476018595 72124434187793562714027893)
                ·
                  refine ⟨6761665705105646504440115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72124434187793562714027893 6761665705105646504440115)
                  ·
                    refine ⟨10142498557658469756660173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6761665705105646504440115 10142498557658469756660173)
                    ·
                      refine ⟨3803436959121926158747565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10142498557658469756660173 3803436959121926158747565)
                      ·
                        rfl

theorem cell23_7407167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_7407167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407167 prefixEnd_7407167 := by exact prefixLift 7407167
  have htrace : WordTrace (prefixWord ++ tailWord_7407167) baseStart_7407167 baseEnd_7407167 := by
    simpa [prefixWord, tailWord_7407167, baseEnd_7407167] using wordTrace_append hprefix tailTrace_7407167
  have hstable : (prefixWord ++ tailWord_7407167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407167).length < 2 ^ (prefixWord ++ tailWord_7407167).sum := by decide
  have hdescent : baseEnd_7407167 < baseStart_7407167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407217 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 2, 4]
def baseStart_7407217 : Nat := 118140960795 + 7407217 * 2 ^ 59
def prefixEnd_7407217 : Nat := 4983230072969 + 3 ^ 40 * 7407217 * 2
def baseEnd_7407217 : Nat := 1267820877718216987707445

theorem tailTrace_7407217 : CollatzResearch.WordTrace tailWord_7407217 prefixEnd_7407217 1267820877718216987707445 := by
  unfold tailWord_7407217
  simp only [CollatzResearch.WordTrace]
  refine ⟨270163398805925335792779905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180108932537283557195186603 270163398805925335792779905)
  ·
    refine ⟨202622549104444001844584929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270163398805925335792779905 202622549104444001844584929)
    ·
      refine ⟨151966911828333001383438697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202622549104444001844584929 151966911828333001383438697)
      ·
        refine ⟨113975183871249751037579023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151966911828333001383438697 113975183871249751037579023)
        ·
          refine ⟨170962775806874626556368535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113975183871249751037579023 170962775806874626556368535)
          ·
            refine ⟨256444163710311939834552803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170962775806874626556368535 256444163710311939834552803)
            ·
              refine ⟨384666245565467909751829205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256444163710311939834552803 384666245565467909751829205)
              ·
                refine ⟨9015615130440654134808497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 384666245565467909751829205 9015615130440654134808497)
                ·
                  refine ⟨6761711347830490601106373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9015615130440654134808497 6761711347830490601106373)
                  ·
                    refine ⟨1267820877718216987707445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761711347830490601106373 1267820877718216987707445)
                    ·
                      rfl

theorem cell23_7407217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_7407217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407217 prefixEnd_7407217 := by exact prefixLift 7407217
  have htrace : WordTrace (prefixWord ++ tailWord_7407217) baseStart_7407217 baseEnd_7407217 := by
    simpa [prefixWord, tailWord_7407217, baseEnd_7407217] using wordTrace_append hprefix tailTrace_7407217
  have hstable : (prefixWord ++ tailWord_7407217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407217).length < 2 ^ (prefixWord ++ tailWord_7407217).sum := by decide
  have hdescent : baseEnd_7407217 < baseStart_7407217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407308 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7407308 : Nat := 118140960795 + 7407308 * 2 ^ 59
def prefixEnd_7407308 : Nat := 4983230072969 + 3 ^ 40 * 7407308 * 2
def baseEnd_7407308 : Nat := 3803509359894210107084417

theorem tailTrace_7407308 : CollatzResearch.WordTrace tailWord_7407308 prefixEnd_7407308 3803509359894210107084417 := by
  unfold tailWord_7407308
  simp only [CollatzResearch.WordTrace]
  refine ⟨135083358924297829167171289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180111145232397105556228385 135083358924297829167171289)
  ·
    refine ⟨101312519193223371875378467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135083358924297829167171289 101312519193223371875378467)
    ·
      refine ⟨151968778789835057813067701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101312519193223371875378467 151968778789835057813067701)
      ·
        refine ⟨14247073011547036669975097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151968778789835057813067701 14247073011547036669975097)
        ·
          refine ⟨10685304758660277502481323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14247073011547036669975097 10685304758660277502481323)
          ·
            refine ⟨16027957137990416253721985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10685304758660277502481323 16027957137990416253721985)
            ·
              refine ⟨12020967853492812190291489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16027957137990416253721985 12020967853492812190291489)
              ·
                refine ⟨9015725890119609142718617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12020967853492812190291489 9015725890119609142718617)
                ·
                  refine ⟨6761794417589706857038963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9015725890119609142718617 6761794417589706857038963)
                  ·
                    refine ⟨10142691626384560285558445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6761794417589706857038963 10142691626384560285558445)
                    ·
                      refine ⟨3803509359894210107084417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10142691626384560285558445 3803509359894210107084417)
                      ·
                        rfl

theorem cell23_7407308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7407308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407308 prefixEnd_7407308 := by exact prefixLift 7407308
  have htrace : WordTrace (prefixWord ++ tailWord_7407308) baseStart_7407308 baseEnd_7407308 := by
    simpa [prefixWord, tailWord_7407308, baseEnd_7407308] using wordTrace_append hprefix tailTrace_7407308
  have hstable : (prefixWord ++ tailWord_7407308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407308).length < 2 ^ (prefixWord ++ tailWord_7407308).sum := by decide
  have hdescent : baseEnd_7407308 < baseStart_7407308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407309 : List Nat := [1, 6, 2, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_7407309 : Nat := 118140960795 + 7407309 * 2 ^ 59
def prefixEnd_7407309 : Nat := 4983230072969 + 3 ^ 40 * 7407309 * 2
def baseEnd_7407309 : Nat := 3803509873374864603171913

theorem tailTrace_7407309 : CollatzResearch.WordTrace tailWord_7407309 prefixEnd_7407309 3803509873374864603171913 := by
  unfold tailWord_7407309
  simp only [CollatzResearch.WordTrace]
  refine ⟨270166754321592035505128981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180111169547728023670085987 270166754321592035505128981)
  ·
    refine ⟨12664066608824626664302921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 270166754321592035505128981 12664066608824626664302921)
    ·
      refine ⟨9498049956618469998227191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12664066608824626664302921 9498049956618469998227191)
      ·
        refine ⟨14247074934927704997340787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9498049956618469998227191 14247074934927704997340787)
        ·
          refine ⟨21370612402391557496011181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14247074934927704997340787 21370612402391557496011181)
          ·
            refine ⟨8013979650896834061004193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21370612402391557496011181 8013979650896834061004193)
            ·
              refine ⟨6010484738172625545753145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8013979650896834061004193 6010484738172625545753145)
              ·
                refine ⟨4507863553629469159314859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010484738172625545753145 4507863553629469159314859)
                ·
                  refine ⟨6761795330444203738972289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507863553629469159314859 6761795330444203738972289)
                  ·
                    refine ⟨5071346497833152804229217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6761795330444203738972289 5071346497833152804229217)
                    ·
                      refine ⟨3803509873374864603171913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071346497833152804229217 3803509873374864603171913)
                      ·
                        rfl

theorem cell23_7407309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_7407309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407309 prefixEnd_7407309 := by exact prefixLift 7407309
  have htrace : WordTrace (prefixWord ++ tailWord_7407309) baseStart_7407309 baseEnd_7407309 := by
    simpa [prefixWord, tailWord_7407309, baseEnd_7407309] using wordTrace_append hprefix tailTrace_7407309
  have hstable : (prefixWord ++ tailWord_7407309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407309).length < 2 ^ (prefixWord ++ tailWord_7407309).sum := by decide
  have hdescent : baseEnd_7407309 < baseStart_7407309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407327 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_7407327 : Nat := 118140960795 + 7407327 * 2 ^ 59
def prefixEnd_7407327 : Nat := 4983230072969 + 3 ^ 40 * 7407327 * 2
def baseEnd_7407327 : Nat := 3803519116026645532746829

theorem tailTrace_7407327 : CollatzResearch.WordTrace tailWord_7407327 prefixEnd_7407327 3803519116026645532746829 := by
  unfold tailWord_7407327
  simp only [CollatzResearch.WordTrace]
  refine ⟨270167410835526824579284235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180111607223684549719522823 270167410835526824579284235)
  ·
    refine ⟨405251116253290236868926353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270167410835526824579284235 405251116253290236868926353)
    ·
      refine ⟨303938337189967677651694765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405251116253290236868926353 303938337189967677651694765)
      ·
        refine ⟨113976876446237879119385537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303938337189967677651694765 113976876446237879119385537)
        ·
          refine ⟨85482657334678409339539153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113976876446237879119385537 85482657334678409339539153)
          ·
            refine ⟨64111993001008807004654365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85482657334678409339539153 64111993001008807004654365)
            ·
              refine ⟨24041997375378302626745387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64111993001008807004654365 24041997375378302626745387)
              ·
                refine ⟨36062996063067453940118081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24041997375378302626745387 36062996063067453940118081)
                ·
                  refine ⟨27047247047300590455088561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36062996063067453940118081 27047247047300590455088561)
                  ·
                    refine ⟨20285435285475442841316421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27047247047300590455088561 20285435285475442841316421)
                    ·
                      refine ⟨3803519116026645532746829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20285435285475442841316421 3803519116026645532746829)
                      ·
                        rfl

theorem cell23_7407327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_7407327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407327 prefixEnd_7407327 := by exact prefixLift 7407327
  have htrace : WordTrace (prefixWord ++ tailWord_7407327) baseStart_7407327 baseEnd_7407327 := by
    simpa [prefixWord, tailWord_7407327, baseEnd_7407327] using wordTrace_append hprefix tailTrace_7407327
  have hstable : (prefixWord ++ tailWord_7407327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407327).length < 2 ^ (prefixWord ++ tailWord_7407327).sum := by decide
  have hdescent : baseEnd_7407327 < baseStart_7407327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407364 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_7407364 : Nat := 118140960795 + 7407364 * 2 ^ 59
def prefixEnd_7407364 : Nat := 4983230072969 + 3 ^ 40 * 7407364 * 2
def baseEnd_7407364 : Nat := 3803538114810861887984159

theorem tailTrace_7407364 : CollatzResearch.WordTrace tailWord_7407364 prefixEnd_7407364 3803538114810861887984159 := by
  unfold tailWord_7407364
  simp only [CollatzResearch.WordTrace]
  refine ⟨135084380168196389949190573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180112506890928519932254097 135084380168196389949190573)
  ·
    refine ⟨50656642563073646230946465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135084380168196389949190573 50656642563073646230946465)
    ·
      refine ⟨37992481922305234673209849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50656642563073646230946465 37992481922305234673209849)
      ·
        refine ⟨28494361441728926004907387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37992481922305234673209849 28494361441728926004907387)
        ·
          refine ⟨42741542162593389007361081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28494361441728926004907387 42741542162593389007361081)
          ·
            refine ⟨32056156621945041755520811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42741542162593389007361081 32056156621945041755520811)
            ·
              refine ⟨48084234932917562633281217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32056156621945041755520811 48084234932917562633281217)
              ·
                refine ⟨36063176199688171974960913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48084234932917562633281217 36063176199688171974960913)
                ·
                  refine ⟨27047382149766128981220685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36063176199688171974960913 27047382149766128981220685)
                  ·
                    refine ⟨10142768306162298367957757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27047382149766128981220685 10142768306162298367957757)
                    ·
                      refine ⟨3803538114810861887984159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10142768306162298367957757 3803538114810861887984159)
                      ·
                        rfl

theorem cell23_7407364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_7407364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407364 prefixEnd_7407364 := by exact prefixLift 7407364
  have htrace : WordTrace (prefixWord ++ tailWord_7407364) baseStart_7407364 baseEnd_7407364 := by
    simpa [prefixWord, tailWord_7407364, baseEnd_7407364] using wordTrace_append hprefix tailTrace_7407364
  have hstable : (prefixWord ++ tailWord_7407364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407364).length < 2 ^ (prefixWord ++ tailWord_7407364).sum := by decide
  have hdescent : baseEnd_7407364 < baseStart_7407364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407374 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_7407374 : Nat := 118140960795 + 7407374 * 2 ^ 59
def prefixEnd_7407374 : Nat := 4983230072969 + 3 ^ 40 * 7407374 * 2
def baseEnd_7407374 : Nat := 3803543249617406848859113

theorem tailTrace_7407374 : CollatzResearch.WordTrace tailWord_7407374 prefixEnd_7407374 3803543249617406848859113 := by
  unfold tailWord_7407374
  simp only [CollatzResearch.WordTrace]
  refine ⟨33771140633294568950780647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180112750044237701070830117 33771140633294568950780647)
  ·
    refine ⟨50656710949941853426170971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33771140633294568950780647 50656710949941853426170971)
    ·
      refine ⟨75985066424912780139256457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50656710949941853426170971 75985066424912780139256457)
      ·
        refine ⟨56988799818684585104442343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75985066424912780139256457 56988799818684585104442343)
        ·
          refine ⟨85483199728026877656663515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56988799818684585104442343 85483199728026877656663515)
          ·
            refine ⟨128224799592040316484995273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85483199728026877656663515 128224799592040316484995273)
            ·
              refine ⟨96168599694030237363746455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128224799592040316484995273 96168599694030237363746455)
              ·
                refine ⟨144252899541045356045619683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96168599694030237363746455 144252899541045356045619683)
                ·
                  refine ⟨216379349311568034068429525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144252899541045356045619683 216379349311568034068429525)
                  ·
                    refine ⟨5071390999489875798478817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 216379349311568034068429525 5071390999489875798478817)
                    ·
                      refine ⟨3803543249617406848859113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071390999489875798478817 3803543249617406848859113)
                      ·
                        rfl

theorem cell23_7407374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_7407374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407374 prefixEnd_7407374 := by exact prefixLift 7407374
  have htrace : WordTrace (prefixWord ++ tailWord_7407374) baseStart_7407374 baseEnd_7407374 := by
    simpa [prefixWord, tailWord_7407374, baseEnd_7407374] using wordTrace_append hprefix tailTrace_7407374
  have hstable : (prefixWord ++ tailWord_7407374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407374).length < 2 ^ (prefixWord ++ tailWord_7407374).sum := by decide
  have hdescent : baseEnd_7407374 < baseStart_7407374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407387 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 4]
def baseStart_7407387 : Nat := 118140960795 + 7407387 * 2 ^ 59
def prefixEnd_7407387 : Nat := 4983230072969 + 3 ^ 40 * 7407387 * 2
def baseEnd_7407387 : Nat := 3803549924865915297996553

theorem tailTrace_7407387 : CollatzResearch.WordTrace tailWord_7407387 prefixEnd_7407387 3803549924865915297996553 := by
  unfold tailWord_7407387
  simp only [CollatzResearch.WordTrace]
  refine ⟨270169599215309454826468415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180113066143539636550978943 270169599215309454826468415)
  ·
    refine ⟨405254398822964182239702623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270169599215309454826468415 405254398822964182239702623)
    ·
      refine ⟨607881598234446273359553935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405254398822964182239702623 607881598234446273359553935)
      ·
        refine ⟨911822397351669410039330903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607881598234446273359553935 911822397351669410039330903)
        ·
          refine ⟨1367733596027504115058996355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911822397351669410039330903 1367733596027504115058996355)
          ·
            refine ⟨2051600394041256172588494533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367733596027504115058996355 2051600394041256172588494533)
            ·
              refine ⟨384675073882735532360342725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2051600394041256172588494533 384675073882735532360342725)
              ·
                refine ⟨72126576353012912317564261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384675073882735532360342725 72126576353012912317564261)
                ·
                  refine ⟨13523733066189921059543299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72126576353012912317564261 13523733066189921059543299)
                  ·
                    refine ⟨20285599599284881589314949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13523733066189921059543299 20285599599284881589314949)
                    ·
                      refine ⟨3803549924865915297996553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20285599599284881589314949 3803549924865915297996553)
                      ·
                        rfl

theorem cell23_7407387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 4].length) (baseStart_7407387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407387 prefixEnd_7407387 := by exact prefixLift 7407387
  have htrace : WordTrace (prefixWord ++ tailWord_7407387) baseStart_7407387 baseEnd_7407387 := by
    simpa [prefixWord, tailWord_7407387, baseEnd_7407387] using wordTrace_append hprefix tailTrace_7407387
  have hstable : (prefixWord ++ tailWord_7407387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407387).length < 2 ^ (prefixWord ++ tailWord_7407387).sum := by decide
  have hdescent : baseEnd_7407387 < baseStart_7407387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407421 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7407421 : Nat := 118140960795 + 7407421 * 2 ^ 59
def prefixEnd_7407421 : Nat := 4983230072969 + 3 ^ 40 * 7407421 * 2
def baseEnd_7407421 : Nat := 3803567383208168164971397

theorem tailTrace_7407421 : CollatzResearch.WordTrace tailWord_7407421 prefixEnd_7407421 3803567383208168164971397 := by
  unfold tailWord_7407421
  simp only [CollatzResearch.WordTrace]
  refine ⟨270170839297186278633206117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180113892864790852422137411 270170839297186278633206117)
  ·
    refine ⟨50657032368222427243726147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270170839297186278633206117 50657032368222427243726147)
    ·
      refine ⟨75985548552333640865589221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50657032368222427243726147 75985548552333640865589221)
      ·
        refine ⟨14247290353562557662297979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75985548552333640865589221 14247290353562557662297979)
        ·
          refine ⟨21370935530343836493446969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14247290353562557662297979 21370935530343836493446969)
          ·
            refine ⟨16028201647757877370085227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21370935530343836493446969 16028201647757877370085227)
            ·
              refine ⟨24042302471636816055127841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16028201647757877370085227 24042302471636816055127841)
              ·
                refine ⟨18031726853727612041345881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24042302471636816055127841 18031726853727612041345881)
                ·
                  refine ⟨13523795140295709031009411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18031726853727612041345881 13523795140295709031009411)
                  ·
                    refine ⟨20285692710443563546514117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13523795140295709031009411 20285692710443563546514117)
                    ·
                      refine ⟨3803567383208168164971397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20285692710443563546514117 3803567383208168164971397)
                      ·
                        rfl

theorem cell23_7407421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7407421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407421 prefixEnd_7407421 := by exact prefixLift 7407421
  have htrace : WordTrace (prefixWord ++ tailWord_7407421) baseStart_7407421 baseEnd_7407421 := by
    simpa [prefixWord, tailWord_7407421, baseEnd_7407421] using wordTrace_append hprefix tailTrace_7407421
  have hstable : (prefixWord ++ tailWord_7407421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407421).length < 2 ^ (prefixWord ++ tailWord_7407421).sum := by decide
  have hdescent : baseEnd_7407421 < baseStart_7407421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407427 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 8]
def baseStart_7407427 : Nat := 118140960795 + 7407427 * 2 ^ 59
def prefixEnd_7407427 : Nat := 4983230072969 + 3 ^ 40 * 7407427 * 2
def baseEnd_7407427 : Nat := 422618940454677237944041

theorem tailTrace_7407427 : CollatzResearch.WordTrace tailWord_7407427 prefixEnd_7407427 422618940454677237944041 := by
  unfold tailWord_7407427
  simp only [CollatzResearch.WordTrace]
  refine ⟨270171058135164541657924535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180114038756776361105283023 270171058135164541657924535)
  ·
    refine ⟨405256587202746812486886803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270171058135164541657924535 405256587202746812486886803)
    ·
      refine ⟨607884880804120218730330205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405256587202746812486886803 607884880804120218730330205)
      ·
        refine ⟨227956830301545082023873827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607884880804120218730330205 227956830301545082023873827)
        ·
          refine ⟨341935245452317623035810741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227956830301545082023873827 341935245452317623035810741)
          ·
            refine ⟨32056429261154777159607257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341935245452317623035810741 32056429261154777159607257)
            ·
              refine ⟨24042321945866082869705443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32056429261154777159607257 24042321945866082869705443)
              ·
                refine ⟨36063482918799124304558165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24042321945866082869705443 36063482918799124304558165)
                ·
                  refine ⟨422618940454677237944041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36063482918799124304558165 422618940454677237944041)
                  ·
                    rfl

theorem cell23_7407427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 8].length) (baseStart_7407427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407427 prefixEnd_7407427 := by exact prefixLift 7407427
  have htrace : WordTrace (prefixWord ++ tailWord_7407427) baseStart_7407427 baseEnd_7407427 := by
    simpa [prefixWord, tailWord_7407427, baseEnd_7407427] using wordTrace_append hprefix tailTrace_7407427
  have hstable : (prefixWord ++ tailWord_7407427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407427).length < 2 ^ (prefixWord ++ tailWord_7407427).sum := by decide
  have hdescent : baseEnd_7407427 < baseStart_7407427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407431 : List Nat := [1, 1, 4, 1, 2, 1, 2, 6, 1, 4]
def baseStart_7407431 : Nat := 118140960795 + 7407431 * 2 ^ 59
def prefixEnd_7407431 : Nat := 4983230072969 + 3 ^ 40 * 7407431 * 2
def baseEnd_7407431 : Nat := 1267857506004904375282117

theorem tailTrace_7407431 : CollatzResearch.WordTrace tailWord_7407431 prefixEnd_7407431 1267857506004904375282117 := by
  unfold tailWord_7407431
  simp only [CollatzResearch.WordTrace]
  refine ⟨270171204027150050341070147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180114136018100033560713431 270171204027150050341070147)
  ·
    refine ⟨405256806040725075511605221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270171204027150050341070147 405256806040725075511605221)
    ·
      refine ⟨75985651132635951658425979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405256806040725075511605221 75985651132635951658425979)
      ·
        refine ⟨113978476698953927487638969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75985651132635951658425979 113978476698953927487638969)
        ·
          refine ⟨85483857524215445615729227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113978476698953927487638969 85483857524215445615729227)
          ·
            refine ⟨128225786286323168423593841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85483857524215445615729227 128225786286323168423593841)
            ·
              refine ⟨96169339714742376317695381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128225786286323168423593841 96169339714742376317695381)
              ·
                refine ⟨4507937799128548889891971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96169339714742376317695381 4507937799128548889891971)
                ·
                  refine ⟨6761906698692823334837957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507937799128548889891971 6761906698692823334837957)
                  ·
                    refine ⟨1267857506004904375282117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761906698692823334837957 1267857506004904375282117)
                    ·
                      rfl

theorem cell23_7407431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_7407431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407431 prefixEnd_7407431 := by exact prefixLift 7407431
  have htrace : WordTrace (prefixWord ++ tailWord_7407431) baseStart_7407431 baseEnd_7407431 := by
    simpa [prefixWord, tailWord_7407431, baseEnd_7407431] using wordTrace_append hprefix tailTrace_7407431
  have hstable : (prefixWord ++ tailWord_7407431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407431).length < 2 ^ (prefixWord ++ tailWord_7407431).sum := by decide
  have hdescent : baseEnd_7407431 < baseStart_7407431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407458 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_7407458 : Nat := 118140960795 + 7407458 * 2 ^ 59
def prefixEnd_7407458 : Nat := 4983230072969 + 3 ^ 40 * 7407458 * 2
def baseEnd_7407458 : Nat := 3803586381992384520208727

theorem tailTrace_7407458 : CollatzResearch.WordTrace tailWord_7407458 prefixEnd_7407458 3803586381992384520208727 := by
  unfold tailWord_7407458
  simp only [CollatzResearch.WordTrace]
  refine ⟨67543047199513058488075757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180114792532034822634868685 67543047199513058488075757)
  ·
    refine ⟨25328642699817396933028409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67543047199513058488075757 25328642699817396933028409)
    ·
      refine ⟨18996482024863047699771307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25328642699817396933028409 18996482024863047699771307)
      ·
        refine ⟨28494723037294571549656961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18996482024863047699771307 28494723037294571549656961)
        ·
          refine ⟨21371042277970928662242721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28494723037294571549656961 21371042277970928662242721)
          ·
            refine ⟨16028281708478196496682041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21371042277970928662242721 16028281708478196496682041)
            ·
              refine ⟨12021211281358647372511531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16028281708478196496682041 12021211281358647372511531)
              ·
                refine ⟨18031816922037971058767297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12021211281358647372511531 18031816922037971058767297)
                ·
                  refine ⟨13523862691528478294075473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18031816922037971058767297 13523862691528478294075473)
                  ·
                    refine ⟨10142897018646358720556605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13523862691528478294075473 10142897018646358720556605)
                    ·
                      refine ⟨3803586381992384520208727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10142897018646358720556605 3803586381992384520208727)
                      ·
                        rfl

theorem cell23_7407458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_7407458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407458 prefixEnd_7407458 := by exact prefixLift 7407458
  have htrace : WordTrace (prefixWord ++ tailWord_7407458) baseStart_7407458 baseEnd_7407458 := by
    simpa [prefixWord, tailWord_7407458, baseEnd_7407458] using wordTrace_append hprefix tailTrace_7407458
  have hstable : (prefixWord ++ tailWord_7407458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407458).length < 2 ^ (prefixWord ++ tailWord_7407458).sum := by decide
  have hdescent : baseEnd_7407458 < baseStart_7407458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407478 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_7407478 : Nat := 118140960795 + 7407478 * 2 ^ 59
def prefixEnd_7407478 : Nat := 4983230072969 + 3 ^ 40 * 7407478 * 2
def baseEnd_7407478 : Nat := 422621850178386049106515

theorem tailTrace_7407478 : CollatzResearch.WordTrace tailWord_7407478 prefixEnd_7407478 422621850178386049106515 := by
  unfold tailWord_7407478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16885807391123736085501943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180115278838653184912020725 16885807391123736085501943)
  ·
    refine ⟨25328711086685604128252915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16885807391123736085501943 25328711086685604128252915)
    ·
      refine ⟨37993066630028406192379373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25328711086685604128252915 37993066630028406192379373)
      ·
        refine ⟨14247399986260652322142265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37993066630028406192379373 14247399986260652322142265)
        ·
          refine ⟨10685549989695489241606699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14247399986260652322142265 10685549989695489241606699)
          ·
            refine ⟨16028324984543233862410049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10685549989695489241606699 16028324984543233862410049)
            ·
              refine ⟨12021243738407425396807537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16028324984543233862410049 12021243738407425396807537)
              ·
                refine ⟨9015932803805569047605653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12021243738407425396807537 9015932803805569047605653)
                ·
                  refine ⟨422621850178386049106515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9015932803805569047605653 422621850178386049106515)
                  ·
                    rfl

theorem cell23_7407478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_7407478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407478 prefixEnd_7407478 := by exact prefixLift 7407478
  have htrace : WordTrace (prefixWord ++ tailWord_7407478) baseStart_7407478 baseEnd_7407478 := by
    simpa [prefixWord, tailWord_7407478, baseEnd_7407478] using wordTrace_append hprefix tailTrace_7407478
  have hstable : (prefixWord ++ tailWord_7407478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407478).length < 2 ^ (prefixWord ++ tailWord_7407478).sum := by decide
  have hdescent : baseEnd_7407478 < baseStart_7407478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407481 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 2, 3, 2]
def baseStart_7407481 : Nat := 118140960795 + 7407481 * 2 ^ 59
def prefixEnd_7407481 : Nat := 4983230072969 + 3 ^ 40 * 7407481 * 2
def baseEnd_7407481 : Nat := 3803598192047437930221121

theorem tailTrace_7407481 : CollatzResearch.WordTrace tailWord_7407481 prefixEnd_7407481 3803598192047437930221121 := by
  unfold tailWord_7407481
  simp only [CollatzResearch.WordTrace]
  refine ⟨270173027676968908880390297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180115351784645939253593531 270173027676968908880390297)
  ·
    refine ⟨202629770757726681660292723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270173027676968908880390297 202629770757726681660292723)
    ·
      refine ⟨303944656136590022490439085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202629770757726681660292723 303944656136590022490439085)
      ·
        refine ⟨113979246051221258433914657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303944656136590022490439085 113979246051221258433914657)
        ·
          refine ⟨85484434538415943825435993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113979246051221258433914657 85484434538415943825435993)
          ·
            refine ⟨64113325903811957869076995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85484434538415943825435993 64113325903811957869076995)
            ·
              refine ⟨96169988855717936803615493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64113325903811957869076995 96169988855717936803615493)
              ·
                refine ⟨18031872910447113150677905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96169988855717936803615493 18031872910447113150677905)
                ·
                  refine ⟨13523904682835334863008429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18031872910447113150677905 13523904682835334863008429)
                  ·
                    refine ⟨5071464256063250573628161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13523904682835334863008429 5071464256063250573628161)
                    ·
                      refine ⟨3803598192047437930221121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071464256063250573628161 3803598192047437930221121)
                      ·
                        rfl

theorem cell23_7407481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_7407481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407481 prefixEnd_7407481 := by exact prefixLift 7407481
  have htrace : WordTrace (prefixWord ++ tailWord_7407481) baseStart_7407481 baseEnd_7407481 := by
    simpa [prefixWord, tailWord_7407481, baseEnd_7407481] using wordTrace_append hprefix tailTrace_7407481
  have hstable : (prefixWord ++ tailWord_7407481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407481).length < 2 ^ (prefixWord ++ tailWord_7407481).sum := by decide
  have hdescent : baseEnd_7407481 < baseStart_7407481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407487 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 5, 6]
def baseStart_7407487 : Nat := 118140960795 + 7407487 * 2 ^ 59
def prefixEnd_7407487 : Nat := 4983230072969 + 3 ^ 40 * 7407487 * 2
def baseEnd_7407487 : Nat := 1267867090977121635582031

theorem tailTrace_7407487 : CollatzResearch.WordTrace tailWord_7407487 prefixEnd_7407487 1267867090977121635582031 := by
  unfold tailWord_7407487
  simp only [CollatzResearch.WordTrace]
  refine ⟨270173246514947171905108715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180115497676631447936739143 270173246514947171905108715)
  ·
    refine ⟨405259869772420757857663073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270173246514947171905108715 405259869772420757857663073)
    ·
      refine ⟨303944902329315568393247305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405259869772420757857663073 303944902329315568393247305)
      ·
        refine ⟨227958676746986676294935479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303944902329315568393247305 227958676746986676294935479)
        ·
          refine ⟨341938015120480014442403219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227958676746986676294935479 341938015120480014442403219)
          ·
            refine ⟨512907022680720021663604829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341938015120480014442403219 512907022680720021663604829)
            ·
              refine ⟨192340133505270008123851811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512907022680720021663604829 192340133505270008123851811)
              ·
                refine ⟨288510200257905012185777717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192340133505270008123851811 288510200257905012185777717)
                ·
                  refine ⟨27047831274178594892416661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288510200257905012185777717 27047831274178594892416661)
                  ·
                    refine ⟨1267867090977121635582031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27047831274178594892416661 1267867090977121635582031)
                    ·
                      rfl

theorem cell23_7407487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_7407487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407487 prefixEnd_7407487 := by exact prefixLift 7407487
  have htrace : WordTrace (prefixWord ++ tailWord_7407487) baseStart_7407487 baseEnd_7407487 := by
    simpa [prefixWord, tailWord_7407487, baseEnd_7407487] using wordTrace_append hprefix tailTrace_7407487
  have hstable : (prefixWord ++ tailWord_7407487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407487).length < 2 ^ (prefixWord ++ tailWord_7407487).sum := by decide
  have hdescent : baseEnd_7407487 < baseStart_7407487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407488 : List Nat := [2, 1, 1, 2, 1, 2, 5, 4, 1, 1, 3]
def baseStart_7407488 : Nat := 118140960795 + 7407488 * 2 ^ 59
def prefixEnd_7407488 : Nat := 4983230072969 + 3 ^ 40 * 7407488 * 2
def baseEnd_7407488 : Nat := 3803601786412019402833589

theorem tailTrace_7407488 : CollatzResearch.WordTrace tailWord_7407488 prefixEnd_7407488 3803601786412019402833589 := by
  unfold tailWord_7407488
  simp only [CollatzResearch.WordTrace]
  refine ⟨135086641493971774537947559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180115521991962366050596745 135086641493971774537947559)
  ·
    refine ⟨202629962240957661806921339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135086641493971774537947559 202629962240957661806921339)
    ·
      refine ⟨303944943361436492710382009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202629962240957661806921339 303944943361436492710382009)
      ·
        refine ⟨227958707521077369532786507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303944943361436492710382009 227958707521077369532786507)
        ·
          refine ⟨341938061281616054299179761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227958707521077369532786507 341938061281616054299179761)
          ·
            refine ⟨256453545961212040724384821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341938061281616054299179761 256453545961212040724384821)
            ·
              refine ⟨24042519933863628817911077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 256453545961212040724384821 24042519933863628817911077)
              ·
                refine ⟨4507972487599430403358327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24042519933863628817911077 4507972487599430403358327)
                ·
                  refine ⟨6761958731399145605037491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507972487599430403358327 6761958731399145605037491)
                  ·
                    refine ⟨10142938097098718407556237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6761958731399145605037491 10142938097098718407556237)
                    ·
                      refine ⟨3803601786412019402833589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10142938097098718407556237 3803601786412019402833589)
                      ·
                        rfl

theorem cell23_7407488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_7407488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407488 prefixEnd_7407488 := by exact prefixLift 7407488
  have htrace : WordTrace (prefixWord ++ tailWord_7407488) baseStart_7407488 baseEnd_7407488 := by
    simpa [prefixWord, tailWord_7407488, baseEnd_7407488] using wordTrace_append hprefix tailTrace_7407488
  have hstable : (prefixWord ++ tailWord_7407488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407488).length < 2 ^ (prefixWord ++ tailWord_7407488).sum := by decide
  have hdescent : baseEnd_7407488 < baseStart_7407488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407507 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 6]
def baseStart_7407507 : Nat := 118140960795 + 7407507 * 2 ^ 59
def prefixEnd_7407507 : Nat := 4983230072969 + 3 ^ 40 * 7407507 * 2
def baseEnd_7407507 : Nat := 3803611542544454828496001

theorem tailTrace_7407507 : CollatzResearch.WordTrace tailWord_7407507 prefixEnd_7407507 3803611542544454828496001 := by
  unfold tailWord_7407507
  simp only [CollatzResearch.WordTrace]
  refine ⟨270173975974874715320836775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180115983983249810213891183 270173975974874715320836775)
  ·
    refine ⟨405260963962312072981255163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270173975974874715320836775 405260963962312072981255163)
    ·
      refine ⟨607891445943468109471882745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405260963962312072981255163 607891445943468109471882745)
      ·
        refine ⟨455918584457601082103912059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607891445943468109471882745 455918584457601082103912059)
        ·
          refine ⟨683877876686401623155868089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455918584457601082103912059 683877876686401623155868089)
          ·
            refine ⟨512908407514801217366901067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683877876686401623155868089 512908407514801217366901067)
            ·
              refine ⟨769362611272201826050351601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512908407514801217366901067 769362611272201826050351601)
              ·
                refine ⟨577021958454151369537763701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769362611272201826050351601 577021958454151369537763701)
                ·
                  refine ⟨54095808605076690894165347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577021958454151369537763701 54095808605076690894165347)
                  ·
                    refine ⟨81143712907615036341248021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54095808605076690894165347 81143712907615036341248021)
                    ·
                      refine ⟨3803611542544454828496001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81143712907615036341248021 3803611542544454828496001)
                      ·
                        rfl

theorem cell23_7407507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_7407507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407507 prefixEnd_7407507 := by exact prefixLift 7407507
  have htrace : WordTrace (prefixWord ++ tailWord_7407507) baseStart_7407507 baseEnd_7407507 := by
    simpa [prefixWord, tailWord_7407507, baseEnd_7407507] using wordTrace_append hprefix tailTrace_7407507
  have hstable : (prefixWord ++ tailWord_7407507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407507).length < 2 ^ (prefixWord ++ tailWord_7407507).sum := by decide
  have hdescent : baseEnd_7407507 < baseStart_7407507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407522 : List Nat := [3, 3, 1, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_7407522 : Nat := 118140960795 + 7407522 * 2 ^ 59
def prefixEnd_7407522 : Nat := 4983230072969 + 3 ^ 40 * 7407522 * 2
def baseEnd_7407522 : Nat := 3803619244754272269808433

theorem tailTrace_7407522 : CollatzResearch.WordTrace tailWord_7407522 prefixEnd_7407522 3803619244754272269808433 := by
  unfold tailWord_7407522
  simp only [CollatzResearch.WordTrace]
  refine ⟨67543630767455093220658205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180116348713213581921755213 67543630767455093220658205)
  ·
    refine ⟨25328861537795659957746827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67543630767455093220658205 25328861537795659957746827)
    ·
      refine ⟨37993292306693489936620241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25328861537795659957746827 37993292306693489936620241)
      ·
        refine ⟨28494969230020117452465181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37993292306693489936620241 28494969230020117452465181)
        ·
          refine ⟨10685613461257544044674443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28494969230020117452465181 10685613461257544044674443)
          ·
            refine ⟨16028420191886316067011665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10685613461257544044674443 16028420191886316067011665)
            ·
              refine ⟨12021315143914737050258749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16028420191886316067011665 12021315143914737050258749)
              ·
                refine ⟨4507993178968026393847031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12021315143914737050258749 4507993178968026393847031)
                ·
                  refine ⟨6761989768452039590770547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507993178968026393847031 6761989768452039590770547)
                  ·
                    refine ⟨10142984652678059386155821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6761989768452039590770547 10142984652678059386155821)
                    ·
                      refine ⟨3803619244754272269808433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10142984652678059386155821 3803619244754272269808433)
                      ·
                        rfl

theorem cell23_7407522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_7407522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407522 prefixEnd_7407522 := by exact prefixLift 7407522
  have htrace : WordTrace (prefixWord ++ tailWord_7407522) baseStart_7407522 baseEnd_7407522 := by
    simpa [prefixWord, tailWord_7407522, baseEnd_7407522] using wordTrace_append hprefix tailTrace_7407522
  have hstable : (prefixWord ++ tailWord_7407522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407522).length < 2 ^ (prefixWord ++ tailWord_7407522).sum := by decide
  have hdescent : baseEnd_7407522 < baseStart_7407522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407545 : List Nat := [1, 2, 1, 4, 2, 1, 1, 6, 1, 2, 2]
def baseStart_7407545 : Nat := 118140960795 + 7407545 * 2 ^ 59
def prefixEnd_7407545 : Nat := 4983230072969 + 3 ^ 40 * 7407545 * 2
def baseEnd_7407545 : Nat := 3803631054809325679820827

theorem tailTrace_7407545 : CollatzResearch.WordTrace tailWord_7407545 prefixEnd_7407545 3803631054809325679820827 := by
  unfold tailWord_7407545
  simp only [CollatzResearch.WordTrace]
  refine ⟨270175361948737047810720089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180116907965824698540480059 270175361948737047810720089)
  ·
    refine ⟨202631521461552785858040067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270175361948737047810720089 202631521461552785858040067)
    ·
      refine ⟨303947282192329178787060101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202631521461552785858040067 303947282192329178787060101)
      ·
        refine ⟨56990115411061721022573769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303947282192329178787060101 56990115411061721022573769)
        ·
          refine ⟨42742586558296290766930327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56990115411061721022573769 42742586558296290766930327)
          ·
            refine ⟨64113879837444436150395491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42742586558296290766930327 64113879837444436150395491)
            ·
              refine ⟨96170819756166654225593237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64113879837444436150395491 96170819756166654225593237)
              ·
                refine ⟨4508007176070311916824683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96170819756166654225593237 4508007176070311916824683)
                ·
                  refine ⟨6762010764105467875237025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508007176070311916824683 6762010764105467875237025)
                  ·
                    refine ⟨5071508073079100906427769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6762010764105467875237025 5071508073079100906427769)
                    ·
                      refine ⟨3803631054809325679820827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071508073079100906427769 3803631054809325679820827)
                      ·
                        rfl

theorem cell23_7407545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_7407545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407545 prefixEnd_7407545 := by exact prefixLift 7407545
  have htrace : WordTrace (prefixWord ++ tailWord_7407545) baseStart_7407545 baseEnd_7407545 := by
    simpa [prefixWord, tailWord_7407545, baseEnd_7407545] using wordTrace_append hprefix tailTrace_7407545
  have hstable : (prefixWord ++ tailWord_7407545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407545).length < 2 ^ (prefixWord ++ tailWord_7407545).sum := by decide
  have hdescent : baseEnd_7407545 < baseStart_7407545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407548 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7407548 : Nat := 118140960795 + 7407548 * 2 ^ 59
def prefixEnd_7407548 : Nat := 4983230072969 + 3 ^ 40 * 7407548 * 2
def baseEnd_7407548 : Nat := 3803632595251289168083313

theorem tailTrace_7407548 : CollatzResearch.WordTrace tailWord_7407548 prefixEnd_7407548 3803632595251289168083313 := by
  unfold tailWord_7407548
  simp only [CollatzResearch.WordTrace]
  refine ⟨135087735683863089661539649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180116980911817452882052865 135087735683863089661539649)
  ·
    refine ⟨101315801762897317246154737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135087735683863089661539649 101315801762897317246154737)
    ·
      refine ⟨75986851322172987934616053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101315801762897317246154737 75986851322172987934616053)
      ·
        refine ⟨7123767311453717618870255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75986851322172987934616053 7123767311453717618870255)
        ·
          refine ⟨10685650967180576428305383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123767311453717618870255 10685650967180576428305383)
          ·
            refine ⟨16028476450770864642458075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10685650967180576428305383 16028476450770864642458075)
            ·
              refine ⟨24042714676156296963687113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16028476450770864642458075 24042714676156296963687113)
              ·
                refine ⟨18032036007117222722765335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24042714676156296963687113 18032036007117222722765335)
                ·
                  refine ⟨27048054010675834084148003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18032036007117222722765335 27048054010675834084148003)
                  ·
                    refine ⟨40572081016013751126222005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27048054010675834084148003 40572081016013751126222005)
                    ·
                      refine ⟨3803632595251289168083313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40572081016013751126222005 3803632595251289168083313)
                      ·
                        rfl

theorem cell23_7407548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7407548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407548 prefixEnd_7407548 := by exact prefixLift 7407548
  have htrace : WordTrace (prefixWord ++ tailWord_7407548) baseStart_7407548 baseEnd_7407548 := by
    simpa [prefixWord, tailWord_7407548, baseEnd_7407548] using wordTrace_append hprefix tailTrace_7407548
  have hstable : (prefixWord ++ tailWord_7407548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407548).length < 2 ^ (prefixWord ++ tailWord_7407548).sum := by decide
  have hdescent : baseEnd_7407548 < baseStart_7407548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407588 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_7407588 : Nat := 118140960795 + 7407588 * 2 ^ 59
def prefixEnd_7407588 : Nat := 4983230072969 + 3 ^ 40 * 7407588 * 2
def baseEnd_7407588 : Nat := 3803653134477469011583129

theorem tailTrace_7407588 : CollatzResearch.WordTrace tailWord_7407588 prefixEnd_7407588 3803653134477469011583129 := by
  unfold tailWord_7407588
  simp only [CollatzResearch.WordTrace]
  refine ⟨135088465143790633077267709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180117953525054177436356945 135088465143790633077267709)
  ·
    refine ⟨50658174428921487403975391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135088465143790633077267709 50658174428921487403975391)
    ·
      refine ⟨75987261643382231105963087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50658174428921487403975391 75987261643382231105963087)
      ·
        refine ⟨113980892465073346658944631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75987261643382231105963087 113980892465073346658944631)
        ·
          refine ⟨170971338697610019988416947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113980892465073346658944631 170971338697610019988416947)
          ·
            refine ⟨256457008046415029982625421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170971338697610019988416947 256457008046415029982625421)
            ·
              refine ⟨96171378017405636243484533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256457008046415029982625421 96171378017405636243484533)
              ·
                refine ⟨9016066689131778397826675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96171378017405636243484533 9016066689131778397826675)
                ·
                  refine ⟨13524100033697667596740013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016066689131778397826675 13524100033697667596740013)
                  ·
                    refine ⟨5071537512636625348777505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13524100033697667596740013 5071537512636625348777505)
                    ·
                      refine ⟨3803653134477469011583129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071537512636625348777505 3803653134477469011583129)
                      ·
                        rfl

theorem cell23_7407588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_7407588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407588 prefixEnd_7407588 := by exact prefixLift 7407588
  have htrace : WordTrace (prefixWord ++ tailWord_7407588) baseStart_7407588 baseEnd_7407588 := by
    simpa [prefixWord, tailWord_7407588, baseEnd_7407588] using wordTrace_append hprefix tailTrace_7407588
  have hstable : (prefixWord ++ tailWord_7407588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407588).length < 2 ^ (prefixWord ++ tailWord_7407588).sum := by decide
  have hdescent : baseEnd_7407588 < baseStart_7407588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407624 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 9]
def baseStart_7407624 : Nat := 118140960795 + 7407624 * 2 ^ 59
def prefixEnd_7407624 : Nat := 4983230072969 + 3 ^ 40 * 7407624 * 2
def baseEnd_7407624 : Nat := 422630179975670096748107

theorem tailTrace_7407624 : CollatzResearch.WordTrace tailWord_7407624 prefixEnd_7407624 422630179975670096748107 := by
  unfold tailWord_7407624
  simp only [CollatzResearch.WordTrace]
  refine ⟨135089121657725422151422963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180118828876967229535230617 135089121657725422151422963)
  ·
    refine ⟨202633682486588133227134445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135089121657725422151422963 202633682486588133227134445)
    ·
      refine ⟨75987630932470549960175417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202633682486588133227134445 75987630932470549960175417)
      ·
        refine ⟨56990723199352912470131563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75987630932470549960175417 56990723199352912470131563)
        ·
          refine ⟨85486084799029368705197345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56990723199352912470131563 85486084799029368705197345)
          ·
            refine ⟨64114563599272026528898009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85486084799029368705197345 64114563599272026528898009)
            ·
              refine ⟨48085922699454019896673507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64114563599272026528898009 48085922699454019896673507)
              ·
                refine ⟨72128884049181029845010261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48085922699454019896673507 72128884049181029845010261)
                ·
                  refine ⟨422630179975670096748107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72128884049181029845010261 422630179975670096748107)
                  ·
                    rfl

theorem cell23_7407624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 9].length) (baseStart_7407624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407624 prefixEnd_7407624 := by exact prefixLift 7407624
  have htrace : WordTrace (prefixWord ++ tailWord_7407624) baseStart_7407624 baseEnd_7407624 := by
    simpa [prefixWord, tailWord_7407624, baseEnd_7407624] using wordTrace_append hprefix tailTrace_7407624
  have hstable : (prefixWord ++ tailWord_7407624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407624).length < 2 ^ (prefixWord ++ tailWord_7407624).sum := by decide
  have hdescent : baseEnd_7407624 < baseStart_7407624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407641 : List Nat := [1, 2, 1, 2, 1, 1, 3, 7, 5]
def baseStart_7407641 : Nat := 118140960795 + 7407641 * 2 ^ 59
def prefixEnd_7407641 : Nat := 4983230072969 + 3 ^ 40 * 7407641 * 2
def baseEnd_7407641 : Nat := 422631149883573033802265

theorem tailTrace_7407641 : CollatzResearch.WordTrace tailWord_7407641 prefixEnd_7407641 422631149883573033802265 := by
  unfold tailWord_7407641
  simp only [CollatzResearch.WordTrace]
  refine ⟨270178863356389256206214777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180119242237592837470809851 270178863356389256206214777)
  ·
    refine ⟨202634147517291942154661083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270178863356389256206214777 202634147517291942154661083)
    ·
      refine ⟨303951221275937913231991625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202634147517291942154661083 303951221275937913231991625)
      ·
        refine ⟨227963415956953434923993719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303951221275937913231991625 227963415956953434923993719)
        ·
          refine ⟨341945123935430152385990579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227963415956953434923993719 341945123935430152385990579)
          ·
            refine ⟨512917685903145228578985869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341945123935430152385990579 512917685903145228578985869)
            ·
              refine ⟨192344132213679460717119701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512917685903145228578985869 192344132213679460717119701)
              ·
                refine ⟨4508065598758112360557493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192344132213679460717119701 4508065598758112360557493)
                ·
                  refine ⟨422631149883573033802265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4508065598758112360557493 422631149883573033802265)
                  ·
                    rfl

theorem cell23_7407641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 5].length) (baseStart_7407641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407641 prefixEnd_7407641 := by exact prefixLift 7407641
  have htrace : WordTrace (prefixWord ++ tailWord_7407641) baseStart_7407641 baseEnd_7407641 := by
    simpa [prefixWord, tailWord_7407641, baseEnd_7407641] using wordTrace_append hprefix tailTrace_7407641
  have hstable : (prefixWord ++ tailWord_7407641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407641).length < 2 ^ (prefixWord ++ tailWord_7407641).sum := by decide
  have hdescent : baseEnd_7407641 < baseStart_7407641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407651 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 3]
def baseStart_7407651 : Nat := 118140960795 + 7407651 * 2 ^ 59
def prefixEnd_7407651 : Nat := 4983230072969 + 3 ^ 40 * 7407651 * 2
def baseEnd_7407651 : Nat := 3803685483758702265095339

theorem tailTrace_7407651 : CollatzResearch.WordTrace tailWord_7407651 prefixEnd_7407651 3803685483758702265095339 := by
  unfold tailWord_7407651
  simp only [CollatzResearch.WordTrace]
  refine ⟨270179228086353027914078807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180119485390902018609385871 270179228086353027914078807)
  ·
    refine ⟨405268842129529541871118211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270179228086353027914078807 405268842129529541871118211)
    ·
      refine ⟨607903263194294312806677317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405268842129529541871118211 607903263194294312806677317)
      ·
        refine ⟨113981861848930183651251997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 607903263194294312806677317 113981861848930183651251997)
        ·
          refine ⟨42743198193348818869219499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113981861848930183651251997 42743198193348818869219499)
          ·
            refine ⟨64114797290023228303829249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42743198193348818869219499 64114797290023228303829249)
            ·
              refine ⟨48086097967517421227871937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64114797290023228303829249 48086097967517421227871937)
              ·
                refine ⟨36064573475638065920903953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48086097967517421227871937 36064573475638065920903953)
                ·
                  refine ⟨27048430106728549440677965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36064573475638065920903953 27048430106728549440677965)
                  ·
                    refine ⟨10143161290023206040254237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27048430106728549440677965 10143161290023206040254237)
                    ·
                      refine ⟨3803685483758702265095339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10143161290023206040254237 3803685483758702265095339)
                      ·
                        rfl

theorem cell23_7407651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_7407651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407651 prefixEnd_7407651 := by exact prefixLift 7407651
  have htrace : WordTrace (prefixWord ++ tailWord_7407651) baseStart_7407651 baseEnd_7407651 := by
    simpa [prefixWord, tailWord_7407651, baseEnd_7407651] using wordTrace_append hprefix tailTrace_7407651
  have hstable : (prefixWord ++ tailWord_7407651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407651).length < 2 ^ (prefixWord ++ tailWord_7407651).sum := by decide
  have hdescent : baseEnd_7407651 < baseStart_7407651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407752 : List Nat := [2, 1, 3, 4, 1, 1, 3, 3, 1, 4]
def baseStart_7407752 : Nat := 118140960795 + 7407752 * 2 ^ 59
def prefixEnd_7407752 : Nat := 4983230072969 + 3 ^ 40 * 7407752 * 2
def baseEnd_7407752 : Nat := 1267912448434935456644125

theorem tailTrace_7407752 : CollatzResearch.WordTrace tailWord_7407752 prefixEnd_7407752 1267912448434935456644125 := by
  unfold tailWord_7407752
  simp only [CollatzResearch.WordTrace]
  refine ⟨135091455929493561081752755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180121941239324748109003673 135091455929493561081752755)
  ·
    refine ⟨202637183894240341622629133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135091455929493561081752755 202637183894240341622629133)
    ·
      refine ⟨75988943960340128108485925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202637183894240341622629133 75988943960340128108485925)
      ·
        refine ⟨14247926992563774020341111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75988943960340128108485925 14247926992563774020341111)
        ·
          refine ⟨21371890488845661030511667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14247926992563774020341111 21371890488845661030511667)
          ·
            refine ⟨32057835733268491545767501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21371890488845661030511667 32057835733268491545767501)
            ·
              refine ⟨12021688399975684329662813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32057835733268491545767501 12021688399975684329662813)
              ·
                refine ⟨4508133149990881623623555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12021688399975684329662813 4508133149990881623623555)
                ·
                  refine ⟨6762199724986322435435333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508133149990881623623555 6762199724986322435435333)
                  ·
                    refine ⟨1267912448434935456644125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762199724986322435435333 1267912448434935456644125)
                    ·
                      rfl

theorem cell23_7407752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_7407752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407752 prefixEnd_7407752 := by exact prefixLift 7407752
  have htrace : WordTrace (prefixWord ++ tailWord_7407752) baseStart_7407752 baseEnd_7407752 := by
    simpa [prefixWord, tailWord_7407752, baseEnd_7407752] using wordTrace_append hprefix tailTrace_7407752
  have hstable : (prefixWord ++ tailWord_7407752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407752).length < 2 ^ (prefixWord ++ tailWord_7407752).sum := by decide
  have hdescent : baseEnd_7407752 < baseStart_7407752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407791 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 1, 6]
def baseStart_7407791 : Nat := 118140960795 + 7407791 * 2 ^ 59
def prefixEnd_7407791 : Nat := 4983230072969 + 3 ^ 40 * 7407791 * 2
def baseEnd_7407791 : Nat := 1267919123683443905781565

theorem tailTrace_7407791 : CollatzResearch.WordTrace tailWord_7407791 prefixEnd_7407791 1267919123683443905781565 := by
  unfold tailWord_7407791
  simp only [CollatzResearch.WordTrace]
  refine ⟨270184334305845831824175227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180122889537230554549450151 270184334305845831824175227)
  ·
    refine ⟨405276501458768747736262841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270184334305845831824175227 405276501458768747736262841)
    ·
      refine ⟨303957376094076560802197131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405276501458768747736262841 303957376094076560802197131)
      ·
        refine ⟨455936064141114841203295697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303957376094076560802197131 455936064141114841203295697)
        ·
          refine ⟨341952048105836130902471773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455936064141114841203295697 341952048105836130902471773)
          ·
            refine ⟨128232018039688549088426915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341952048105836130902471773 128232018039688549088426915)
            ·
              refine ⟨192348027059532823632640373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128232018039688549088426915 192348027059532823632640373)
              ·
                refine ⟨18032627536831202215560035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192348027059532823632640373 18032627536831202215560035)
                ·
                  refine ⟨27048941305246803323340053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18032627536831202215560035 27048941305246803323340053)
                  ·
                    refine ⟨1267919123683443905781565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27048941305246803323340053 1267919123683443905781565)
                    ·
                      rfl

theorem cell23_7407791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_7407791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407791 prefixEnd_7407791 := by exact prefixLift 7407791
  have htrace : WordTrace (prefixWord ++ tailWord_7407791) baseStart_7407791 baseEnd_7407791 := by
    simpa [prefixWord, tailWord_7407791, baseEnd_7407791] using wordTrace_append hprefix tailTrace_7407791
  have hstable : (prefixWord ++ tailWord_7407791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407791).length < 2 ^ (prefixWord ++ tailWord_7407791).sum := by decide
  have hdescent : baseEnd_7407791 < baseStart_7407791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407796 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7407796 : Nat := 118140960795 + 7407796 * 2 ^ 59
def prefixEnd_7407796 : Nat := 4983230072969 + 3 ^ 40 * 7407796 * 2
def baseEnd_7407796 : Nat := 3803759938453604197782173

theorem tailTrace_7407796 : CollatzResearch.WordTrace tailWord_7407796 prefixEnd_7407796 3803759938453604197782173 := by
  unfold tailWord_7407796
  simp only [CollatzResearch.WordTrace]
  refine ⟨135092258335413858839053621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180123011113885145118738161 135092258335413858839053621)
  ·
    refine ⟨12664899218945049266161277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135092258335413858839053621 12664899218945049266161277)
    ·
      refine ⟨4749337207104393474810479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12664899218945049266161277 4749337207104393474810479)
      ·
        refine ⟨7124005810656590212215719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749337207104393474810479 7124005810656590212215719)
        ·
          refine ⟨10686008715984885318323579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7124005810656590212215719 10686008715984885318323579)
          ·
            refine ⟨16029013073977327977485369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10686008715984885318323579 16029013073977327977485369)
            ·
              refine ⟨12021759805482995983114027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16029013073977327977485369 12021759805482995983114027)
              ·
                refine ⟨18032639708224493974671041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12021759805482995983114027 18032639708224493974671041)
                ·
                  refine ⟨13524479781168370481003281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18032639708224493974671041 13524479781168370481003281)
                  ·
                    refine ⟨10143359835876277860752461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13524479781168370481003281 10143359835876277860752461)
                    ·
                      refine ⟨3803759938453604197782173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10143359835876277860752461 3803759938453604197782173)
                      ·
                        rfl

theorem cell23_7407796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7407796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407796 prefixEnd_7407796 := by exact prefixLift 7407796
  have htrace : WordTrace (prefixWord ++ tailWord_7407796) baseStart_7407796 baseEnd_7407796 := by
    simpa [prefixWord, tailWord_7407796, baseEnd_7407796] using wordTrace_append hprefix tailTrace_7407796
  have hstable : (prefixWord ++ tailWord_7407796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407796).length < 2 ^ (prefixWord ++ tailWord_7407796).sum := by decide
  have hdescent : baseEnd_7407796 < baseStart_7407796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407808 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 1, 6]
def baseStart_7407808 : Nat := 118140960795 + 7407808 * 2 ^ 59
def prefixEnd_7407808 : Nat := 4983230072969 + 3 ^ 40 * 7407808 * 2
def baseEnd_7407808 : Nat := 1267922033407152716944039

theorem tailTrace_7407808 : CollatzResearch.WordTrace tailWord_7407808 prefixEnd_7407808 1267922033407152716944039 := by
  unfold tailWord_7407808
  simp only [CollatzResearch.WordTrace]
  refine ⟨135092477173392121863772039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180123302897856162485029385 135092477173392121863772039)
  ·
    refine ⟨202638715760088182795658059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135092477173392121863772039 202638715760088182795658059)
    ·
      refine ⟨303958073640132274193487089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202638715760088182795658059 303958073640132274193487089)
      ·
        refine ⟨227968555230099205645115317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303958073640132274193487089 227968555230099205645115317)
        ·
          refine ⟨21372052052821800529229561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227968555230099205645115317 21372052052821800529229561)
          ·
            refine ⟨16029039039616350396922171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21372052052821800529229561 16029039039616350396922171)
            ·
              refine ⟨24043558559424525595383257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16029039039616350396922171 24043558559424525595383257)
              ·
                refine ⟨18032668919568394196537443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24043558559424525595383257 18032668919568394196537443)
                ·
                  refine ⟨27049003379352591294806165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18032668919568394196537443 27049003379352591294806165)
                  ·
                    refine ⟨1267922033407152716944039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27049003379352591294806165 1267922033407152716944039)
                    ·
                      rfl

theorem cell23_7407808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_7407808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407808 prefixEnd_7407808 := by exact prefixLift 7407808
  have htrace : WordTrace (prefixWord ++ tailWord_7407808) baseStart_7407808 baseEnd_7407808 := by
    simpa [prefixWord, tailWord_7407808, baseEnd_7407808] using wordTrace_append hprefix tailTrace_7407808
  have hstable : (prefixWord ++ tailWord_7407808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407808).length < 2 ^ (prefixWord ++ tailWord_7407808).sum := by decide
  have hdescent : baseEnd_7407808 < baseStart_7407808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407812 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_7407812 : Nat := 118140960795 + 7407812 * 2 ^ 59
def prefixEnd_7407812 : Nat := 4983230072969 + 3 ^ 40 * 7407812 * 2
def baseEnd_7407812 : Nat := 1267922718048025378394033

theorem tailTrace_7407812 : CollatzResearch.WordTrace tailWord_7407812 prefixEnd_7407812 1267922718048025378394033 := by
  unfold tailWord_7407812
  simp only [CollatzResearch.WordTrace]
  refine ⟨135092550119384876205344845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180123400159179834940459793 135092550119384876205344845)
  ·
    refine ⟨50659706294769328577004317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135092550119384876205344845 50659706294769328577004317)
    ·
      refine ⟨18997389860538498216376619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50659706294769328577004317 18997389860538498216376619)
      ·
        refine ⟨28496084790807747324564929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18997389860538498216376619 28496084790807747324564929)
        ·
          refine ⟨21372063593105810493423697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28496084790807747324564929 21372063593105810493423697)
          ·
            refine ⟨16029047694829357870067773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21372063593105810493423697 16029047694829357870067773)
            ·
              refine ⟨6010892885561009201275415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16029047694829357870067773 6010892885561009201275415)
              ·
                refine ⟨9016339328341513801913123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6010892885561009201275415 9016339328341513801913123)
                ·
                  refine ⟨13524508992512270702869685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016339328341513801913123 13524508992512270702869685)
                  ·
                    refine ⟨1267922718048025378394033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13524508992512270702869685 1267922718048025378394033)
                    ·
                      rfl

theorem cell23_7407812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_7407812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407812 prefixEnd_7407812 := by exact prefixLift 7407812
  have htrace : WordTrace (prefixWord ++ tailWord_7407812) baseStart_7407812 baseEnd_7407812 := by
    simpa [prefixWord, tailWord_7407812, baseEnd_7407812] using wordTrace_append hprefix tailTrace_7407812
  have hstable : (prefixWord ++ tailWord_7407812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407812).length < 2 ^ (prefixWord ++ tailWord_7407812).sum := by decide
  have hdescent : baseEnd_7407812 < baseStart_7407812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407826 : List Nat := [3, 2, 2, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_7407826 : Nat := 118140960795 + 7407826 * 2 ^ 59
def prefixEnd_7407826 : Nat := 4983230072969 + 3 ^ 40 * 7407826 * 2
def baseEnd_7407826 : Nat := 3803775342873239080407035

theorem tailTrace_7407826 : CollatzResearch.WordTrace tailWord_7407826 prefixEnd_7407826 3803775342873239080407035 := by
  unfold tailWord_7407826
  simp only [CollatzResearch.WordTrace]
  refine ⟨67546402715179758200424833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180123740573812688534466221 67546402715179758200424833)
  ·
    refine ⟨50659802036384818650318625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67546402715179758200424833 50659802036384818650318625)
    ·
      refine ⟨37994851527288613987738969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50659802036384818650318625 37994851527288613987738969)
      ·
        refine ⟨28496138645466460490804227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37994851527288613987738969 28496138645466460490804227)
        ·
          refine ⟨42744207968199690736206341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28496138645466460490804227 42744207968199690736206341)
          ·
            refine ⟨8014538994037442013038689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42744207968199690736206341 8014538994037442013038689)
            ·
              refine ⟨6010904245528081509779017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8014538994037442013038689 6010904245528081509779017)
              ·
                refine ⟨4508178184146061132334263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010904245528081509779017 4508178184146061132334263)
                ·
                  refine ⟨6762267276219091698501395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508178184146061132334263 6762267276219091698501395)
                  ·
                    refine ⟨10143400914328637547752093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762267276219091698501395 10143400914328637547752093)
                    ·
                      refine ⟨3803775342873239080407035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10143400914328637547752093 3803775342873239080407035)
                      ·
                        rfl

theorem cell23_7407826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_7407826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407826 prefixEnd_7407826 := by exact prefixLift 7407826
  have htrace : WordTrace (prefixWord ++ tailWord_7407826) baseStart_7407826 baseEnd_7407826 := by
    simpa [prefixWord, tailWord_7407826, baseEnd_7407826] using wordTrace_append hprefix tailTrace_7407826
  have hstable : (prefixWord ++ tailWord_7407826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407826).length < 2 ^ (prefixWord ++ tailWord_7407826).sum := by decide
  have hdescent : baseEnd_7407826 < baseStart_7407826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407845 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_7407845 : Nat := 118140960795 + 7407845 * 2 ^ 59
def prefixEnd_7407845 : Nat := 4983230072969 + 3 ^ 40 * 7407845 * 2
def baseEnd_7407845 : Nat := 3803785099005674506069447

theorem tailTrace_7407845 : CollatzResearch.WordTrace tailWord_7407845 prefixEnd_7407845 3803785099005674506069447 := by
  unfold tailWord_7407845
  simp only [CollatzResearch.WordTrace]
  refine ⟨270186303847650199046640989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180124202565100132697760659 270186303847650199046640989)
  ·
    refine ⟨101319863942868824642490371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270186303847650199046640989 101319863942868824642490371)
    ·
      refine ⟨151979795914303236963735557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101319863942868824642490371 151979795914303236963735557)
      ·
        refine ⟨28496211733931856930700417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151979795914303236963735557 28496211733931856930700417)
        ·
          refine ⟨21372158800448892698025313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28496211733931856930700417 21372158800448892698025313)
          ·
            refine ⟨16029119100336669523518985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21372158800448892698025313 16029119100336669523518985)
            ·
              refine ⟨12021839325252502142639239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16029119100336669523518985 12021839325252502142639239)
              ·
                refine ⟨18032758987878753213958859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12021839325252502142639239 18032758987878753213958859)
                ·
                  refine ⟨27049138481818129820938289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18032758987878753213958859 27049138481818129820938289)
                  ·
                    refine ⟨20286853861363597365703717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27049138481818129820938289 20286853861363597365703717)
                    ·
                      refine ⟨3803785099005674506069447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20286853861363597365703717 3803785099005674506069447)
                      ·
                        rfl

theorem cell23_7407845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_7407845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407845 prefixEnd_7407845 := by exact prefixLift 7407845
  have htrace : WordTrace (prefixWord ++ tailWord_7407845) baseStart_7407845 baseEnd_7407845 := by
    simpa [prefixWord, tailWord_7407845, baseEnd_7407845] using wordTrace_append hprefix tailTrace_7407845
  have hstable : (prefixWord ++ tailWord_7407845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407845).length < 2 ^ (prefixWord ++ tailWord_7407845).sum := by decide
  have hdescent : baseEnd_7407845 < baseStart_7407845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407851 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 2, 7]
def baseStart_7407851 : Nat := 118140960795 + 7407851 * 2 ^ 59
def prefixEnd_7407851 : Nat := 4983230072969 + 3 ^ 40 * 7407851 * 2
def baseEnd_7407851 : Nat := 1267929393296533827531473

theorem tailTrace_7407851 : CollatzResearch.WordTrace tailWord_7407851 prefixEnd_7407851 1267929393296533827531473 := by
  unfold tailWord_7407851
  simp only [CollatzResearch.WordTrace]
  refine ⟨270186522685628462071359407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180124348457085641380906271 270186522685628462071359407)
  ·
    refine ⟨405279784028442693107039111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270186522685628462071359407 405279784028442693107039111)
    ·
      refine ⟨607919676042664039660558667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405279784028442693107039111 607919676042664039660558667)
      ·
        refine ⟨911879514063996059490838001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607919676042664039660558667 911879514063996059490838001)
        ·
          refine ⟨683909635547997044618128501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911879514063996059490838001 683909635547997044618128501)
          ·
            refine ⟨64116528332624722932949547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 683909635547997044618128501 64116528332624722932949547)
            ·
              refine ⟨96174792498937084399424321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64116528332624722932949547 96174792498937084399424321)
              ·
                refine ⟨72131094374202813299568241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96174792498937084399424321 72131094374202813299568241)
                ·
                  refine ⟨54098320780652109974676181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72131094374202813299568241 54098320780652109974676181)
                  ·
                    refine ⟨1267929393296533827531473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54098320780652109974676181 1267929393296533827531473)
                    ·
                      rfl

theorem cell23_7407851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 7].length) (baseStart_7407851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407851 prefixEnd_7407851 := by exact prefixLift 7407851
  have htrace : WordTrace (prefixWord ++ tailWord_7407851) baseStart_7407851 baseEnd_7407851 := by
    simpa [prefixWord, tailWord_7407851, baseEnd_7407851] using wordTrace_append hprefix tailTrace_7407851
  have hstable : (prefixWord ++ tailWord_7407851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407851).length < 2 ^ (prefixWord ++ tailWord_7407851).sum := by decide
  have hdescent : baseEnd_7407851 < baseStart_7407851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407882 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_7407882 : Nat := 118140960795 + 7407882 * 2 ^ 59
def prefixEnd_7407882 : Nat := 4983230072969 + 3 ^ 40 * 7407882 * 2
def baseEnd_7407882 : Nat := 3803804097789890861306777

theorem tailTrace_7407882 : CollatzResearch.WordTrace tailWord_7407882 prefixEnd_7407882 3803804097789890861306777 := by
  unfold tailWord_7407882
  simp only [CollatzResearch.WordTrace]
  refine ⟨67546913337129038591434475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180125102232344102910491933 67546913337129038591434475)
  ·
    refine ⟨101320370005693557887151713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67546913337129038591434475 101320370005693557887151713)
    ·
      refine ⟨75990277504270168415363785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101320370005693557887151713 75990277504270168415363785)
      ·
        refine ⟨56992708128202626311522839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75990277504270168415363785 56992708128202626311522839)
        ·
          refine ⟨85489062192303939467284259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56992708128202626311522839 85489062192303939467284259)
          ·
            refine ⟨128233593288455909200926389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85489062192303939467284259 128233593288455909200926389)
            ·
              refine ⟨12021899370792741487586849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128233593288455909200926389 12021899370792741487586849)
              ·
                refine ⟨9016424528094556115690137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12021899370792741487586849 9016424528094556115690137)
                ·
                  refine ⟨6762318396070917086767603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9016424528094556115690137 6762318396070917086767603)
                  ·
                    refine ⟨10143477594106375630151405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762318396070917086767603 10143477594106375630151405)
                    ·
                      refine ⟨3803804097789890861306777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10143477594106375630151405 3803804097789890861306777)
                      ·
                        rfl

theorem cell23_7407882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_7407882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407882 prefixEnd_7407882 := by exact prefixLift 7407882
  have htrace : WordTrace (prefixWord ++ tailWord_7407882) baseStart_7407882 baseEnd_7407882 := by
    simpa [prefixWord, tailWord_7407882, baseEnd_7407882] using wordTrace_append hprefix tailTrace_7407882
  have hstable : (prefixWord ++ tailWord_7407882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407882).length < 2 ^ (prefixWord ++ tailWord_7407882).sum := by decide
  have hdescent : baseEnd_7407882 < baseStart_7407882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407909 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 1, 3, 2]
def baseStart_7407909 : Nat := 118140960795 + 7407909 * 2 ^ 59
def prefixEnd_7407909 : Nat := 4983230072969 + 3 ^ 40 * 7407909 * 2
def baseEnd_7407909 : Nat := 3803817961767562255669153

theorem tailTrace_7407909 : CollatzResearch.WordTrace tailWord_7407909 prefixEnd_7407909 3803817961767562255669153 := by
  unfold tailWord_7407909
  simp only [CollatzResearch.WordTrace]
  refine ⟨270188638119418337976970781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180125758746278891984647187 270188638119418337976970781)
  ·
    refine ⟨101320739294781876741364043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270188638119418337976970781 101320739294781876741364043)
    ·
      refine ⟨151981108942172815112046065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101320739294781876741364043 151981108942172815112046065)
      ·
        refine ⟨113985831706629611334034549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151981108942172815112046065 113985831706629611334034549)
        ·
          refine ⟨10686171722496526062565739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113985831706629611334034549 10686171722496526062565739)
          ·
            refine ⟨16029257583744789093848609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10686171722496526062565739 16029257583744789093848609)
            ·
              refine ⟨12021943187808591820386457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16029257583744789093848609 12021943187808591820386457)
              ·
                refine ⟨9016457390856443865289843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12021943187808591820386457 9016457390856443865289843)
                ·
                  refine ⟨13524686086284665797934765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016457390856443865289843 13524686086284665797934765)
                  ·
                    refine ⟨5071757282356749674225537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13524686086284665797934765 5071757282356749674225537)
                    ·
                      refine ⟨3803817961767562255669153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071757282356749674225537 3803817961767562255669153)
                      ·
                        rfl

theorem cell23_7407909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_7407909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407909 prefixEnd_7407909 := by exact prefixLift 7407909
  have htrace : WordTrace (prefixWord ++ tailWord_7407909) baseStart_7407909 baseEnd_7407909 := by
    simpa [prefixWord, tailWord_7407909, baseEnd_7407909] using wordTrace_append hprefix tailTrace_7407909
  have hstable : (prefixWord ++ tailWord_7407909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407909).length < 2 ^ (prefixWord ++ tailWord_7407909).sum := by decide
  have hdescent : baseEnd_7407909 < baseStart_7407909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407956 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_7407956 : Nat := 118140960795 + 7407956 * 2 ^ 59
def prefixEnd_7407956 : Nat := 4983230072969 + 3 ^ 40 * 7407956 * 2
def baseEnd_7407956 : Nat := 3803842095358323571781437

theorem tailTrace_7407956 : CollatzResearch.WordTrace tailWord_7407956 prefixEnd_7407956 3803842095358323571781437 := by
  unfold tailWord_7407956
  simp only [CollatzResearch.WordTrace]
  refine ⟨135095176175124032501965861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180126901566832043335954481 135095176175124032501965861)
  ·
    refine ⟨25330345532835756094118599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135095176175124032501965861 25330345532835756094118599)
    ·
      refine ⟨37995518299253634141177899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25330345532835756094118599 37995518299253634141177899)
      ·
        refine ⟨56993277448880451211766849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37995518299253634141177899 56993277448880451211766849)
        ·
          refine ⟨42744958086660338408825137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56993277448880451211766849 42744958086660338408825137)
          ·
            refine ⟨32058718564995253806618853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42744958086660338408825137 32058718564995253806618853)
            ·
              refine ⟨6011009730936610088741035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32058718564995253806618853 6011009730936610088741035)
              ·
                refine ⟨9016514596404915133111553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011009730936610088741035 9016514596404915133111553)
                ·
                  refine ⟨6762385947303686349833665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9016514596404915133111553 6762385947303686349833665)
                  ·
                    refine ⟨5071789460477764762375249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6762385947303686349833665 5071789460477764762375249)
                    ·
                      refine ⟨3803842095358323571781437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071789460477764762375249 3803842095358323571781437)
                      ·
                        rfl

theorem cell23_7407956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_7407956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407956 prefixEnd_7407956 := by exact prefixLift 7407956
  have htrace : WordTrace (prefixWord ++ tailWord_7407956) baseStart_7407956 baseEnd_7407956 := by
    simpa [prefixWord, tailWord_7407956, baseEnd_7407956] using wordTrace_append hprefix tailTrace_7407956
  have hstable : (prefixWord ++ tailWord_7407956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407956).length < 2 ^ (prefixWord ++ tailWord_7407956).sum := by decide
  have hdescent : baseEnd_7407956 < baseStart_7407956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407975 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 2, 5]
def baseStart_7407975 : Nat := 118140960795 + 7407975 * 2 ^ 59
def prefixEnd_7407975 : Nat := 4983230072969 + 3 ^ 40 * 7407975 * 2
def baseEnd_7407975 : Nat := 1267950617163586332481283

theorem tailTrace_7407975 : CollatzResearch.WordTrace tailWord_7407975 prefixEnd_7407975 1267950617163586332481283 := by
  unfold tailWord_7407975
  simp only [CollatzResearch.WordTrace]
  refine ⟨270191045337179231248873379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180127363558119487499248919 270191045337179231248873379)
  ·
    refine ⟨405286568005768846873310069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270191045337179231248873379 405286568005768846873310069)
    ·
      refine ⟨37995615750540829394372819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 405286568005768846873310069 37995615750540829394372819)
      ·
        refine ⟨56993423625811244091559229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37995615750540829394372819 56993423625811244091559229)
        ·
          refine ⟨21372533859679216534334711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56993423625811244091559229 21372533859679216534334711)
          ·
            refine ⟨32058800789518824801502067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21372533859679216534334711 32058800789518824801502067)
            ·
              refine ⟨48088201184278237202253101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32058800789518824801502067 48088201184278237202253101)
              ·
                refine ⟨18033075444104338950844913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48088201184278237202253101 18033075444104338950844913)
                ·
                  refine ⟨13524806583078254213133685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18033075444104338950844913 13524806583078254213133685)
                  ·
                    refine ⟨1267950617163586332481283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13524806583078254213133685 1267950617163586332481283)
                    ·
                      rfl

theorem cell23_7407975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_7407975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407975 prefixEnd_7407975 := by exact prefixLift 7407975
  have htrace : WordTrace (prefixWord ++ tailWord_7407975) baseStart_7407975 baseEnd_7407975 := by
    simpa [prefixWord, tailWord_7407975, baseEnd_7407975] using wordTrace_append hprefix tailTrace_7407975
  have hstable : (prefixWord ++ tailWord_7407975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407975).length < 2 ^ (prefixWord ++ tailWord_7407975).sum := by decide
  have hdescent : baseEnd_7407975 < baseStart_7407975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7407995 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 4]
def baseStart_7407995 : Nat := 118140960795 + 7407995 * 2 ^ 59
def prefixEnd_7407995 : Nat := 4983230072969 + 3 ^ 40 * 7407995 * 2
def baseEnd_7407995 : Nat := 3803862121103848919193757

theorem tailTrace_7407995 : CollatzResearch.WordTrace tailWord_7407995 prefixEnd_7407995 3803862121103848919193757 := by
  unfold tailWord_7407995
  simp only [CollatzResearch.WordTrace]
  refine ⟨270191774797106774664601439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180127849864737849776400959 270191774797106774664601439)
  ·
    refine ⟨405287662195660161996902159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270191774797106774664601439 405287662195660161996902159)
    ·
      refine ⟨607931493293490242995353239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405287662195660161996902159 607931493293490242995353239)
      ·
        refine ⟨911897239940235364493029859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607931493293490242995353239 911897239940235364493029859)
        ·
          refine ⟨1367845859910353046739544789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911897239940235364493029859 1367845859910353046739544789)
          ·
            refine ⟨32058887341648899532958081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1367845859910353046739544789 32058887341648899532958081)
            ·
              refine ⟨24044165506236674649718561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32058887341648899532958081 24044165506236674649718561)
              ·
                refine ⟨18033124129677505987288921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24044165506236674649718561 18033124129677505987288921)
                ·
                  refine ⟨13524843097258129490466691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18033124129677505987288921 13524843097258129490466691)
                  ·
                    refine ⟨20287264645887194235700037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13524843097258129490466691 20287264645887194235700037)
                    ·
                      refine ⟨3803862121103848919193757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20287264645887194235700037 3803862121103848919193757)
                      ·
                        rfl

theorem cell23_7407995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 4].length) (baseStart_7407995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7407995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7407995 prefixEnd_7407995 := by exact prefixLift 7407995
  have htrace : WordTrace (prefixWord ++ tailWord_7407995) baseStart_7407995 baseEnd_7407995 := by
    simpa [prefixWord, tailWord_7407995, baseEnd_7407995] using wordTrace_append hprefix tailTrace_7407995
  have hstable : (prefixWord ++ tailWord_7407995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7407995).length < 2 ^ (prefixWord ++ tailWord_7407995).sum := by decide
  have hdescent : baseEnd_7407995 < baseStart_7407995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7407995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408005 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_7408005 : Nat := 118140960795 + 7408005 * 2 ^ 59
def prefixEnd_7408005 : Nat := 4983230072969 + 3 ^ 40 * 7408005 * 2
def baseEnd_7408005 : Nat := 1267955751970131293356237

theorem tailTrace_7408005 : CollatzResearch.WordTrace tailWord_7408005 prefixEnd_7408005 1267955751970131293356237 := by
  unfold tailWord_7408005
  simp only [CollatzResearch.WordTrace]
  refine ⟨270192139527070546372465469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180128093018047030914976979 270192139527070546372465469)
  ·
    refine ⟨101322052322651454889674551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270192139527070546372465469 101322052322651454889674551)
    ·
      refine ⟨151983078483977182334511827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101322052322651454889674551 151983078483977182334511827)
      ·
        refine ⟨227974617725965773501767741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151983078483977182334511827 227974617725965773501767741)
        ·
          refine ⟨85490481647237165063162903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227974617725965773501767741 85490481647237165063162903)
          ·
            refine ⟨128235722470855747594744355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85490481647237165063162903 128235722470855747594744355)
            ·
              refine ⟨192353583706283621392116533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128235722470855747594744355 192353583706283621392116533)
              ·
                refine ⟨18033148472464089505510925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192353583706283621392116533 18033148472464089505510925)
                ·
                  refine ⟨6762430677174033564566597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18033148472464089505510925 6762430677174033564566597)
                  ·
                    refine ⟨1267955751970131293356237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762430677174033564566597 1267955751970131293356237)
                    ·
                      rfl

theorem cell23_7408005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_7408005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408005 prefixEnd_7408005 := by exact prefixLift 7408005
  have htrace : WordTrace (prefixWord ++ tailWord_7408005) baseStart_7408005 baseEnd_7408005 := by
    simpa [prefixWord, tailWord_7408005, baseEnd_7408005] using wordTrace_append hprefix tailTrace_7408005
  have hstable : (prefixWord ++ tailWord_7408005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408005).length < 2 ^ (prefixWord ++ tailWord_7408005).sum := by decide
  have hdescent : baseEnd_7408005 < baseStart_7408005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408012 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 2, 4, 2]
def baseStart_7408012 : Nat := 118140960795 + 7408012 * 2 ^ 59
def prefixEnd_7408012 : Nat := 4983230072969 + 3 ^ 40 * 7408012 * 2
def baseEnd_7408012 : Nat := 3803870850274975352681179

theorem tailTrace_7408012 : CollatzResearch.WordTrace tailWord_7408012 prefixEnd_7408012 3803870850274975352681179 := by
  unfold tailWord_7408012
  simp only [CollatzResearch.WordTrace]
  refine ⟨135096197419022593283985145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180128263225363457711980193 135096197419022593283985145)
  ·
    refine ⟨101322148064266944962988859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135096197419022593283985145 101322148064266944962988859)
    ·
      refine ⟨151983222096400417444483289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101322148064266944962988859 151983222096400417444483289)
      ·
        refine ⟨113987416572300313083362467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151983222096400417444483289 113987416572300313083362467)
        ·
          refine ⟨170981124858450469625043701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113987416572300313083362467 170981124858450469625043701)
          ·
            refine ⟨16029480455479731527347847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170981124858450469625043701 16029480455479731527347847)
            ·
              refine ⟨24044220683219597291021771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16029480455479731527347847 24044220683219597291021771)
              ·
                refine ⟨36066331024829395936532657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24044220683219597291021771 36066331024829395936532657)
                ·
                  refine ⟨27049748268622046952399493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36066331024829395936532657 27049748268622046952399493)
                  ·
                    refine ⟨5071827800366633803574905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27049748268622046952399493 5071827800366633803574905)
                    ·
                      refine ⟨3803870850274975352681179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071827800366633803574905 3803870850274975352681179)
                      ·
                        rfl

theorem cell23_7408012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_7408012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408012 prefixEnd_7408012 := by exact prefixLift 7408012
  have htrace : WordTrace (prefixWord ++ tailWord_7408012) baseStart_7408012 baseEnd_7408012 := by
    simpa [prefixWord, tailWord_7408012, baseEnd_7408012] using wordTrace_append hprefix tailTrace_7408012
  have hstable : (prefixWord ++ tailWord_7408012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408012).length < 2 ^ (prefixWord ++ tailWord_7408012).sum := by decide
  have hdescent : baseEnd_7408012 < baseStart_7408012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408029 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_7408029 : Nat := 118140960795 + 7408029 * 2 ^ 59
def prefixEnd_7408029 : Nat := 4983230072969 + 3 ^ 40 * 7408029 * 2
def baseEnd_7408029 : Nat := 3803879579446101786168601

theorem tailTrace_7408029 : CollatzResearch.WordTrace tailWord_7408029 prefixEnd_7408029 3803879579446101786168601 := by
  unfold tailWord_7408029
  simp only [CollatzResearch.WordTrace]
  refine ⟨270193014878983598471339141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180128676585989065647559427 270193014878983598471339141)
  ·
    refine ⟨50661190289809424713376089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270193014878983598471339141 50661190289809424713376089)
    ·
      refine ⟨37995892717357068535032067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50661190289809424713376089 37995892717357068535032067)
      ·
        refine ⟨56993839076035602802548101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37995892717357068535032067 56993839076035602802548101)
        ·
          refine ⟨10686344826756675525477769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56993839076035602802548101 10686344826756675525477769)
          ·
            refine ⟨8014758620067506644108327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10686344826756675525477769 8014758620067506644108327)
            ·
              refine ⟨12022137930101259966162491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8014758620067506644108327 12022137930101259966162491)
              ·
                refine ⟨18033206895151889949243737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12022137930101259966162491 18033206895151889949243737)
                ·
                  refine ⟨13524905171363917461932803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18033206895151889949243737 13524905171363917461932803)
                  ·
                    refine ⟨20287357757045876192899205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13524905171363917461932803 20287357757045876192899205)
                    ·
                      refine ⟨3803879579446101786168601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20287357757045876192899205 3803879579446101786168601)
                      ·
                        rfl

theorem cell23_7408029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_7408029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408029 prefixEnd_7408029 := by exact prefixLift 7408029
  have htrace : WordTrace (prefixWord ++ tailWord_7408029) baseStart_7408029 baseEnd_7408029 := by
    simpa [prefixWord, tailWord_7408029, baseEnd_7408029] using wordTrace_append hprefix tailTrace_7408029
  have hstable : (prefixWord ++ tailWord_7408029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408029).length < 2 ^ (prefixWord ++ tailWord_7408029).sum := by decide
  have hdescent : baseEnd_7408029 < baseStart_7408029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408032 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 3]
def baseStart_7408032 : Nat := 118140960795 + 7408032 * 2 ^ 59
def prefixEnd_7408032 : Nat := 4983230072969 + 3 ^ 40 * 7408032 * 2
def baseEnd_7408032 : Nat := 3803881119888065274431087

theorem tailTrace_7408032 : CollatzResearch.WordTrace tailWord_7408032 prefixEnd_7408032 3803881119888065274431087 := by
  unfold tailWord_7408032
  simp only [CollatzResearch.WordTrace]
  refine ⟨135096562148986364991849175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180128749531981819989132233 135096562148986364991849175)
  ·
    refine ⟨202644843223479547487773763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135096562148986364991849175 202644843223479547487773763)
    ·
      refine ⟨303967264835219321231660645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202644843223479547487773763 303967264835219321231660645)
      ·
        refine ⟨56993862156603622730936371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303967264835219321231660645 56993862156603622730936371)
        ·
          refine ⟨85490793234905434096404557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56993862156603622730936371 85490793234905434096404557)
          ·
            refine ⟨32059047463089537786151709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85490793234905434096404557 32059047463089537786151709)
            ·
              refine ⟨12022142798658576669806891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32059047463089537786151709 12022142798658576669806891)
              ·
                refine ⟨18033214197987865004710337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12022142798658576669806891 18033214197987865004710337)
                ·
                  refine ⟨13524910648490898753532753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18033214197987865004710337 13524910648490898753532753)
                  ·
                    refine ⟨10143682986368174065149565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13524910648490898753532753 10143682986368174065149565)
                    ·
                      refine ⟨3803881119888065274431087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10143682986368174065149565 3803881119888065274431087)
                      ·
                        rfl

theorem cell23_7408032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_7408032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408032 prefixEnd_7408032 := by exact prefixLift 7408032
  have htrace : WordTrace (prefixWord ++ tailWord_7408032) baseStart_7408032 baseEnd_7408032 := by
    simpa [prefixWord, tailWord_7408032, baseEnd_7408032] using wordTrace_append hprefix tailTrace_7408032
  have hstable : (prefixWord ++ tailWord_7408032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408032).length < 2 ^ (prefixWord ++ tailWord_7408032).sum := by decide
  have hdescent : baseEnd_7408032 < baseStart_7408032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408039 : List Nat := [1, 1, 6, 1, 1, 2, 1, 5, 1, 4]
def baseStart_7408039 : Nat := 118140960795 + 7408039 * 2 ^ 59
def prefixEnd_7408039 : Nat := 4983230072969 + 3 ^ 40 * 7408039 * 2
def baseEnd_7408039 : Nat := 1267961571417548915681185

theorem tailTrace_7408039 : CollatzResearch.WordTrace tailWord_7408039 prefixEnd_7408039 1267961571417548915681185 := by
  unfold tailWord_7408039
  simp only [CollatzResearch.WordTrace]
  refine ⟨270193379608947370179203171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180128919739298246786135447 270193379608947370179203171)
  ·
    refine ⟨405290069413421055268804757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270193379608947370179203171 405290069413421055268804757)
    ·
      refine ⟨18997972003754111965725223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 405290069413421055268804757 18997972003754111965725223)
      ·
        refine ⟨28496958005631167948587835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18997972003754111965725223 28496958005631167948587835)
        ·
          refine ⟨42745437008446751922881753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28496958005631167948587835 42745437008446751922881753)
          ·
            refine ⟨32059077756335063942161315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42745437008446751922881753 32059077756335063942161315)
            ·
              refine ⟨48088616634502595913241973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32059077756335063942161315 48088616634502595913241973)
              ·
                refine ⟨4508307809484618366866435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48088616634502595913241973 4508307809484618366866435)
                ·
                  refine ⟨6762461714226927550299653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508307809484618366866435 6762461714226927550299653)
                  ·
                    refine ⟨1267961571417548915681185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762461714226927550299653 1267961571417548915681185)
                    ·
                      rfl

theorem cell23_7408039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_7408039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408039 prefixEnd_7408039 := by exact prefixLift 7408039
  have htrace : WordTrace (prefixWord ++ tailWord_7408039) baseStart_7408039 baseEnd_7408039 := by
    simpa [prefixWord, tailWord_7408039, baseEnd_7408039] using wordTrace_append hprefix tailTrace_7408039
  have hstable : (prefixWord ++ tailWord_7408039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408039).length < 2 ^ (prefixWord ++ tailWord_7408039).sum := by decide
  have hdescent : baseEnd_7408039 < baseStart_7408039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408072 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_7408072 : Nat := 118140960795 + 7408072 * 2 ^ 59
def prefixEnd_7408072 : Nat := 4983230072969 + 3 ^ 40 * 7408072 * 2
def baseEnd_7408072 : Nat := 3803901659114245117930903

theorem tailTrace_7408072 : CollatzResearch.WordTrace tailWord_7408072 prefixEnd_7408072 3803901659114245117930903 := by
  unfold tailWord_7408072
  simp only [CollatzResearch.WordTrace]
  refine ⟨135097291608913908407577235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180129722145218544543436313 135097291608913908407577235)
  ·
    refine ⟨202645937413370862611365853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135097291608913908407577235 202645937413370862611365853)
    ·
      refine ⟨75992226530014073479262195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202645937413370862611365853 75992226530014073479262195)
      ·
        refine ⟨113988339795021110218893293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75992226530014073479262195 113988339795021110218893293)
        ·
          refine ⟨42745627423132916332084985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113988339795021110218893293 42745627423132916332084985)
          ·
            refine ⟨32059220567349687249063739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42745627423132916332084985 32059220567349687249063739)
            ·
              refine ⟨48088830851024530873595609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32059220567349687249063739 48088830851024530873595609)
              ·
                refine ⟨36066623138268398155196707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48088830851024530873595609 36066623138268398155196707)
                ·
                  refine ⟨54099934707402597232795061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36066623138268398155196707 54099934707402597232795061)
                  ·
                    refine ⟨5071868878818993490574537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54099934707402597232795061 5071868878818993490574537)
                    ·
                      refine ⟨3803901659114245117930903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071868878818993490574537 3803901659114245117930903)
                      ·
                        rfl

theorem cell23_7408072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_7408072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408072 prefixEnd_7408072 := by exact prefixLift 7408072
  have htrace : WordTrace (prefixWord ++ tailWord_7408072) baseStart_7408072 baseEnd_7408072 := by
    simpa [prefixWord, tailWord_7408072, baseEnd_7408072] using wordTrace_append hprefix tailTrace_7408072
  have hstable : (prefixWord ++ tailWord_7408072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408072).length < 2 ^ (prefixWord ++ tailWord_7408072).sum := by decide
  have hdescent : baseEnd_7408072 < baseStart_7408072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408112 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 2, 4]
def baseStart_7408112 : Nat := 118140960795 + 7408112 * 2 ^ 59
def prefixEnd_7408112 : Nat := 4983230072969 + 3 ^ 40 * 7408112 * 2
def baseEnd_7408112 : Nat := 1267974066113474987143573

theorem tailTrace_7408112 : CollatzResearch.WordTrace tailWord_7408112 prefixEnd_7408112 1267974066113474987143573 := by
  unfold tailWord_7408112
  simp only [CollatzResearch.WordTrace]
  refine ⟨135098021068841451823305295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180130694758455269097740393 135098021068841451823305295)
  ·
    refine ⟨202647031603262177734957943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135098021068841451823305295 202647031603262177734957943)
    ·
      refine ⟨303970547404893266602436915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202647031603262177734957943 303970547404893266602436915)
      ·
        refine ⟨455955821107339899903655373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303970547404893266602436915 455955821107339899903655373)
        ·
          refine ⟨170983432915252462463870765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455955821107339899903655373 170983432915252462463870765)
          ·
            refine ⟨64118787343219673423951537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170983432915252462463870765 64118787343219673423951537)
            ·
              refine ⟨48089090507414755067963653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64118787343219673423951537 48089090507414755067963653)
              ·
                refine ⟨9016704470140266575243185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48089090507414755067963653 9016704470140266575243185)
                ·
                  refine ⟨6762528352605199931432389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9016704470140266575243185 6762528352605199931432389)
                  ·
                    refine ⟨1267974066113474987143573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762528352605199931432389 1267974066113474987143573)
                    ·
                      rfl

theorem cell23_7408112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 4].length) (baseStart_7408112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408112 prefixEnd_7408112 := by exact prefixLift 7408112
  have htrace : WordTrace (prefixWord ++ tailWord_7408112) baseStart_7408112 baseEnd_7408112 := by
    simpa [prefixWord, tailWord_7408112, baseEnd_7408112] using wordTrace_append hprefix tailTrace_7408112
  have hstable : (prefixWord ++ tailWord_7408112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408112).length < 2 ^ (prefixWord ++ tailWord_7408112).sum := by decide
  have hdescent : baseEnd_7408112 < baseStart_7408112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408125 : List Nat := [1, 4, 1, 1, 1, 3, 4, 8]
def baseStart_7408125 : Nat := 118140960795 + 7408125 * 2 ^ 59
def prefixEnd_7408125 : Nat := 4983230072969 + 3 ^ 40 * 7408125 * 2
def baseEnd_7408125 : Nat := 140886254577367904095117

theorem tailTrace_7408125 : CollatzResearch.WordTrace tailWord_7408125 prefixEnd_7408125 140886254577367904095117 := by
  unfold tailWord_7408125
  simp only [CollatzResearch.WordTrace]
  refine ⟨270196516286635806866833829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180131010857757204577889219 270196516286635806866833829)
  ·
    refine ⟨50661846803744213787531343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270196516286635806866833829 50661846803744213787531343)
    ·
      refine ⟨75992770205616320681297015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50661846803744213787531343 75992770205616320681297015)
      ·
        refine ⟨113989155308424481021945523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75992770205616320681297015 113989155308424481021945523)
        ·
          refine ⟨170983732962636721532918285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113989155308424481021945523 170983732962636721532918285)
          ·
            refine ⟨64118899860988770574844357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170983732962636721532918285 64118899860988770574844357)
            ·
              refine ⟨12022293723935394482783317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64118899860988770574844357 12022293723935394482783317)
              ·
                refine ⟨140886254577367904095117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12022293723935394482783317 140886254577367904095117)
                ·
                  rfl

theorem cell23_7408125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 8].length) (baseStart_7408125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408125 prefixEnd_7408125 := by exact prefixLift 7408125
  have htrace : WordTrace (prefixWord ++ tailWord_7408125) baseStart_7408125 baseEnd_7408125 := by
    simpa [prefixWord, tailWord_7408125, baseEnd_7408125] using wordTrace_append hprefix tailTrace_7408125
  have hstable : (prefixWord ++ tailWord_7408125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408125).length < 2 ^ (prefixWord ++ tailWord_7408125).sum := by decide
  have hdescent : baseEnd_7408125 < baseStart_7408125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408129 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 2, 4]
def baseStart_7408129 : Nat := 118140960795 + 7408129 * 2 ^ 59
def prefixEnd_7408129 : Nat := 4983230072969 + 3 ^ 40 * 7408129 * 2
def baseEnd_7408129 : Nat := 1267976975837183798306047

theorem tailTrace_7408129 : CollatzResearch.WordTrace tailWord_7408129 prefixEnd_7408129 1267976975837183798306047 := by
  unfold tailWord_7408129
  simp only [CollatzResearch.WordTrace]
  refine ⟨270196662178621315549979441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180131108119080877033319627 270196662178621315549979441)
  ·
    refine ⟨202647496633965986662484581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270196662178621315549979441 202647496633965986662484581)
    ·
      refine ⟨37996405618868622499215859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202647496633965986662484581 37996405618868622499215859)
      ·
        refine ⟨56994608428302933748823789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37996405618868622499215859 56994608428302933748823789)
        ·
          refine ⟨21372978160613600155808921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56994608428302933748823789 21372978160613600155808921)
          ·
            refine ⟨16029733620460200116856691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21372978160613600155808921 16029733620460200116856691)
            ·
              refine ⟨24044600430690300175285037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16029733620460200116856691 24044600430690300175285037)
              ·
                refine ⟨9016725161508862565731889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24044600430690300175285037 9016725161508862565731889)
                ·
                  refine ⟨6762543871131646924298917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9016725161508862565731889 6762543871131646924298917)
                  ·
                    refine ⟨1267976975837183798306047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762543871131646924298917 1267976975837183798306047)
                    ·
                      rfl

theorem cell23_7408129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_7408129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408129 prefixEnd_7408129 := by exact prefixLift 7408129
  have htrace : WordTrace (prefixWord ++ tailWord_7408129) baseStart_7408129 baseEnd_7408129 := by
    simpa [prefixWord, tailWord_7408129, baseEnd_7408129] using wordTrace_append hprefix tailTrace_7408129
  have hstable : (prefixWord ++ tailWord_7408129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408129).length < 2 ^ (prefixWord ++ tailWord_7408129).sum := by decide
  have hdescent : baseEnd_7408129 < baseStart_7408129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408132 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_7408132 : Nat := 118140960795 + 7408132 * 2 ^ 59
def prefixEnd_7408132 : Nat := 4983230072969 + 3 ^ 40 * 7408132 * 2
def baseEnd_7408132 : Nat := 3803932467953514883180627

theorem tailTrace_7408132 : CollatzResearch.WordTrace tailWord_7408132 prefixEnd_7408132 3803932467953514883180627 := by
  unfold tailWord_7408132
  simp only [CollatzResearch.WordTrace]
  refine ⟨135098385798805223531169325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180131181065073631374892433 135098385798805223531169325)
  ·
    refine ⟨50661894674551958824188497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135098385798805223531169325 50661894674551958824188497)
    ·
      refine ⟨37996421005913969118141373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50661894674551958824188497 37996421005913969118141373)
      ·
        refine ⟨14248657877217738419303015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37996421005913969118141373 14248657877217738419303015)
        ·
          refine ⟨21372986815826607628954523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14248657877217738419303015 21372986815826607628954523)
          ·
            refine ⟨32059480223739911443431785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21372986815826607628954523 32059480223739911443431785)
            ·
              refine ⟨24044610167804933582573839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32059480223739911443431785 24044610167804933582573839)
              ·
                refine ⟨36066915251707400373860759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24044610167804933582573839 36066915251707400373860759)
                ·
                  refine ⟨54100372877561100560791139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36066915251707400373860759 54100372877561100560791139)
                  ·
                    refine ⟨81150559316341650841186709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54100372877561100560791139 81150559316341650841186709)
                    ·
                      refine ⟨3803932467953514883180627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81150559316341650841186709 3803932467953514883180627)
                      ·
                        rfl

theorem cell23_7408132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_7408132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408132 prefixEnd_7408132 := by exact prefixLift 7408132
  have htrace : WordTrace (prefixWord ++ tailWord_7408132) baseStart_7408132 baseEnd_7408132 := by
    simpa [prefixWord, tailWord_7408132, baseEnd_7408132] using wordTrace_append hprefix tailTrace_7408132
  have hstable : (prefixWord ++ tailWord_7408132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408132).length < 2 ^ (prefixWord ++ tailWord_7408132).sum := by decide
  have hdescent : baseEnd_7408132 < baseStart_7408132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408139 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 3]
def baseStart_7408139 : Nat := 118140960795 + 7408139 * 2 ^ 59
def prefixEnd_7408139 : Nat := 4983230072969 + 3 ^ 40 * 7408139 * 2
def baseEnd_7408139 : Nat := 3803936062318096355793095

theorem tailTrace_7408139 : CollatzResearch.WordTrace tailWord_7408139 prefixEnd_7408139 3803936062318096355793095 := by
  unfold tailWord_7408139
  simp only [CollatzResearch.WordTrace]
  refine ⟨270197026908585087257843471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180131351272390058171895647 270197026908585087257843471)
  ·
    refine ⟨405295540362877630886765207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270197026908585087257843471 405295540362877630886765207)
    ·
      refine ⟨607943310544316446330147811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405295540362877630886765207 607943310544316446330147811)
      ·
        refine ⟨911914965816474669495221717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607943310544316446330147811 911914965816474669495221717)
        ·
          refine ⟨21373007011323625066294259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 911914965816474669495221717 21373007011323625066294259)
          ·
            refine ⟨32059510516985437599441389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21373007011323625066294259 32059510516985437599441389)
            ·
              refine ⟨12022316443869539099790521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32059510516985437599441389 12022316443869539099790521)
              ·
                refine ⟨9016737332902154324842891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12022316443869539099790521 9016737332902154324842891)
                ·
                  refine ⟨13525105999353231487264337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016737332902154324842891 13525105999353231487264337)
                  ·
                    refine ⟨10143829499514923615448253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13525105999353231487264337 10143829499514923615448253)
                    ·
                      refine ⟨3803936062318096355793095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10143829499514923615448253 3803936062318096355793095)
                      ·
                        rfl

theorem cell23_7408139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 3].length) (baseStart_7408139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408139 prefixEnd_7408139 := by exact prefixLift 7408139
  have htrace : WordTrace (prefixWord ++ tailWord_7408139) baseStart_7408139 baseEnd_7408139 := by
    simpa [prefixWord, tailWord_7408139, baseEnd_7408139] using wordTrace_append hprefix tailTrace_7408139
  have hstable : (prefixWord ++ tailWord_7408139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408139).length < 2 ^ (prefixWord ++ tailWord_7408139).sum := by decide
  have hdescent : baseEnd_7408139 < baseStart_7408139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408152 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_7408152 : Nat := 118140960795 + 7408152 * 2 ^ 59
def prefixEnd_7408152 : Nat := 4983230072969 + 3 ^ 40 * 7408152 * 2
def baseEnd_7408152 : Nat := 3803942737566604804930535

theorem tailTrace_7408152 : CollatzResearch.WordTrace tailWord_7408152 prefixEnd_7408152 3803942737566604804930535 := by
  unfold tailWord_7408152
  simp only [CollatzResearch.WordTrace]
  refine ⟨135098750528768995239033355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180131667371691993652044473 135098750528768995239033355)
  ·
    refine ⟨202648125793153492858550033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135098750528768995239033355 202648125793153492858550033)
    ·
      refine ⟨151986094344865119643912525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202648125793153492858550033 151986094344865119643912525)
      ·
        refine ⟨56994785379324419866467197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151986094344865119643912525 56994785379324419866467197)
        ·
          refine ⟨21373044517246657449925199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56994785379324419866467197 21373044517246657449925199)
          ·
            refine ⟨32059566775869986174887799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21373044517246657449925199 32059566775869986174887799)
            ·
              refine ⟨48089350163804979262331699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32059566775869986174887799 48089350163804979262331699)
              ·
                refine ⟨72134025245707468893497549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48089350163804979262331699 72134025245707468893497549)
                ·
                  refine ⟨27050259467140300835061581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72134025245707468893497549 27050259467140300835061581)
                  ·
                    refine ⟨10143847300177612813148093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27050259467140300835061581 10143847300177612813148093)
                    ·
                      refine ⟨3803942737566604804930535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10143847300177612813148093 3803942737566604804930535)
                      ·
                        rfl

theorem cell23_7408152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_7408152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408152 prefixEnd_7408152 := by exact prefixLift 7408152
  have htrace : WordTrace (prefixWord ++ tailWord_7408152) baseStart_7408152 baseEnd_7408152 := by
    simpa [prefixWord, tailWord_7408152, baseEnd_7408152] using wordTrace_append hprefix tailTrace_7408152
  have hstable : (prefixWord ++ tailWord_7408152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408152).length < 2 ^ (prefixWord ++ tailWord_7408152).sum := by decide
  have hdescent : baseEnd_7408152 < baseStart_7408152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408156 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_7408156 : Nat := 118140960795 + 7408156 * 2 ^ 59
def prefixEnd_7408156 : Nat := 4983230072969 + 3 ^ 40 * 7408156 * 2
def baseEnd_7408156 : Nat := 3803944791489222789280517

theorem tailTrace_7408156 : CollatzResearch.WordTrace tailWord_7408156 prefixEnd_7408156 3803944791489222789280517 := by
  unfold tailWord_7408156
  simp only [CollatzResearch.WordTrace]
  refine ⟨135098823474761749580606161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180131764633015666107474881 135098823474761749580606161)
  ·
    refine ⟨101324117606071312185454621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135098823474761749580606161 101324117606071312185454621)
    ·
      refine ⟨37996544102276742069545483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101324117606071312185454621 37996544102276742069545483)
      ·
        refine ⟨56994816153415113104318225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37996544102276742069545483 56994816153415113104318225)
        ·
          refine ⟨42746112115061334828238669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56994816153415113104318225 42746112115061334828238669)
          ·
            refine ⟨16029792043148000560589501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42746112115061334828238669 16029792043148000560589501)
            ·
              refine ⟨6011172016180500210221063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16029792043148000560589501 6011172016180500210221063)
              ·
                refine ⟨9016758024270750315331595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011172016180500210221063 9016758024270750315331595)
                ·
                  refine ⟨13525137036406125472997393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016758024270750315331595 13525137036406125472997393)
                  ·
                    refine ⟨10143852777304594104748045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13525137036406125472997393 10143852777304594104748045)
                    ·
                      refine ⟨3803944791489222789280517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10143852777304594104748045 3803944791489222789280517)
                      ·
                        rfl

theorem cell23_7408156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_7408156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408156 prefixEnd_7408156 := by exact prefixLift 7408156
  have htrace : WordTrace (prefixWord ++ tailWord_7408156) baseStart_7408156 baseEnd_7408156 := by
    simpa [prefixWord, tailWord_7408156, baseEnd_7408156] using wordTrace_append hprefix tailTrace_7408156
  have hstable : (prefixWord ++ tailWord_7408156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408156).length < 2 ^ (prefixWord ++ tailWord_7408156).sum := by decide
  have hdescent : baseEnd_7408156 < baseStart_7408156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408165 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_7408165 : Nat := 118140960795 + 7408165 * 2 ^ 59
def prefixEnd_7408165 : Nat := 4983230072969 + 3 ^ 40 * 7408165 * 2
def baseEnd_7408165 : Nat := 3803949412815113254067975

theorem tailTrace_7408165 : CollatzResearch.WordTrace tailWord_7408165 prefixEnd_7408165 3803949412815113254067975 := by
  unfold tailWord_7408165
  simp only [CollatzResearch.WordTrace]
  refine ⟨270197975206490893698289949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180131983470993929132193299 270197975206490893698289949)
  ·
    refine ⟨101324240702434085136858731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270197975206490893698289949 101324240702434085136858731)
    ·
      refine ⟨151986361053651127705288097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101324240702434085136858731 151986361053651127705288097)
      ·
        refine ⟨113989770790238345778966073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151986361053651127705288097 113989770790238345778966073)
        ·
          refine ⟨85492328092678759334224555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113989770790238345778966073 85492328092678759334224555)
          ·
            refine ⟨128238492139018139001336833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85492328092678759334224555 128238492139018139001336833)
            ·
              refine ⟨96178869104263604251002625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128238492139018139001336833 96178869104263604251002625)
              ·
                refine ⟨72134151828197703188251969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96178869104263604251002625 72134151828197703188251969)
                ·
                  refine ⟨54100613871148277391188977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72134151828197703188251969 54100613871148277391188977)
                  ·
                    refine ⟨40575460403361208043391733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54100613871148277391188977 40575460403361208043391733)
                    ·
                      refine ⟨3803949412815113254067975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40575460403361208043391733 3803949412815113254067975)
                      ·
                        rfl

theorem cell23_7408165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_7408165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408165 prefixEnd_7408165 := by exact prefixLift 7408165
  have htrace : WordTrace (prefixWord ++ tailWord_7408165) baseStart_7408165 baseEnd_7408165 := by
    simpa [prefixWord, tailWord_7408165, baseEnd_7408165] using wordTrace_append hprefix tailTrace_7408165
  have hstable : (prefixWord ++ tailWord_7408165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408165).length < 2 ^ (prefixWord ++ tailWord_7408165).sum := by decide
  have hdescent : baseEnd_7408165 < baseStart_7408165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408170 : List Nat := [3, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_7408170 : Nat := 118140960795 + 7408170 * 2 ^ 59
def prefixEnd_7408170 : Nat := 4983230072969 + 3 ^ 40 * 7408170 * 2
def baseEnd_7408170 : Nat := 3803951980218385734505453

theorem tailTrace_7408170 : CollatzResearch.WordTrace tailWord_7408170 prefixEnd_7408170 3803951980218385734505453 := by
  unfold tailWord_7408170
  simp only [CollatzResearch.WordTrace]
  refine ⟨67549539392868194888055491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180132105047648519701481309 67549539392868194888055491)
  ·
    refine ⟨101324309089302292332083237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67549539392868194888055491 101324309089302292332083237)
    ·
      refine ⟨18998307954244179812265607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101324309089302292332083237 18998307954244179812265607)
      ·
        refine ⟨28497461931366269718398411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18998307954244179812265607 28497461931366269718398411)
        ·
          refine ⟨42746192897049404577597617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28497461931366269718398411 42746192897049404577597617)
          ·
            refine ⟨32059644672787053433198213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42746192897049404577597617 32059644672787053433198213)
            ·
              refine ⟨6011183376147572518724665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32059644672787053433198213 6011183376147572518724665)
              ·
                refine ⟨4508387532110679389043499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6011183376147572518724665 4508387532110679389043499)
                ·
                  refine ⟨6762581298166019083565249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508387532110679389043499 6762581298166019083565249)
                  ·
                    refine ⟨5071935973624514312673937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6762581298166019083565249 5071935973624514312673937)
                    ·
                      refine ⟨3803951980218385734505453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071935973624514312673937 3803951980218385734505453)
                      ·
                        rfl

theorem cell23_7408170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_7408170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408170 prefixEnd_7408170 := by exact prefixLift 7408170
  have htrace : WordTrace (prefixWord ++ tailWord_7408170) baseStart_7408170 baseEnd_7408170 := by
    simpa [prefixWord, tailWord_7408170, baseEnd_7408170] using wordTrace_append hprefix tailTrace_7408170
  have hstable : (prefixWord ++ tailWord_7408170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408170).length < 2 ^ (prefixWord ++ tailWord_7408170).sum := by decide
  have hdescent : baseEnd_7408170 < baseStart_7408170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408195 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 5]
def baseStart_7408195 : Nat := 118140960795 + 7408195 * 2 ^ 59
def prefixEnd_7408195 : Nat := 4983230072969 + 3 ^ 40 * 7408195 * 2
def baseEnd_7408195 : Nat := 3803964817234748136692837

theorem tailTrace_7408195 : CollatzResearch.WordTrace tailWord_7408195 prefixEnd_7408195 3803964817234748136692837 := by
  unfold tailWord_7408195
  simp only [CollatzResearch.WordTrace]
  refine ⟨270199069396382208821882039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180132712930921472547921359 270199069396382208821882039)
  ·
    refine ⟨405298604094573313232823059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270199069396382208821882039 405298604094573313232823059)
    ·
      refine ⟨607947906141859969849234589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405298604094573313232823059 607947906141859969849234589)
      ·
        refine ⟨227980464803197488693462971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607947906141859969849234589 227980464803197488693462971)
        ·
          refine ⟨341970697204796233040194457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227980464803197488693462971 341970697204796233040194457)
          ·
            refine ⟨256478022903597174780145843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341970697204796233040194457 256478022903597174780145843)
            ·
              refine ⟨384717034355395762170218765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256478022903597174780145843 384717034355395762170218765)
              ·
                refine ⟨144268887883273410813832037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384717034355395762170218765 144268887883273410813832037)
                ·
                  refine ⟨27050416478113764527593507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144268887883273410813832037 27050416478113764527593507)
                  ·
                    refine ⟨40575624717170646791390261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27050416478113764527593507 40575624717170646791390261)
                    ·
                      refine ⟨3803964817234748136692837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40575624717170646791390261 3803964817234748136692837)
                      ·
                        rfl

theorem cell23_7408195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_7408195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408195 prefixEnd_7408195 := by exact prefixLift 7408195
  have htrace : WordTrace (prefixWord ++ tailWord_7408195) baseStart_7408195 baseEnd_7408195 := by
    simpa [prefixWord, tailWord_7408195, baseEnd_7408195] using wordTrace_append hprefix tailTrace_7408195
  have hstable : (prefixWord ++ tailWord_7408195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408195).length < 2 ^ (prefixWord ++ tailWord_7408195).sum := by decide
  have hdescent : baseEnd_7408195 < baseStart_7408195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408209 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 1, 4, 2]
def baseStart_7408209 : Nat := 118140960795 + 7408209 * 2 ^ 59
def prefixEnd_7408209 : Nat := 4983230072969 + 3 ^ 40 * 7408209 * 2
def baseEnd_7408209 : Nat := 3803972005963911081917773

theorem tailTrace_7408209 : CollatzResearch.WordTrace tailWord_7408209 prefixEnd_7408209 3803972005963911081917773 := by
  unfold tailWord_7408209
  simp only [CollatzResearch.WordTrace]
  refine ⟨270199580018331489212891681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180133053345554326141927787 270199580018331489212891681)
  ·
    refine ⟨202649685013748616909668761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270199580018331489212891681 202649685013748616909668761)
    ·
      refine ⟨151987263760311462682251571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202649685013748616909668761 151987263760311462682251571)
      ·
        refine ⟨227980895640467194023377357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151987263760311462682251571 227980895640467194023377357)
        ·
          refine ⟨85492835865175197758766509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227980895640467194023377357 85492835865175197758766509)
          ·
            refine ⟨32059813449440699159537441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85492835865175197758766509 32059813449440699159537441)
            ·
              refine ⟨24044860087080524369653081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32059813449440699159537441 24044860087080524369653081)
              ·
                refine ⟨18033645065310393277239811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24044860087080524369653081 18033645065310393277239811)
                ·
                  refine ⟨27050467597965589915859717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18033645065310393277239811 27050467597965589915859717)
                  ·
                    refine ⟨5071962674618548109223697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27050467597965589915859717 5071962674618548109223697)
                    ·
                      refine ⟨3803972005963911081917773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5071962674618548109223697 3803972005963911081917773)
                      ·
                        rfl

theorem cell23_7408209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_7408209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408209 prefixEnd_7408209 := by exact prefixLift 7408209
  have htrace : WordTrace (prefixWord ++ tailWord_7408209) baseStart_7408209 baseEnd_7408209 := by
    simpa [prefixWord, tailWord_7408209, baseEnd_7408209] using wordTrace_append hprefix tailTrace_7408209
  have hstable : (prefixWord ++ tailWord_7408209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408209).length < 2 ^ (prefixWord ++ tailWord_7408209).sum := by decide
  have hdescent : baseEnd_7408209 < baseStart_7408209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408215 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 9]
def baseStart_7408215 : Nat := 118140960795 + 7408215 * 2 ^ 59
def prefixEnd_7408215 : Nat := 4983230072969 + 3 ^ 40 * 7408215 * 2
def baseEnd_7408215 : Nat := 422663898538648673160305

theorem tailTrace_7408215 : CollatzResearch.WordTrace tailWord_7408215 prefixEnd_7408215 422663898538648673160305 := by
  unfold tailWord_7408215
  simp only [CollatzResearch.WordTrace]
  refine ⟨270199798856309752237610099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180133199237539834825073399 270199798856309752237610099)
  ·
    refine ⟨405299698284464628356415149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270199798856309752237610099 405299698284464628356415149)
    ·
      refine ⟨151987386856674235633655681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405299698284464628356415149 151987386856674235633655681)
      ·
        refine ⟨113990540142505676725241761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151987386856674235633655681 113990540142505676725241761)
        ·
          refine ⟨85492905106879257543931321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113990540142505676725241761 85492905106879257543931321)
          ·
            refine ⟨64119678830159443157948491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85492905106879257543931321 64119678830159443157948491)
            ·
              refine ⟨96179518245239164736922737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64119678830159443157948491 96179518245239164736922737)
              ·
                refine ⟨72134638683929373552692053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96179518245239164736922737 72134638683929373552692053)
                ·
                  refine ⟨422663898538648673160305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72134638683929373552692053 422663898538648673160305)
                  ·
                    rfl

theorem cell23_7408215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 9].length) (baseStart_7408215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408215 prefixEnd_7408215 := by exact prefixLift 7408215
  have htrace : WordTrace (prefixWord ++ tailWord_7408215) baseStart_7408215 baseEnd_7408215 := by
    simpa [prefixWord, tailWord_7408215, baseEnd_7408215] using wordTrace_append hprefix tailTrace_7408215
  have hstable : (prefixWord ++ tailWord_7408215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408215).length < 2 ^ (prefixWord ++ tailWord_7408215).sum := by decide
  have hdescent : baseEnd_7408215 < baseStart_7408215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408220 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_7408220 : Nat := 118140960795 + 7408220 * 2 ^ 59
def prefixEnd_7408220 : Nat := 4983230072969 + 3 ^ 40 * 7408220 * 2
def baseEnd_7408220 : Nat := 3803977654251110538880223

theorem tailTrace_7408220 : CollatzResearch.WordTrace tailWord_7408220 prefixEnd_7408220 3803977654251110538880223 := by
  unfold tailWord_7408220
  simp only [CollatzResearch.WordTrace]
  refine ⟨135099990610645819045771057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180133320814194425394361409 135099990610645819045771057)
  ·
    refine ⟨101324992957984364284328293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135099990610645819045771057 101324992957984364284328293)
    ·
      refine ⟨18998436179622068303311555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101324992957984364284328293 18998436179622068303311555)
      ·
        refine ⟨28497654269433102454967333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18998436179622068303311555 28497654269433102454967333)
        ·
          refine ⟨5343310175518706710306375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28497654269433102454967333 5343310175518706710306375)
          ·
            refine ⟨8014965263278060065459563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343310175518706710306375 8014965263278060065459563)
            ·
              refine ⟨12022447894917090098189345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8014965263278060065459563 12022447894917090098189345)
              ·
                refine ⟨9016835921187817573642009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12022447894917090098189345 9016835921187817573642009)
                ·
                  refine ⟨6762626940890863180231507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9016835921187817573642009 6762626940890863180231507)
                  ·
                    refine ⟨10143940411336294770347261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762626940890863180231507 10143940411336294770347261)
                    ·
                      refine ⟨3803977654251110538880223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10143940411336294770347261 3803977654251110538880223)
                      ·
                        rfl

theorem cell23_7408220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_7408220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408220 prefixEnd_7408220 := by exact prefixLift 7408220
  have htrace : WordTrace (prefixWord ++ tailWord_7408220) baseStart_7408220 baseEnd_7408220 := by
    simpa [prefixWord, tailWord_7408220, baseEnd_7408220] using wordTrace_append hprefix tailTrace_7408220
  have hstable : (prefixWord ++ tailWord_7408220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408220).length < 2 ^ (prefixWord ++ tailWord_7408220).sum := by decide
  have hdescent : baseEnd_7408220 < baseStart_7408220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408255 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_7408255 : Nat := 118140960795 + 7408255 * 2 ^ 59
def prefixEnd_7408255 : Nat := 4983230072969 + 3 ^ 40 * 7408255 * 2
def baseEnd_7408255 : Nat := 3803995626074017901942561

theorem tailTrace_7408255 : CollatzResearch.WordTrace tailWord_7408255 prefixEnd_7408255 3803995626074017901942561 := by
  unfold tailWord_7408255
  simp only [CollatzResearch.WordTrace]
  refine ⟨270201257776164839069066219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180134171850776559379377479 270201257776164839069066219)
  ·
    refine ⟨405301886664247258603599329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270201257776164839069066219 405301886664247258603599329)
    ·
      refine ⟨303976414998185443952699497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405301886664247258603599329 303976414998185443952699497)
      ·
        refine ⟨227982311248639082964524623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303976414998185443952699497 227982311248639082964524623)
        ·
          refine ⟨341973466872958624446786935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227982311248639082964524623 341973466872958624446786935)
          ·
            refine ⟨512960200309437936670180403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341973466872958624446786935 512960200309437936670180403)
            ·
              refine ⟨769440300464156905005270605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512960200309437936670180403 769440300464156905005270605)
              ·
                refine ⟨288540112674058839376976477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 769440300464156905005270605 288540112674058839376976477)
                ·
                  refine ⟨108202542252772064766366179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 288540112674058839376976477 108202542252772064766366179)
                  ·
                    refine ⟨162303813379158097149549269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108202542252772064766366179 162303813379158097149549269)
                    ·
                      refine ⟨3803995626074017901942561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162303813379158097149549269 3803995626074017901942561)
                      ·
                        rfl

theorem cell23_7408255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_7408255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408255 prefixEnd_7408255 := by exact prefixLift 7408255
  have htrace : WordTrace (prefixWord ++ tailWord_7408255) baseStart_7408255 baseEnd_7408255 := by
    simpa [prefixWord, tailWord_7408255, baseEnd_7408255] using wordTrace_append hprefix tailTrace_7408255
  have hstable : (prefixWord ++ tailWord_7408255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408255).length < 2 ^ (prefixWord ++ tailWord_7408255).sum := by decide
  have hdescent : baseEnd_7408255 < baseStart_7408255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408275 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 10]
def baseStart_7408275 : Nat := 118140960795 + 7408275 * 2 ^ 59
def prefixEnd_7408275 : Nat := 4983230072969 + 3 ^ 40 * 7408275 * 2
def baseEnd_7408275 : Nat := 1268001965229035941230823

theorem tailTrace_7408275 : CollatzResearch.WordTrace tailWord_7408275 prefixEnd_7408275 1268001965229035941230823 := by
  unfold tailWord_7408275
  simp only [CollatzResearch.WordTrace]
  refine ⟨270201987236092382484794279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180134658157394921656529519 270201987236092382484794279)
  ·
    refine ⟨405302980854138573727191419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270201987236092382484794279 405302980854138573727191419)
    ·
      refine ⟨607954471281207860590787129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405302980854138573727191419 607954471281207860590787129)
      ·
        refine ⟨455965853460905895443090347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607954471281207860590787129 455965853460905895443090347)
        ·
          refine ⟨683948780191358843164635521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455965853460905895443090347 683948780191358843164635521)
          ·
            refine ⟨512961585143519132373476641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683948780191358843164635521 512961585143519132373476641)
            ·
              refine ⟨384721188857639349280107481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512961585143519132373476641 384721188857639349280107481)
              ·
                refine ⟨288540891643229511960080611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384721188857639349280107481 288540891643229511960080611)
                ·
                  refine ⟨432811337464844267940120917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288540891643229511960080611 432811337464844267940120917)
                  ·
                    refine ⟨1268001965229035941230823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 432811337464844267940120917 1268001965229035941230823)
                    ·
                      rfl

theorem cell23_7408275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 10].length) (baseStart_7408275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408275 prefixEnd_7408275 := by exact prefixLift 7408275
  have htrace : WordTrace (prefixWord ++ tailWord_7408275) baseStart_7408275 baseEnd_7408275 := by
    simpa [prefixWord, tailWord_7408275, baseEnd_7408275] using wordTrace_append hprefix tailTrace_7408275
  have hstable : (prefixWord ++ tailWord_7408275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408275).length < 2 ^ (prefixWord ++ tailWord_7408275).sum := by decide
  have hdescent : baseEnd_7408275 < baseStart_7408275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408286 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_7408286 : Nat := 118140960795 + 7408286 * 2 ^ 59
def prefixEnd_7408286 : Nat := 4983230072969 + 3 ^ 40 * 7408286 * 2
def baseEnd_7408286 : Nat := 3804011543974307280654919

theorem tailTrace_7408286 : CollatzResearch.WordTrace tailWord_7408286 prefixEnd_7408286 3804011543974307280654919 := by
  unfold tailWord_7408286
  simp only [CollatzResearch.WordTrace]
  refine ⟨33775298554881566420430589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180134925626035020908963141 33775298554881566420430589)
  ·
    refine ⟨12665736958080587407661471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33775298554881566420430589 12665736958080587407661471)
    ·
      refine ⟨18998605437120881111492207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12665736958080587407661471 18998605437120881111492207)
      ·
        refine ⟨28497908155681321667238311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18998605437120881111492207 28497908155681321667238311)
        ·
          refine ⟨42746862233521982500857467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28497908155681321667238311 42746862233521982500857467)
          ·
            refine ⟨64120293350282973751286201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42746862233521982500857467 64120293350282973751286201)
            ·
              refine ⟨48090220012712230313464651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64120293350282973751286201 48090220012712230313464651)
              ·
                refine ⟨72135330019068345470196977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48090220012712230313464651 72135330019068345470196977)
                ·
                  refine ⟨54101497514301259102647733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72135330019068345470196977 54101497514301259102647733)
                  ·
                    refine ⟨5072015391965743040873225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54101497514301259102647733 5072015391965743040873225)
                    ·
                      refine ⟨3804011543974307280654919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072015391965743040873225 3804011543974307280654919)
                      ·
                        rfl

theorem cell23_7408286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_7408286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408286 prefixEnd_7408286 := by exact prefixLift 7408286
  have htrace : WordTrace (prefixWord ++ tailWord_7408286) baseStart_7408286 baseEnd_7408286 := by
    simpa [prefixWord, tailWord_7408286, baseEnd_7408286] using wordTrace_append hprefix tailTrace_7408286
  have hstable : (prefixWord ++ tailWord_7408286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408286).length < 2 ^ (prefixWord ++ tailWord_7408286).sum := by decide
  have hdescent : baseEnd_7408286 < baseStart_7408286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408289 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_7408289 : Nat := 118140960795 + 7408289 * 2 ^ 59
def prefixEnd_7408289 : Nat := 4983230072969 + 3 ^ 40 * 7408289 * 2
def baseEnd_7408289 : Nat := 3804013084416270768917405

theorem tailTrace_7408289 : CollatzResearch.WordTrace tailWord_7408289 prefixEnd_7408289 3804013084416270768917405 := by
  unfold tailWord_7408289
  simp only [CollatzResearch.WordTrace]
  refine ⟨270202497858041662875803921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180134998572027775250535947 270202497858041662875803921)
  ·
    refine ⟨202651873393531247156852941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270202497858041662875803921 202651873393531247156852941)
    ·
      refine ⟨75994452522574217683819853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202651873393531247156852941 75994452522574217683819853)
      ·
        refine ⟨28497919695965331631432445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75994452522574217683819853 28497919695965331631432445)
        ·
          refine ⟨10686719885986999361787167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28497919695965331631432445 10686719885986999361787167)
          ·
            refine ⟨16030079828980499042680751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10686719885986999361787167 16030079828980499042680751)
            ·
              refine ⟨24045119743470748564021127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16030079828980499042680751 24045119743470748564021127)
              ·
                refine ⟨36067679615206122846031691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24045119743470748564021127 36067679615206122846031691)
                ·
                  refine ⟨54101519422809184269047537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36067679615206122846031691 54101519422809184269047537)
                  ·
                    refine ⟨40576139567106888201785653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54101519422809184269047537 40576139567106888201785653)
                    ·
                      refine ⟨3804013084416270768917405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40576139567106888201785653 3804013084416270768917405)
                      ·
                        rfl

theorem cell23_7408289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_7408289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408289 prefixEnd_7408289 := by exact prefixLift 7408289
  have htrace : WordTrace (prefixWord ++ tailWord_7408289) baseStart_7408289 baseEnd_7408289 := by
    simpa [prefixWord, tailWord_7408289, baseEnd_7408289] using wordTrace_append hprefix tailTrace_7408289
  have hstable : (prefixWord ++ tailWord_7408289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408289).length < 2 ^ (prefixWord ++ tailWord_7408289).sum := by decide
  have hdescent : baseEnd_7408289 < baseStart_7408289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408319 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 3]
def baseStart_7408319 : Nat := 118140960795 + 7408319 * 2 ^ 59
def prefixEnd_7408319 : Nat := 4983230072969 + 3 ^ 40 * 7408319 * 2
def baseEnd_7408319 : Nat := 3804028488835905651542267

theorem tailTrace_7408319 : CollatzResearch.WordTrace tailWord_7408319 prefixEnd_7408319 3804028488835905651542267 := by
  unfold tailWord_7408319
  simp only [CollatzResearch.WordTrace]
  refine ⟨270203592047932977999396011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180135728031955318666264007 270203592047932977999396011)
  ·
    refine ⟨405305388071899466999094017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270203592047932977999396011 405305388071899466999094017)
    ·
      refine ⟨303979041053924600249320513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405305388071899466999094017 303979041053924600249320513)
      ·
        refine ⟨227984280790443450186990385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303979041053924600249320513 227984280790443450186990385)
        ·
          refine ⟨170988210592832587640242789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227984280790443450186990385 170988210592832587640242789)
          ·
            refine ⟨32060289486156110182545523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170988210592832587640242789 32060289486156110182545523)
            ·
              refine ⟨48090434229234165273818285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32060289486156110182545523 48090434229234165273818285)
              ·
                refine ⟨18033912835962811977681857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48090434229234165273818285 18033912835962811977681857)
                ·
                  refine ⟨13525434626972108983261393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18033912835962811977681857 13525434626972108983261393)
                  ·
                    refine ⟨10144075970229081737446045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13525434626972108983261393 10144075970229081737446045)
                    ·
                      refine ⟨3804028488835905651542267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10144075970229081737446045 3804028488835905651542267)
                      ·
                        rfl

theorem cell23_7408319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_7408319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408319 prefixEnd_7408319 := by exact prefixLift 7408319
  have htrace : WordTrace (prefixWord ++ tailWord_7408319) baseStart_7408319 baseEnd_7408319 := by
    simpa [prefixWord, tailWord_7408319, baseEnd_7408319] using wordTrace_append hprefix tailTrace_7408319
  have hstable : (prefixWord ++ tailWord_7408319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408319).length < 2 ^ (prefixWord ++ tailWord_7408319).sum := by decide
  have hdescent : baseEnd_7408319 < baseStart_7408319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408343 : List Nat := [1, 1, 3, 2, 1, 4, 4, 2, 1, 4]
def baseStart_7408343 : Nat := 118140960795 + 7408343 * 2 ^ 59
def prefixEnd_7408343 : Nat := 4983230072969 + 3 ^ 40 * 7408343 * 2
def baseEnd_7408343 : Nat := 1268013604123871185880719

theorem tailTrace_7408343 : CollatzResearch.WordTrace tailWord_7408343 prefixEnd_7408343 1268013604123871185880719 := by
  unfold tailWord_7408343
  simp only [CollatzResearch.WordTrace]
  refine ⟨270204467399846030098269683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180136311599897353398846455 270204467399846030098269683)
  ·
    refine ⟨405306701099769045147404525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270204467399846030098269683 405306701099769045147404525)
    ·
      refine ⟨151990012912413391930276697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405306701099769045147404525 151990012912413391930276697)
      ·
        refine ⟨113992509684310043947707523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151990012912413391930276697 113992509684310043947707523)
        ·
          refine ⟨170988764526465065921561285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113992509684310043947707523 170988764526465065921561285)
          ·
            refine ⟨32060393348712199860292741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170988764526465065921561285 32060393348712199860292741)
            ·
              refine ⟨6011323752883537473804889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32060393348712199860292741 6011323752883537473804889)
              ·
                refine ⟨4508492814662653105353667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6011323752883537473804889 4508492814662653105353667)
                ·
                  refine ⟨6762739221993979658030501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508492814662653105353667 6762739221993979658030501)
                  ·
                    refine ⟨1268013604123871185880719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762739221993979658030501 1268013604123871185880719)
                    ·
                      rfl

theorem cell23_7408343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_7408343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408343 prefixEnd_7408343 := by exact prefixLift 7408343
  have htrace : WordTrace (prefixWord ++ tailWord_7408343) baseStart_7408343 baseEnd_7408343 := by
    simpa [prefixWord, tailWord_7408343, baseEnd_7408343] using wordTrace_append hprefix tailTrace_7408343
  have hstable : (prefixWord ++ tailWord_7408343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408343).length < 2 ^ (prefixWord ++ tailWord_7408343).sum := by decide
  have hdescent : baseEnd_7408343 < baseStart_7408343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408362 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_7408362 : Nat := 118140960795 + 7408362 * 2 ^ 59
def prefixEnd_7408362 : Nat := 4983230072969 + 3 ^ 40 * 7408362 * 2
def baseEnd_7408362 : Nat := 3804050568504048983304569

theorem tailTrace_7408362 : CollatzResearch.WordTrace tailWord_7408362 prefixEnd_7408362 3804050568504048983304569 := by
  unfold tailWord_7408362
  simp only [CollatzResearch.WordTrace]
  refine ⟨67551290096694299085802835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180136773591184797562140893 67551290096694299085802835)
  ·
    refine ⟨101326935145041448628704253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67551290096694299085802835 101326935145041448628704253)
    ·
      refine ⟨37997600679390543235764095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101326935145041448628704253 37997600679390543235764095)
      ·
        refine ⟨56996401019085814853646143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37997600679390543235764095 56996401019085814853646143)
        ·
          refine ⟨85494601528628722280469215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56996401019085814853646143 85494601528628722280469215)
          ·
            refine ⟨128241902292943083420703823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85494601528628722280469215 128241902292943083420703823)
            ·
              refine ⟨192362853439414625131055735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128241902292943083420703823 192362853439414625131055735)
              ·
                refine ⟨288544280159121937696583603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192362853439414625131055735 288544280159121937696583603)
                ·
                  refine ⟨432816420238682906544875405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288544280159121937696583603 432816420238682906544875405)
                  ·
                    refine ⟨162306157589506089954328277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 432816420238682906544875405 162306157589506089954328277)
                    ·
                      refine ⟨3804050568504048983304569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162306157589506089954328277 3804050568504048983304569)
                      ·
                        rfl

theorem cell23_7408362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_7408362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408362 prefixEnd_7408362 := by exact prefixLift 7408362
  have htrace : WordTrace (prefixWord ++ tailWord_7408362) baseStart_7408362 baseEnd_7408362 := by
    simpa [prefixWord, tailWord_7408362, baseEnd_7408362] using wordTrace_append hprefix tailTrace_7408362
  have hstable : (prefixWord ++ tailWord_7408362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408362).length < 2 ^ (prefixWord ++ tailWord_7408362).sum := by decide
  have hdescent : baseEnd_7408362 < baseStart_7408362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408366 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_7408366 : Nat := 118140960795 + 7408366 * 2 ^ 59
def prefixEnd_7408366 : Nat := 4983230072969 + 3 ^ 40 * 7408366 * 2
def baseEnd_7408366 : Nat := 3804052622426666967654551

theorem tailTrace_7408366 : CollatzResearch.WordTrace tailWord_7408366 prefixEnd_7408366 3804052622426666967654551 := by
  unfold tailWord_7408366
  simp only [CollatzResearch.WordTrace]
  refine ⟨33775663284845338128294619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180136870852508470017571301 33775663284845338128294619)
  ·
    refine ⟨50663494927268007192441929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33775663284845338128294619 50663494927268007192441929)
    ·
      refine ⟨37997621195451005394331447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50663494927268007192441929 37997621195451005394331447)
      ·
        refine ⟨56996431793176508091497171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37997621195451005394331447 56996431793176508091497171)
        ·
          refine ⟨85494647689764762137245757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56996431793176508091497171 85494647689764762137245757)
          ·
            refine ⟨32060492883661785801467159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85494647689764762137245757 32060492883661785801467159)
            ·
              refine ⟨48090739325492678702200739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32060492883661785801467159 48090739325492678702200739)
              ·
                refine ⟨72136108988239018053301109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48090739325492678702200739 72136108988239018053301109)
                ·
                  refine ⟨6762760217647407942496979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72136108988239018053301109 6762760217647407942496979)
                  ·
                    refine ⟨10144140326471111913745469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762760217647407942496979 10144140326471111913745469)
                    ·
                      refine ⟨3804052622426666967654551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10144140326471111913745469 3804052622426666967654551)
                      ·
                        rfl

theorem cell23_7408366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_7408366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408366 prefixEnd_7408366 := by exact prefixLift 7408366
  have htrace : WordTrace (prefixWord ++ tailWord_7408366) baseStart_7408366 baseEnd_7408366 := by
    simpa [prefixWord, tailWord_7408366, baseEnd_7408366] using wordTrace_append hprefix tailTrace_7408366
  have hstable : (prefixWord ++ tailWord_7408366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408366).length < 2 ^ (prefixWord ++ tailWord_7408366).sum := by decide
  have hdescent : baseEnd_7408366 < baseStart_7408366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408369 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 1, 5]
def baseStart_7408369 : Nat := 118140960795 + 7408369 * 2 ^ 59
def prefixEnd_7408369 : Nat := 4983230072969 + 3 ^ 40 * 7408369 * 2
def baseEnd_7408369 : Nat := 1268018054289543485305679

theorem tailTrace_7408369 : CollatzResearch.WordTrace tailWord_7408369 prefixEnd_7408369 1268018054289543485305679 := by
  unfold tailWord_7408369
  simp only [CollatzResearch.WordTrace]
  refine ⟨270205415697751836538716161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180136943798501224359144107 270205415697751836538716161)
  ·
    refine ⟨202654061773313877404037121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270205415697751836538716161 202654061773313877404037121)
    ·
      refine ⟨151990546329985408053027841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202654061773313877404037121 151990546329985408053027841)
      ·
        refine ⟨113992909747489056039770881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151990546329985408053027841 113992909747489056039770881)
        ·
          refine ⟨85494682310616792029828161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113992909747489056039770881 85494682310616792029828161)
          ·
            refine ⟨64121011732962594022371121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85494682310616792029828161 64121011732962594022371121)
            ·
              refine ⟨48090758799721945516778341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64121011732962594022371121 48090758799721945516778341)
              ·
                refine ⟨9017017274947864784395939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48090758799721945516778341 9017017274947864784395939)
                ·
                  refine ⟨13525525912421797176593909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9017017274947864784395939 13525525912421797176593909)
                  ·
                    refine ⟨1268018054289543485305679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13525525912421797176593909 1268018054289543485305679)
                    ·
                      rfl

theorem cell23_7408369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_7408369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408369 prefixEnd_7408369 := by exact prefixLift 7408369
  have htrace : WordTrace (prefixWord ++ tailWord_7408369) baseStart_7408369 baseEnd_7408369 := by
    simpa [prefixWord, tailWord_7408369, baseEnd_7408369] using wordTrace_append hprefix tailTrace_7408369
  have hstable : (prefixWord ++ tailWord_7408369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408369).length < 2 ^ (prefixWord ++ tailWord_7408369).sum := by decide
  have hdescent : baseEnd_7408369 < baseStart_7408369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408389 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 8, 2]
def baseStart_7408389 : Nat := 118140960795 + 7408389 * 2 ^ 59
def prefixEnd_7408389 : Nat := 4983230072969 + 3 ^ 40 * 7408389 * 2
def baseEnd_7408389 : Nat := 3804064432481720377666945

theorem tailTrace_7408389 : CollatzResearch.WordTrace tailWord_7408389 prefixEnd_7408389 3804064432481720377666945 := by
  unfold tailWord_7408389
  simp only [CollatzResearch.WordTrace]
  refine ⟨270206145157679379954444221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180137430105119586636296147 270206145157679379954444221)
  ·
    refine ⟨101327304434129767482916583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270206145157679379954444221 101327304434129767482916583)
    ·
      refine ⟨151990956651194651224374875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101327304434129767482916583 151990956651194651224374875)
      ·
        refine ⟨227986434976791976836562313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151990956651194651224374875 227986434976791976836562313)
        ·
          refine ⟨170989826232593982627421735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227986434976791976836562313 170989826232593982627421735)
          ·
            refine ⟨256484739348890973941132603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170989826232593982627421735 256484739348890973941132603)
            ·
              refine ⟨384727109023336460911698905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256484739348890973941132603 384727109023336460911698905)
              ·
                refine ⟨288545331767502345683774179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384727109023336460911698905 288545331767502345683774179)
                ·
                  refine ⟨432817997651253518525661269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288545331767502345683774179 432817997651253518525661269)
                  ·
                    refine ⟨5072085909975627170222593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 432817997651253518525661269 5072085909975627170222593)
                    ·
                      refine ⟨3804064432481720377666945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072085909975627170222593 3804064432481720377666945)
                      ·
                        rfl

theorem cell23_7408389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_7408389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408389 prefixEnd_7408389 := by exact prefixLift 7408389
  have htrace : WordTrace (prefixWord ++ tailWord_7408389) baseStart_7408389 baseEnd_7408389 := by
    simpa [prefixWord, tailWord_7408389, baseEnd_7408389] using wordTrace_append hprefix tailTrace_7408389
  have hstable : (prefixWord ++ tailWord_7408389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408389).length < 2 ^ (prefixWord ++ tailWord_7408389).sum := by decide
  have hdescent : baseEnd_7408389 < baseStart_7408389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408399 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 4, 4]
def baseStart_7408399 : Nat := 118140960795 + 7408399 * 2 ^ 59
def prefixEnd_7408399 : Nat := 4983230072969 + 3 ^ 40 * 7408399 * 2
def baseEnd_7408399 : Nat := 1268023189096088446180633

theorem tailTrace_7408399 : CollatzResearch.WordTrace tailWord_7408399 prefixEnd_7408399 1268023189096088446180633 := by
  unfold tailWord_7408399
  simp only [CollatzResearch.WordTrace]
  refine ⟨270206509887643151662308251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180137673258428767774872167 270206509887643151662308251)
  ·
    refine ⟨405309764831464727493462377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270206509887643151662308251 405309764831464727493462377)
    ·
      refine ⟨303982323623598545620096783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405309764831464727493462377 303982323623598545620096783)
      ·
        refine ⟨455973485435397818430145175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303982323623598545620096783 455973485435397818430145175)
        ·
          refine ⟨683960228153096727645217763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455973485435397818430145175 683960228153096727645217763)
          ·
            refine ⟨1025940342229645091467826645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683960228153096727645217763 1025940342229645091467826645)
            ·
              refine ⟨24045476771007306831277187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1025940342229645091467826645 24045476771007306831277187)
              ·
                refine ⟨36068215156510960246915781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24045476771007306831277187 36068215156510960246915781)
                ·
                  refine ⟨6762790341845805046296709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36068215156510960246915781 6762790341845805046296709)
                  ·
                    refine ⟨1268023189096088446180633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762790341845805046296709 1268023189096088446180633)
                    ·
                      rfl

theorem cell23_7408399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 4].length) (baseStart_7408399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408399 prefixEnd_7408399 := by exact prefixLift 7408399
  have htrace : WordTrace (prefixWord ++ tailWord_7408399) baseStart_7408399 baseEnd_7408399 := by
    simpa [prefixWord, tailWord_7408399, baseEnd_7408399] using wordTrace_append hprefix tailTrace_7408399
  have hstable : (prefixWord ++ tailWord_7408399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408399).length < 2 ^ (prefixWord ++ tailWord_7408399).sum := by decide
  have hdescent : baseEnd_7408399 < baseStart_7408399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408409 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 3]
def baseStart_7408409 : Nat := 118140960795 + 7408409 * 2 ^ 59
def prefixEnd_7408409 : Nat := 4983230072969 + 3 ^ 40 * 7408409 * 2
def baseEnd_7408409 : Nat := 3804074702094810299416853

theorem tailTrace_7408409 : CollatzResearch.WordTrace tailWord_7408409 prefixEnd_7408409 3804074702094810299416853 := by
  unfold tailWord_7408409
  simp only [CollatzResearch.WordTrace]
  refine ⟨270206874617606923370172281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180137916411737948913448187 270206874617606923370172281)
  ·
    refine ⟨202655155963205192527629211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270206874617606923370172281 202655155963205192527629211)
    ·
      refine ⟨303982733944807788791443817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202655155963205192527629211 303982733944807788791443817)
      ·
        refine ⟨227987050458605841593582863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303982733944807788791443817 227987050458605841593582863)
        ·
          refine ⟨341980575687908762390374295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227987050458605841593582863 341980575687908762390374295)
          ·
            refine ⟨512970863531863143585561443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341980575687908762390374295 512970863531863143585561443)
            ·
              refine ⟨769456295297794715378342165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512970863531863143585561443 769456295297794715378342165)
              ·
                refine ⟨36068263842084127283359789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 769456295297794715378342165 36068263842084127283359789)
                ·
                  refine ⟨13525598940781547731259921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36068263842084127283359789 13525598940781547731259921)
                  ·
                    refine ⟨10144199205586160798444941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13525598940781547731259921 10144199205586160798444941)
                    ·
                      refine ⟨3804074702094810299416853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10144199205586160798444941 3804074702094810299416853)
                      ·
                        rfl

theorem cell23_7408409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_7408409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408409 prefixEnd_7408409 := by exact prefixLift 7408409
  have htrace : WordTrace (prefixWord ++ tailWord_7408409) baseStart_7408409 baseEnd_7408409 := by
    simpa [prefixWord, tailWord_7408409, baseEnd_7408409] using wordTrace_append hprefix tailTrace_7408409
  have hstable : (prefixWord ++ tailWord_7408409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408409).length < 2 ^ (prefixWord ++ tailWord_7408409).sum := by decide
  have hdescent : baseEnd_7408409 < baseStart_7408409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408416 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 1, 6]
def baseStart_7408416 : Nat := 118140960795 + 7408416 * 2 ^ 59
def prefixEnd_7408416 : Nat := 4983230072969 + 3 ^ 40 * 7408416 * 2
def baseEnd_7408416 : Nat := 1268026098819797257343107

theorem tailTrace_7408416 : CollatzResearch.WordTrace tailWord_7408416 prefixEnd_7408416 1268026098819797257343107 := by
  unfold tailWord_7408416
  simp only [CollatzResearch.WordTrace]
  refine ⟨135103564964290781782838551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180138086619054375710451401 135103564964290781782838551)
  ·
    refine ⟨202655347446436172674257827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135103564964290781782838551 202655347446436172674257827)
    ·
      refine ⟨303983021169654259011386741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202655347446436172674257827 303983021169654259011386741)
      ·
        refine ⟨28498408234655086782317507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 303983021169654259011386741 28498408234655086782317507)
        ·
          refine ⟨42747612351982630173476261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28498408234655086782317507 42747612351982630173476261)
          ·
            refine ⟨8015177315996743157526799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42747612351982630173476261 8015177315996743157526799)
            ·
              refine ⟨12022765973995114736290199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8015177315996743157526799 12022765973995114736290199)
              ·
                refine ⟨18034148960992672104435299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12022765973995114736290199 18034148960992672104435299)
                ·
                  refine ⟨27051223441489008156652949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18034148960992672104435299 27051223441489008156652949)
                  ·
                    refine ⟨1268026098819797257343107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27051223441489008156652949 1268026098819797257343107)
                    ·
                      rfl

theorem cell23_7408416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_7408416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408416 prefixEnd_7408416 := by exact prefixLift 7408416
  have htrace : WordTrace (prefixWord ++ tailWord_7408416) baseStart_7408416 baseEnd_7408416 := by
    simpa [prefixWord, tailWord_7408416, baseEnd_7408416] using wordTrace_append hprefix tailTrace_7408416
  have hstable : (prefixWord ++ tailWord_7408416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408416).length < 2 ^ (prefixWord ++ tailWord_7408416).sum := by decide
  have hdescent : baseEnd_7408416 < baseStart_7408416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408432 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_7408432 : Nat := 118140960795 + 7408432 * 2 ^ 59
def prefixEnd_7408432 : Nat := 4983230072969 + 3 ^ 40 * 7408432 * 2
def baseEnd_7408432 : Nat := 3804086512149863709429247

theorem tailTrace_7408432 : CollatzResearch.WordTrace tailWord_7408432 prefixEnd_7408432 3804086512149863709429247 := by
  unfold tailWord_7408432
  simp only [CollatzResearch.WordTrace]
  refine ⟨135103856748261799149129775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180138475664349065532173033 135103856748261799149129775)
  ·
    refine ⟨202655785122392698723694663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135103856748261799149129775 202655785122392698723694663)
    ·
      refine ⟨303983677683589048085541995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202655785122392698723694663 303983677683589048085541995)
      ·
        refine ⟨455975516525383572128312993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303983677683589048085541995 455975516525383572128312993)
        ·
          refine ⟨341981637394037679096234745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455975516525383572128312993 341981637394037679096234745)
          ·
            refine ⟨256486228045528259322176059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341981637394037679096234745 256486228045528259322176059)
            ·
              refine ⟨384729342068292388983264089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256486228045528259322176059 384729342068292388983264089)
              ·
                refine ⟨288547006551219291737448067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384729342068292388983264089 288547006551219291737448067)
                ·
                  refine ⟨432820509826828937606172101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288547006551219291737448067 432820509826828937606172101)
                  ·
                    refine ⟨81153845592530425801157269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 432820509826828937606172101 81153845592530425801157269)
                    ·
                      refine ⟨3804086512149863709429247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81153845592530425801157269 3804086512149863709429247)
                      ·
                        rfl

theorem cell23_7408432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_7408432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408432 prefixEnd_7408432 := by exact prefixLift 7408432
  have htrace : WordTrace (prefixWord ++ tailWord_7408432) baseStart_7408432 baseEnd_7408432 := by
    simpa [prefixWord, tailWord_7408432, baseEnd_7408432] using wordTrace_append hprefix tailTrace_7408432
  have hstable : (prefixWord ++ tailWord_7408432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408432).length < 2 ^ (prefixWord ++ tailWord_7408432).sum := by decide
  have hdescent : baseEnd_7408432 < baseStart_7408432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408439 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_7408439 : Nat := 118140960795 + 7408439 * 2 ^ 59
def prefixEnd_7408439 : Nat := 4983230072969 + 3 ^ 40 * 7408439 * 2
def baseEnd_7408439 : Nat := 3804090106514445182041715

theorem tailTrace_7408439 : CollatzResearch.WordTrace tailWord_7408439 prefixEnd_7408439 3804090106514445182041715 := by
  unfold tailWord_7408439
  simp only [CollatzResearch.WordTrace]
  refine ⟨270207968807498238493764371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180138645871665492329176247 270207968807498238493764371)
  ·
    refine ⟨405311953211247357740646557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270207968807498238493764371 405311953211247357740646557)
    ·
      refine ⟨151991982454217759152742459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405311953211247357740646557 151991982454217759152742459)
      ·
        refine ⟨227987973681326638729113689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151991982454217759152742459 227987973681326638729113689)
        ·
          refine ⟨170990980260994979046835267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227987973681326638729113689 170990980260994979046835267)
          ·
            refine ⟨256486470391492468570252901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170990980260994979046835267 256486470391492468570252901)
            ·
              refine ⟨48091213198404837856922419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256486470391492468570252901 48091213198404837856922419)
              ·
                refine ⟨72136819797607256785383629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48091213198404837856922419 72136819797607256785383629)
                ·
                  refine ⟨27051307424102721294518861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72136819797607256785383629 27051307424102721294518861)
                  ·
                    refine ⟨10144240284038520485444573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27051307424102721294518861 10144240284038520485444573)
                    ·
                      refine ⟨3804090106514445182041715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10144240284038520485444573 3804090106514445182041715)
                      ·
                        rfl

theorem cell23_7408439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_7408439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408439 prefixEnd_7408439 := by exact prefixLift 7408439
  have htrace : WordTrace (prefixWord ++ tailWord_7408439) baseStart_7408439 baseEnd_7408439 := by
    simpa [prefixWord, tailWord_7408439, baseEnd_7408439] using wordTrace_append hprefix tailTrace_7408439
  have hstable : (prefixWord ++ tailWord_7408439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408439).length < 2 ^ (prefixWord ++ tailWord_7408439).sum := by decide
  have hdescent : baseEnd_7408439 < baseStart_7408439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408446 : List Nat := [4, 2, 1, 2, 3, 2, 9]
def baseStart_7408446 : Nat := 118140960795 + 7408446 * 2 ^ 59
def prefixEnd_7408446 : Nat := 4983230072969 + 3 ^ 40 * 7408446 * 2
def baseEnd_7408446 : Nat := 46964119763938600674743

theorem tailTrace_7408446 : CollatzResearch.WordTrace tailWord_7408446 prefixEnd_7408446 46964119763938600674743 := by
  unfold tailWord_7408446
  simp only [CollatzResearch.WordTrace]
  refine ⟨33776028014809109836158649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180138816078981919126179461 33776028014809109836158649)
  ·
    refine ⟨25332021011106832377118987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33776028014809109836158649 25332021011106832377118987)
    ·
      refine ⟨37998031516660248565678481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25332021011106832377118987 37998031516660248565678481)
      ·
        refine ⟨28498523637495186424258861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37998031516660248565678481 28498523637495186424258861)
        ·
          refine ⟨10686946364060694909097073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28498523637495186424258861 10686946364060694909097073)
          ·
            refine ⟨8015209773045521181822805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10686946364060694909097073 8015209773045521181822805)
            ·
              refine ⟨46964119763938600674743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8015209773045521181822805 46964119763938600674743)
              ·
                rfl

theorem cell23_7408446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 9].length) (baseStart_7408446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408446 prefixEnd_7408446 := by exact prefixLift 7408446
  have htrace : WordTrace (prefixWord ++ tailWord_7408446) baseStart_7408446 baseEnd_7408446 := by
    simpa [prefixWord, tailWord_7408446, baseEnd_7408446] using wordTrace_append hprefix tailTrace_7408446
  have hstable : (prefixWord ++ tailWord_7408446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408446).length < 2 ^ (prefixWord ++ tailWord_7408446).sum := by decide
  have hdescent : baseEnd_7408446 < baseStart_7408446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408456 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_7408456 : Nat := 118140960795 + 7408456 * 2 ^ 59
def prefixEnd_7408456 : Nat := 4983230072969 + 3 ^ 40 * 7408456 * 2
def baseEnd_7408456 : Nat := 3804098835685571615529137

theorem tailTrace_7408456 : CollatzResearch.WordTrace tailWord_7408456 prefixEnd_7408456 3804098835685571615529137 := by
  unfold tailWord_7408456
  simp only [CollatzResearch.WordTrace]
  refine ⟨135104294424218325198566611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180139059232291100264755481 135104294424218325198566611)
  ·
    refine ⟨202656441636327487797849917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135104294424218325198566611 202656441636327487797849917)
    ·
      refine ⟨75996165613622807924193719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202656441636327487797849917 75996165613622807924193719)
      ·
        refine ⟨113994248420434211886290579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75996165613622807924193719 113994248420434211886290579)
        ·
          refine ⟨170991372630651317829435869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113994248420434211886290579 170991372630651317829435869)
          ·
            refine ⟨64121764736494244186038451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170991372630651317829435869 64121764736494244186038451)
            ·
              refine ⟨96182647104741366279057677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64121764736494244186038451 96182647104741366279057677)
              ·
                refine ⟨36068492664278012354646629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96182647104741366279057677 36068492664278012354646629)
                ·
                  refine ⟨6762842374552127316496243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36068492664278012354646629 6762842374552127316496243)
                  ·
                    refine ⟨10144263561828190974744365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762842374552127316496243 10144263561828190974744365)
                    ·
                      refine ⟨3804098835685571615529137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10144263561828190974744365 3804098835685571615529137)
                      ·
                        rfl

theorem cell23_7408456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_7408456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408456 prefixEnd_7408456 := by exact prefixLift 7408456
  have htrace : WordTrace (prefixWord ++ tailWord_7408456) baseStart_7408456 baseEnd_7408456 := by
    simpa [prefixWord, tailWord_7408456, baseEnd_7408456] using wordTrace_append hprefix tailTrace_7408456
  have hstable : (prefixWord ++ tailWord_7408456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408456).length < 2 ^ (prefixWord ++ tailWord_7408456).sum := by decide
  have hdescent : baseEnd_7408456 < baseStart_7408456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408457 : List Nat := [1, 2, 1, 1, 2, 6, 3, 2, 1, 2, 2]
def baseStart_7408457 : Nat := 118140960795 + 7408457 * 2 ^ 59
def prefixEnd_7408457 : Nat := 4983230072969 + 3 ^ 40 * 7408457 * 2
def baseEnd_7408457 : Nat := 3804099349166226111616633

theorem tailTrace_7408457 : CollatzResearch.WordTrace tailWord_7408457 prefixEnd_7408457 3804099349166226111616633 := by
  unfold tailWord_7408457
  simp only [CollatzResearch.WordTrace]
  refine ⟨270208625321433027567919625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180139083547622018378613083 270208625321433027567919625)
  ·
    refine ⟨202656468991074770675939719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270208625321433027567919625 202656468991074770675939719)
    ·
      refine ⟨303984703486612156013909579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202656468991074770675939719 303984703486612156013909579)
      ·
        refine ⟨455977055229918234020864369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303984703486612156013909579 455977055229918234020864369)
        ·
          refine ⟨341982791422438675515648277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455977055229918234020864369 341982791422438675515648277)
          ·
            refine ⟨16030443347926812914796013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 341982791422438675515648277 16030443347926812914796013)
            ·
              refine ⟨6011416255472554843048505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16030443347926812914796013 6011416255472554843048505)
              ·
                refine ⟨4508562191604416132286379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6011416255472554843048505 4508562191604416132286379)
                ·
                  refine ⟨6762843287406624198429569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508562191604416132286379 6762843287406624198429569)
                  ·
                    refine ⟨5072132465554968148822177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6762843287406624198429569 5072132465554968148822177)
                    ·
                      refine ⟨3804099349166226111616633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072132465554968148822177 3804099349166226111616633)
                      ·
                        rfl

theorem cell23_7408457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 2, 2].length) (baseStart_7408457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408457 prefixEnd_7408457 := by exact prefixLift 7408457
  have htrace : WordTrace (prefixWord ++ tailWord_7408457) baseStart_7408457 baseEnd_7408457 := by
    simpa [prefixWord, tailWord_7408457, baseEnd_7408457] using wordTrace_append hprefix tailTrace_7408457
  have hstable : (prefixWord ++ tailWord_7408457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408457).length < 2 ^ (prefixWord ++ tailWord_7408457).sum := by decide
  have hdescent : baseEnd_7408457 < baseStart_7408457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408473 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 3]
def baseStart_7408473 : Nat := 118140960795 + 7408473 * 2 ^ 59
def prefixEnd_7408473 : Nat := 4983230072969 + 3 ^ 40 * 7408473 * 2
def baseEnd_7408473 : Nat := 3804107564856698049016559

theorem tailTrace_7408473 : CollatzResearch.WordTrace tailWord_7408473 prefixEnd_7408473 3804107564856698049016559 := by
  unfold tailWord_7408473
  simp only [CollatzResearch.WordTrace]
  refine ⟨270209208889375062300502073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180139472592916708200334715 270209208889375062300502073)
  ·
    refine ⟨202656906667031296725376555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270209208889375062300502073 202656906667031296725376555)
    ·
      refine ⟨303985360000546945088064833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202656906667031296725376555 303985360000546945088064833)
      ·
        refine ⟨227989020000410208816048625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303985360000546945088064833 227989020000410208816048625)
        ·
          refine ⟨170991765000307656612036469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227989020000410208816048625 170991765000307656612036469)
          ·
            refine ⟨16030477968778842807378419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170991765000307656612036469 16030477968778842807378419)
            ·
              refine ⟨24045716953168264211067629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16030477968778842807378419 24045716953168264211067629)
              ·
                refine ⟨9017143857438099079150361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24045716953168264211067629 9017143857438099079150361)
                ·
                  refine ⟨6762857893078574309362771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9017143857438099079150361 6762857893078574309362771)
                  ·
                    refine ⟨10144286839617861464044157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6762857893078574309362771 10144286839617861464044157)
                    ·
                      refine ⟨3804107564856698049016559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10144286839617861464044157 3804107564856698049016559)
                      ·
                        rfl

theorem cell23_7408473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_7408473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408473 prefixEnd_7408473 := by exact prefixLift 7408473
  have htrace : WordTrace (prefixWord ++ tailWord_7408473) baseStart_7408473 baseEnd_7408473 := by
    simpa [prefixWord, tailWord_7408473, baseEnd_7408473] using wordTrace_append hprefix tailTrace_7408473
  have hstable : (prefixWord ++ tailWord_7408473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408473).length < 2 ^ (prefixWord ++ tailWord_7408473).sum := by decide
  have hdescent : baseEnd_7408473 < baseStart_7408473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408483 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 3, 3, 2]
def baseStart_7408483 : Nat := 118140960795 + 7408483 * 2 ^ 59
def prefixEnd_7408483 : Nat := 4983230072969 + 3 ^ 40 * 7408483 * 2
def baseEnd_7408483 : Nat := 3804112699663243009891513

theorem tailTrace_7408483 : CollatzResearch.WordTrace tailWord_7408483 prefixEnd_7408483 3804112699663243009891513 := by
  unfold tailWord_7408483
  simp only [CollatzResearch.WordTrace]
  refine ⟨270209573619338834008366103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180139715746225889338910735 270209573619338834008366103)
  ·
    refine ⟨405314360429008251012549155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270209573619338834008366103 405314360429008251012549155)
    ·
      refine ⟨607971540643512376518823733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405314360429008251012549155 607971540643512376518823733)
      ·
        refine ⟨56997331935329285298639725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 607971540643512376518823733 56997331935329285298639725)
        ·
          refine ⟨21373999475748481986989897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56997331935329285298639725 21373999475748481986989897)
          ·
            refine ⟨16030499606811361490242423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21373999475748481986989897 16030499606811361490242423)
            ·
              refine ⟨24045749410217042235363635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16030499606811361490242423 24045749410217042235363635)
              ·
                refine ⟨36068624115325563353045453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24045749410217042235363635 36068624115325563353045453)
                ·
                  refine ⟨13525734043247086257392045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36068624115325563353045453 13525734043247086257392045)
                  ·
                    refine ⟨5072150266217657346522017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13525734043247086257392045 5072150266217657346522017)
                    ·
                      refine ⟨3804112699663243009891513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072150266217657346522017 3804112699663243009891513)
                      ·
                        rfl

theorem cell23_7408483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_7408483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408483 prefixEnd_7408483 := by exact prefixLift 7408483
  have htrace : WordTrace (prefixWord ++ tailWord_7408483) baseStart_7408483 baseEnd_7408483 := by
    simpa [prefixWord, tailWord_7408483, baseEnd_7408483] using wordTrace_append hprefix tailTrace_7408483
  have hstable : (prefixWord ++ tailWord_7408483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408483).length < 2 ^ (prefixWord ++ tailWord_7408483).sum := by decide
  have hdescent : baseEnd_7408483 < baseStart_7408483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408496 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 3, 4, 2]
def baseStart_7408496 : Nat := 118140960795 + 7408496 * 2 ^ 59
def prefixEnd_7408496 : Nat := 4983230072969 + 3 ^ 40 * 7408496 * 2
def baseEnd_7408496 : Nat := 3804119374911751459028953

theorem tailTrace_7408496 : CollatzResearch.WordTrace tailWord_7408496 prefixEnd_7408496 3804119374911751459028953 := by
  unfold tailWord_7408496
  simp only [CollatzResearch.WordTrace]
  refine ⟨135105023884145868614294671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180140031845527824819059561 135105023884145868614294671)
  ·
    refine ⟨202657535826218802921442007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135105023884145868614294671 202657535826218802921442007)
    ·
      refine ⟨303986303739328204382163011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202657535826218802921442007 303986303739328204382163011)
      ·
        refine ⟨455979455608992306573244517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303986303739328204382163011 455979455608992306573244517)
        ·
          refine ⟨85496147926686057482483347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455979455608992306573244517 85496147926686057482483347)
          ·
            refine ⟨128244221890029086223725021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85496147926686057482483347 128244221890029086223725021)
            ·
              refine ⟨48091583208760907333896883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128244221890029086223725021 48091583208760907333896883)
              ·
                refine ⟨72137374813141361000845325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48091583208760907333896883 72137374813141361000845325)
                ·
                  refine ⟨27051515554928010375316997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72137374813141361000845325 27051515554928010375316997)
                  ·
                    refine ⟨5072159166549001945371937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27051515554928010375316997 5072159166549001945371937)
                    ·
                      refine ⟨3804119374911751459028953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072159166549001945371937 3804119374911751459028953)
                      ·
                        rfl

theorem cell23_7408496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 4, 2].length) (baseStart_7408496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408496 prefixEnd_7408496 := by exact prefixLift 7408496
  have htrace : WordTrace (prefixWord ++ tailWord_7408496) baseStart_7408496 baseEnd_7408496 := by
    simpa [prefixWord, tailWord_7408496, baseEnd_7408496] using wordTrace_append hprefix tailTrace_7408496
  have hstable : (prefixWord ++ tailWord_7408496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408496).length < 2 ^ (prefixWord ++ tailWord_7408496).sum := by decide
  have hdescent : baseEnd_7408496 < baseStart_7408496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408499 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 5]
def baseStart_7408499 : Nat := 118140960795 + 7408499 * 2 ^ 59
def prefixEnd_7408499 : Nat := 4983230072969 + 3 ^ 40 * 7408499 * 2
def baseEnd_7408499 : Nat := 3804120915353714947291439

theorem tailTrace_7408499 : CollatzResearch.WordTrace tailWord_7408499 prefixEnd_7408499 3804120915353714947291439 := by
  unfold tailWord_7408499
  simp only [CollatzResearch.WordTrace]
  refine ⟨270210157187280868740948551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180140104791520579160632367 270210157187280868740948551)
  ·
    refine ⟨405315235780921303111422827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270210157187280868740948551 405315235780921303111422827)
    ·
      refine ⟨607972853671381954667134241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405315235780921303111422827 607972853671381954667134241)
      ·
        refine ⟨455979640253536466000350681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607972853671381954667134241 455979640253536466000350681)
        ·
          refine ⟨341984730190152349500263011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455979640253536466000350681 341984730190152349500263011)
          ·
            refine ⟨512977095285228524250394517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341984730190152349500263011 512977095285228524250394517)
            ·
              refine ⟨24045801341495087074237243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 512977095285228524250394517 24045801341495087074237243)
              ·
                refine ⟨36068702012242630611355865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24045801341495087074237243 36068702012242630611355865)
                ·
                  refine ⟨27051526509181972958516899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36068702012242630611355865 27051526509181972958516899)
                  ·
                    refine ⟨40577289763772959437775349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27051526509181972958516899 40577289763772959437775349)
                    ·
                      refine ⟨3804120915353714947291439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40577289763772959437775349 3804120915353714947291439)
                      ·
                        rfl

theorem cell23_7408499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_7408499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408499 prefixEnd_7408499 := by exact prefixLift 7408499
  have htrace : WordTrace (prefixWord ++ tailWord_7408499) baseStart_7408499 baseEnd_7408499 := by
    simpa [prefixWord, tailWord_7408499, baseEnd_7408499] using wordTrace_append hprefix tailTrace_7408499
  have hstable : (prefixWord ++ tailWord_7408499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408499).length < 2 ^ (prefixWord ++ tailWord_7408499).sum := by decide
  have hdescent : baseEnd_7408499 < baseStart_7408499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408556 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 4, 5, 2]
def baseStart_7408556 : Nat := 118140960795 + 7408556 * 2 ^ 59
def prefixEnd_7408556 : Nat := 4983230072969 + 3 ^ 40 * 7408556 * 2
def baseEnd_7408556 : Nat := 3804150183751021224278677

theorem tailTrace_7408556 : CollatzResearch.WordTrace tailWord_7408556 prefixEnd_7408556 3804150183751021224278677 := by
  unfold tailWord_7408556
  simp only [CollatzResearch.WordTrace]
  refine ⟨135106118074037183737886761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180141490765382911650515681 135106118074037183737886761)
  ·
    refine ⟨101329588555527887803415071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135106118074037183737886761 101329588555527887803415071)
    ·
      refine ⟨151994382833291831705122607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101329588555527887803415071 151994382833291831705122607)
      ·
        refine ⟨227991574249937747557683911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151994382833291831705122607 227991574249937747557683911)
        ·
          refine ⟨341987361374906621336525867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227991574249937747557683911 341987361374906621336525867)
          ·
            refine ⟨512981042062359932004788801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341987361374906621336525867 512981042062359932004788801)
            ·
              refine ⟨384735781546769949003591601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512981042062359932004788801 384735781546769949003591601)
              ·
                refine ⟨288551836160077461752693701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384735781546769949003591601 288551836160077461752693701)
                ·
                  refine ⟨54103469280014524078630069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288551836160077461752693701 54103469280014524078630069)
                  ·
                    refine ⟨5072200245001361632371569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54103469280014524078630069 5072200245001361632371569)
                    ·
                      refine ⟨3804150183751021224278677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072200245001361632371569 3804150183751021224278677)
                      ·
                        rfl

theorem cell23_7408556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_7408556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408556 prefixEnd_7408556 := by exact prefixLift 7408556
  have htrace : WordTrace (prefixWord ++ tailWord_7408556) baseStart_7408556 baseEnd_7408556 := by
    simpa [prefixWord, tailWord_7408556, baseEnd_7408556] using wordTrace_append hprefix tailTrace_7408556
  have hstable : (prefixWord ++ tailWord_7408556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408556).length < 2 ^ (prefixWord ++ tailWord_7408556).sum := by decide
  have hdescent : baseEnd_7408556 < baseStart_7408556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408559 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_7408559 : Nat := 118140960795 + 7408559 * 2 ^ 59
def prefixEnd_7408559 : Nat := 4983230072969 + 3 ^ 40 * 7408559 * 2
def baseEnd_7408559 : Nat := 3804151724192984712541163

theorem tailTrace_7408559 : CollatzResearch.WordTrace tailWord_7408559 prefixEnd_7408559 3804151724192984712541163 := by
  unfold tailWord_7408559
  simp only [CollatzResearch.WordTrace]
  refine ⟨270212345567063498988132731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180141563711375665992088487 270212345567063498988132731)
  ·
    refine ⟨405318518350595248482199097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270212345567063498988132731 405318518350595248482199097)
    ·
      refine ⟨303988888762946436361649323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405318518350595248482199097 303988888762946436361649323)
      ·
        refine ⟨455983333144419654542473985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303988888762946436361649323 455983333144419654542473985)
        ·
          refine ⟨341987499858314740906855489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455983333144419654542473985 341987499858314740906855489)
          ·
            refine ⟨256490624893736055680141617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341987499858314740906855489 256490624893736055680141617)
            ·
              refine ⟨192367968670302041760106213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256490624893736055680141617 192367968670302041760106213)
              ·
                refine ⟨36068994125681632830019915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192367968670302041760106213 36068994125681632830019915)
                ·
                  refine ⟨54103491188522449245029873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36068994125681632830019915 54103491188522449245029873)
                  ·
                    refine ⟨40577618391391836933772405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54103491188522449245029873 40577618391391836933772405)
                    ·
                      refine ⟨3804151724192984712541163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40577618391391836933772405 3804151724192984712541163)
                      ·
                        rfl

theorem cell23_7408559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_7408559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408559 prefixEnd_7408559 := by exact prefixLift 7408559
  have htrace : WordTrace (prefixWord ++ tailWord_7408559) baseStart_7408559 baseEnd_7408559 := by
    simpa [prefixWord, tailWord_7408559, baseEnd_7408559] using wordTrace_append hprefix tailTrace_7408559
  have hstable : (prefixWord ++ tailWord_7408559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408559).length < 2 ^ (prefixWord ++ tailWord_7408559).sum := by decide
  have hdescent : baseEnd_7408559 < baseStart_7408559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408564 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_7408564 : Nat := 118140960795 + 7408564 * 2 ^ 59
def prefixEnd_7408564 : Nat := 4983230072969 + 3 ^ 40 * 7408564 * 2
def baseEnd_7408564 : Nat := 3804154291596257192978641

theorem tailTrace_7408564 : CollatzResearch.WordTrace tailWord_7408564 prefixEnd_7408564 3804154291596257192978641 := by
  unfold tailWord_7408564
  simp only [CollatzResearch.WordTrace]
  refine ⟨135106263966022692421032373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180141685288030256561376497 135106263966022692421032373)
  ·
    refine ⟨12666212246814627414471785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135106263966022692421032373 12666212246814627414471785)
    ·
      refine ⟨9499659185110970560853839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12666212246814627414471785 9499659185110970560853839)
      ·
        refine ⟨14249488777666455841280759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9499659185110970560853839 14249488777666455841280759)
        ·
          refine ⟨21374233166499683761921139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14249488777666455841280759 21374233166499683761921139)
          ·
            refine ⟨32061349749749525642881709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21374233166499683761921139 32061349749749525642881709)
            ·
              refine ⟨12023006156156072116080641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32061349749749525642881709 12023006156156072116080641)
              ·
                refine ⟨9017254617117054087060481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12023006156156072116080641 9017254617117054087060481)
                ·
                  refine ⟨6762940962837790565295361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9017254617117054087060481 6762940962837790565295361)
                  ·
                    refine ⟨5072205722128342923971521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6762940962837790565295361 5072205722128342923971521)
                    ·
                      refine ⟨3804154291596257192978641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072205722128342923971521 3804154291596257192978641)
                      ·
                        rfl

theorem cell23_7408564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_7408564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408564 prefixEnd_7408564 := by exact prefixLift 7408564
  have htrace : WordTrace (prefixWord ++ tailWord_7408564) baseStart_7408564 baseEnd_7408564 := by
    simpa [prefixWord, tailWord_7408564, baseEnd_7408564] using wordTrace_append hprefix tailTrace_7408564
  have hstable : (prefixWord ++ tailWord_7408564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408564).length < 2 ^ (prefixWord ++ tailWord_7408564).sum := by decide
  have hdescent : baseEnd_7408564 < baseStart_7408564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408599 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_7408599 : Nat := 118140960795 + 7408599 * 2 ^ 59
def prefixEnd_7408599 : Nat := 4983230072969 + 3 ^ 40 * 7408599 * 2
def baseEnd_7408599 : Nat := 3804172263419164556040979

theorem tailTrace_7408599 : CollatzResearch.WordTrace tailWord_7408599 prefixEnd_7408599 3804172263419164556040979 := by
  unfold tailWord_7408599
  simp only [CollatzResearch.WordTrace]
  refine ⟨270213804486918585819588851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180142536324612390546392567 270213804486918585819588851)
  ·
    refine ⟨405320706730377878729383277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270213804486918585819588851 405320706730377878729383277)
    ·
      refine ⟨151995265023891704523518729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405320706730377878729383277 151995265023891704523518729)
      ·
        refine ⟨113996448767918778392639047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151995265023891704523518729 113996448767918778392639047)
        ·
          refine ⟨170994673151878167588958571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113996448767918778392639047 170994673151878167588958571)
          ·
            refine ⟨256492009727817251383437857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170994673151878167588958571 256492009727817251383437857)
            ·
              refine ⟨192369007295862938537578393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256492009727817251383437857 192369007295862938537578393)
              ·
                refine ⟨144276755471897203903183795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192369007295862938537578393 144276755471897203903183795)
                ·
                  refine ⟨216415133207845805854775693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144276755471897203903183795 216415133207845805854775693)
                  ·
                    refine ⟨81155674952942177195540885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216415133207845805854775693 81155674952942177195540885)
                    ·
                      refine ⟨3804172263419164556040979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81155674952942177195540885 3804172263419164556040979)
                      ·
                        rfl

theorem cell23_7408599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_7408599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408599 prefixEnd_7408599 := by exact prefixLift 7408599
  have htrace : WordTrace (prefixWord ++ tailWord_7408599) baseStart_7408599 baseEnd_7408599 := by
    simpa [prefixWord, tailWord_7408599, baseEnd_7408599] using wordTrace_append hprefix tailTrace_7408599
  have hstable : (prefixWord ++ tailWord_7408599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408599).length < 2 ^ (prefixWord ++ tailWord_7408599).sum := by decide
  have hdescent : baseEnd_7408599 < baseStart_7408599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408623 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 3]
def baseStart_7408623 : Nat := 118140960795 + 7408623 * 2 ^ 59
def prefixEnd_7408623 : Nat := 4983230072969 + 3 ^ 40 * 7408623 * 2
def baseEnd_7408623 : Nat := 3804184586954872462140869

theorem tailTrace_7408623 : CollatzResearch.WordTrace tailWord_7408623 prefixEnd_7408623 3804184586954872462140869 := by
  unfold tailWord_7408623
  simp only [CollatzResearch.WordTrace]
  refine ⟨270214679838831637918462523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180143119892554425278975015 270214679838831637918462523)
  ·
    refine ⟨405322019758247456877693785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270214679838831637918462523 405322019758247456877693785)
    ·
      refine ⟨303991514818685592658270339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405322019758247456877693785 303991514818685592658270339)
      ·
        refine ⟨455987272228028388987405509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303991514818685592658270339 455987272228028388987405509)
        ·
          refine ⟨85497613542755322935138533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455987272228028388987405509 85497613542755322935138533)
          ·
            refine ⟨16030802539266623050338475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85497613542755322935138533 16030802539266623050338475)
            ·
              refine ⟨24046203808899934575507713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16030802539266623050338475 24046203808899934575507713)
              ·
                refine ⟨18034652856674950931630785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24046203808899934575507713 18034652856674950931630785)
                ·
                  refine ⟨13525989642506213198723089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18034652856674950931630785 13525989642506213198723089)
                  ·
                    refine ⟨10144492231879659899042317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13525989642506213198723089 10144492231879659899042317)
                    ·
                      refine ⟨3804184586954872462140869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10144492231879659899042317 3804184586954872462140869)
                      ·
                        rfl

theorem cell23_7408623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_7408623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408623 prefixEnd_7408623 := by exact prefixLift 7408623
  have htrace : WordTrace (prefixWord ++ tailWord_7408623) baseStart_7408623 baseEnd_7408623 := by
    simpa [prefixWord, tailWord_7408623, baseEnd_7408623] using wordTrace_append hprefix tailTrace_7408623
  have hstable : (prefixWord ++ tailWord_7408623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408623).length < 2 ^ (prefixWord ++ tailWord_7408623).sum := by decide
  have hdescent : baseEnd_7408623 < baseStart_7408623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408630 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_7408630 : Nat := 118140960795 + 7408630 * 2 ^ 59
def prefixEnd_7408630 : Nat := 4983230072969 + 3 ^ 40 * 7408630 * 2
def baseEnd_7408630 : Nat := 1268062727106484644917779

theorem tailTrace_7408630 : CollatzResearch.WordTrace tailWord_7408630 prefixEnd_7408630 1268062727106484644917779 := by
  unfold tailWord_7408630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888433446862892382122959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180143290099870852075978229 16888433446862892382122959)
  ·
    refine ⟨25332650170294338573184439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16888433446862892382122959 25332650170294338573184439)
    ·
      refine ⟨37998975255441507859776659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25332650170294338573184439 37998975255441507859776659)
      ·
        refine ⟨56998462883162261789664989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37998975255441507859776659 56998462883162261789664989)
        ·
          refine ⟨21374423581185848171124371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56998462883162261789664989 21374423581185848171124371)
          ·
            refine ⟨32061635371778772256686557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21374423581185848171124371 32061635371778772256686557)
            ·
              refine ⟨12023113264417039596257459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32061635371778772256686557 12023113264417039596257459)
              ·
                refine ⟨18034669896625559394386189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12023113264417039596257459 18034669896625559394386189)
                ·
                  refine ⟨6763001211234584772894821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18034669896625559394386189 6763001211234584772894821)
                  ·
                    refine ⟨1268062727106484644917779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6763001211234584772894821 1268062727106484644917779)
                    ·
                      rfl

theorem cell23_7408630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_7408630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408630 prefixEnd_7408630 := by exact prefixLift 7408630
  have htrace : WordTrace (prefixWord ++ tailWord_7408630) baseStart_7408630 baseEnd_7408630 := by
    simpa [prefixWord, tailWord_7408630, baseEnd_7408630] using wordTrace_append hprefix tailTrace_7408630
  have hstable : (prefixWord ++ tailWord_7408630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408630).length < 2 ^ (prefixWord ++ tailWord_7408630).sum := by decide
  have hdescent : baseEnd_7408630 < baseStart_7408630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408639 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 11]
def baseStart_7408639 : Nat := 118140960795 + 7408639 * 2 ^ 59
def prefixEnd_7408639 : Nat := 4983230072969 + 3 ^ 40 * 7408639 * 2
def baseEnd_7408639 : Nat := 1268064267548448133180265

theorem tailTrace_7408639 : CollatzResearch.WordTrace tailWord_7408639 prefixEnd_7408639 1268064267548448133180265 := by
  unfold tailWord_7408639
  simp only [CollatzResearch.WordTrace]
  refine ⟨270215263406773672651044971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180143508937849115100696647 270215263406773672651044971)
  ·
    refine ⟨405322895110160508976567457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270215263406773672651044971 405322895110160508976567457)
    ·
      refine ⟨303992171332620381732425593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405322895110160508976567457 303992171332620381732425593)
      ·
        refine ⟨227994128499465286299319195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303992171332620381732425593 227994128499465286299319195)
        ·
          refine ⟨341991192749197929448978793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227994128499465286299319195 341991192749197929448978793)
          ·
            refine ⟨256493394561898447086734095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341991192749197929448978793 256493394561898447086734095)
            ·
              refine ⟨384740091842847670630101143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256493394561898447086734095 384740091842847670630101143)
              ·
                refine ⟨577110137764271505945151715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384740091842847670630101143 577110137764271505945151715)
                ·
                  refine ⟨865665206646407258917727573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577110137764271505945151715 865665206646407258917727573)
                  ·
                    refine ⟨1268064267548448133180265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 865665206646407258917727573 1268064267548448133180265)
                    ·
                      rfl

theorem cell23_7408639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_7408639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408639 prefixEnd_7408639 := by exact prefixLift 7408639
  have htrace : WordTrace (prefixWord ++ tailWord_7408639) baseStart_7408639 baseEnd_7408639 := by
    simpa [prefixWord, tailWord_7408639, baseEnd_7408639] using wordTrace_append hprefix tailTrace_7408639
  have hstable : (prefixWord ++ tailWord_7408639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408639).length < 2 ^ (prefixWord ++ tailWord_7408639).sum := by decide
  have hdescent : baseEnd_7408639 < baseStart_7408639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408693 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_7408693 : Nat := 118140960795 + 7408693 * 2 ^ 59
def prefixEnd_7408693 : Nat := 4983230072969 + 3 ^ 40 * 7408693 * 2
def baseEnd_7408693 : Nat := 3804220530600687188265547

theorem tailTrace_7408693 : CollatzResearch.WordTrace tailWord_7408693 prefixEnd_7408693 3804220530600687188265547 := by
  unfold tailWord_7408693
  simp only [CollatzResearch.WordTrace]
  refine ⟨270217232948578039873510733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180144821965718693249007155 270217232948578039873510733)
  ·
    refine ⟨101331462355716764952566525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270217232948578039873510733 101331462355716764952566525)
    ·
      refine ⟨37999298383393786857212447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101331462355716764952566525 37999298383393786857212447)
      ·
        refine ⟨56998947575090680285818671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37999298383393786857212447 56998947575090680285818671)
        ·
          refine ⟨85498421362636020428728007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56998947575090680285818671 85498421362636020428728007)
          ·
            refine ⟨128247632043954030643092011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85498421362636020428728007 128247632043954030643092011)
            ·
              refine ⟨192371448065931045964638017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128247632043954030643092011 192371448065931045964638017)
              ·
                refine ⟨144278586049448284473478513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192371448065931045964638017 144278586049448284473478513)
                ·
                  refine ⟨108208939537086213355108885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144278586049448284473478513 108208939537086213355108885)
                  ·
                    refine ⟨5072294040800916251020729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108208939537086213355108885 5072294040800916251020729)
                    ·
                      refine ⟨3804220530600687188265547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072294040800916251020729 3804220530600687188265547)
                      ·
                        rfl

theorem cell23_7408693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_7408693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408693 prefixEnd_7408693 := by exact prefixLift 7408693
  have htrace : WordTrace (prefixWord ++ tailWord_7408693) baseStart_7408693 baseEnd_7408693 := by
    simpa [prefixWord, tailWord_7408693, baseEnd_7408693] using wordTrace_append hprefix tailTrace_7408693
  have hstable : (prefixWord ++ tailWord_7408693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408693).length < 2 ^ (prefixWord ++ tailWord_7408693).sum := by decide
  have hdescent : baseEnd_7408693 < baseStart_7408693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408753 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 2, 7, 2]
def baseStart_7408753 : Nat := 118140960795 + 7408753 * 2 ^ 59
def prefixEnd_7408753 : Nat := 4983230072969 + 3 ^ 40 * 7408753 * 2
def baseEnd_7408753 : Nat := 3804251339439956953515271

theorem tailTrace_7408753 : CollatzResearch.WordTrace tailWord_7408753 prefixEnd_7408753 3804251339439956953515271 := by
  unfold tailWord_7408753
  simp only [CollatzResearch.WordTrace]
  refine ⟨270219421328360670120694913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180146280885573780080463275 270219421328360670120694913)
  ·
    refine ⟨202664565996270502590521185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270219421328360670120694913 202664565996270502590521185)
    ·
      refine ⟨151998424497202876942890889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202664565996270502590521185 151998424497202876942890889)
      ·
        refine ⟨113998818372902157707168167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151998424497202876942890889 113998818372902157707168167)
        ·
          refine ⟨170998227559353236560752251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113998818372902157707168167 170998227559353236560752251)
          ·
            refine ⟨256497341339029854841128377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170998227559353236560752251 256497341339029854841128377)
            ·
              refine ⟨192373006004272391130846283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256497341339029854841128377 192373006004272391130846283)
              ·
                refine ⟨288559509006408586696269425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192373006004272391130846283 288559509006408586696269425)
                ·
                  refine ⟨216419631754806440022202069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288559509006408586696269425 216419631754806440022202069)
                  ·
                    refine ⟨5072335119253275938020361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 216419631754806440022202069 5072335119253275938020361)
                    ·
                      refine ⟨3804251339439956953515271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072335119253275938020361 3804251339439956953515271)
                      ·
                        rfl

theorem cell23_7408753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_7408753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408753 prefixEnd_7408753 := by exact prefixLift 7408753
  have htrace : WordTrace (prefixWord ++ tailWord_7408753) baseStart_7408753 baseEnd_7408753 := by
    simpa [prefixWord, tailWord_7408753, baseEnd_7408753] using wordTrace_append hprefix tailTrace_7408753
  have hstable : (prefixWord ++ tailWord_7408753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408753).length < 2 ^ (prefixWord ++ tailWord_7408753).sum := by decide
  have hdescent : baseEnd_7408753 < baseStart_7408753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408760 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_7408760 : Nat := 118140960795 + 7408760 * 2 ^ 59
def prefixEnd_7408760 : Nat := 4983230072969 + 3 ^ 40 * 7408760 * 2
def baseEnd_7408760 : Nat := 3804254933804538426127739

theorem tailTrace_7408760 : CollatzResearch.WordTrace tailWord_7408760 prefixEnd_7408760 3804254933804538426127739 := by
  unfold tailWord_7408760
  simp only [CollatzResearch.WordTrace]
  refine ⟨135109838319667655158099867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180146451092890206877466489 135109838319667655158099867)
  ·
    refine ⟨202664757479501482737149801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135109838319667655158099867 202664757479501482737149801)
    ·
      refine ⟨151998568109626112052862351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202664757479501482737149801 151998568109626112052862351)
      ·
        refine ⟨227997852164439168079293527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151998568109626112052862351 227997852164439168079293527)
        ·
          refine ⟨341996778246658752118940291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227997852164439168079293527 341996778246658752118940291)
          ·
            refine ⟨512995167369988128178410437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341996778246658752118940291 512995167369988128178410437)
            ·
              refine ⟨96186593881872774033451957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 512995167369988128178410437 96186593881872774033451957)
              ·
                refine ⟨9017493176425572565636121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96186593881872774033451957 9017493176425572565636121)
                ·
                  refine ⟨6763119882319179424227091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9017493176425572565636121 6763119882319179424227091)
                  ·
                    refine ⟨10144679823478769136340637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6763119882319179424227091 10144679823478769136340637)
                    ·
                      refine ⟨3804254933804538426127739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10144679823478769136340637 3804254933804538426127739)
                      ·
                        rfl

theorem cell23_7408760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_7408760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408760 prefixEnd_7408760 := by exact prefixLift 7408760
  have htrace : WordTrace (prefixWord ++ tailWord_7408760) baseStart_7408760 baseEnd_7408760 := by
    simpa [prefixWord, tailWord_7408760, baseEnd_7408760] using wordTrace_append hprefix tailTrace_7408760
  have hstable : (prefixWord ++ tailWord_7408760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408760).length < 2 ^ (prefixWord ++ tailWord_7408760).sum := by decide
  have hdescent : baseEnd_7408760 < baseStart_7408760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408816 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_7408816 : Nat := 118140960795 + 7408816 * 2 ^ 59
def prefixEnd_7408816 : Nat := 4983230072969 + 3 ^ 40 * 7408816 * 2
def baseEnd_7408816 : Nat := 3804283688721190207027481

theorem tailTrace_7408816 : CollatzResearch.WordTrace tailWord_7408816 prefixEnd_7408816 3804283688721190207027481 := by
  unfold tailWord_7408816
  simp only [CollatzResearch.WordTrace]
  refine ⟨135110859563566215940119151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180147812751421621253492201 135110859563566215940119151)
  ·
    refine ⟨202666289345349323910178727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135110859563566215940119151 202666289345349323910178727)
    ·
      refine ⟨303999434018023985865268091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202666289345349323910178727 303999434018023985865268091)
      ·
        refine ⟨455999151027035978797902137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303999434018023985865268091 455999151027035978797902137)
        ·
          refine ⟨341999363270276984098426603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455999151027035978797902137 341999363270276984098426603)
          ·
            refine ⟨512999044905415476147639905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341999363270276984098426603 512999044905415476147639905)
            ·
              refine ⟨384749283679061607110729929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512999044905415476147639905 384749283679061607110729929)
              ·
                refine ⟨288561962759296205333047447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384749283679061607110729929 288561962759296205333047447)
                ·
                  refine ⟨432842944138944307999571171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288561962759296205333047447 432842944138944307999571171)
                  ·
                    refine ⟨649264416208416461999356757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 432842944138944307999571171 649264416208416461999356757)
                    ·
                      refine ⟨3804283688721190207027481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 649264416208416461999356757 3804283688721190207027481)
                      ·
                        rfl

theorem cell23_7408816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_7408816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408816 prefixEnd_7408816 := by exact prefixLift 7408816
  have htrace : WordTrace (prefixWord ++ tailWord_7408816) baseStart_7408816 baseEnd_7408816 := by
    simpa [prefixWord, tailWord_7408816, baseEnd_7408816] using wordTrace_append hprefix tailTrace_7408816
  have hstable : (prefixWord ++ tailWord_7408816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408816).length < 2 ^ (prefixWord ++ tailWord_7408816).sum := by decide
  have hdescent : baseEnd_7408816 < baseStart_7408816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408850 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_7408850 : Nat := 118140960795 + 7408850 * 2 ^ 59
def prefixEnd_7408850 : Nat := 4983230072969 + 3 ^ 40 * 7408850 * 2
def baseEnd_7408850 : Nat := 3804301147063443074002325

theorem tailTrace_7408850 : CollatzResearch.WordTrace tailWord_7408850 prefixEnd_7408850 3804301147063443074002325 := by
  unfold tailWord_7408850
  simp only [CollatzResearch.WordTrace]
  refine ⟨67555739802252313921744001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180148639472672837124650669 67555739802252313921744001)
  ·
    refine ⟨50666804851689235441308001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67555739802252313921744001 50666804851689235441308001)
    ·
      refine ⟨38000103638766926580981001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50666804851689235441308001 38000103638766926580981001)
      ·
        refine ⟨28500077729075194935735751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38000103638766926580981001 28500077729075194935735751)
        ·
          refine ⟨42750116593612792403603627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28500077729075194935735751 42750116593612792403603627)
          ·
            refine ⟨64125174890419188605405441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42750116593612792403603627 64125174890419188605405441)
            ·
              refine ⟨48093881167814391454054081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64125174890419188605405441 48093881167814391454054081)
              ·
                refine ⟨36070410875860793590540561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48093881167814391454054081 36070410875860793590540561)
                ·
                  refine ⟨27052808156895595192905421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36070410875860793590540561 27052808156895595192905421)
                  ·
                    refine ⟨10144803058835848197339533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27052808156895595192905421 10144803058835848197339533)
                    ·
                      refine ⟨3804301147063443074002325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10144803058835848197339533 3804301147063443074002325)
                      ·
                        rfl

theorem cell23_7408850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_7408850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408850 prefixEnd_7408850 := by exact prefixLift 7408850
  have htrace : WordTrace (prefixWord ++ tailWord_7408850) baseStart_7408850 baseEnd_7408850 := by
    simpa [prefixWord, tailWord_7408850, baseEnd_7408850] using wordTrace_append hprefix tailTrace_7408850
  have hstable : (prefixWord ++ tailWord_7408850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408850).length < 2 ^ (prefixWord ++ tailWord_7408850).sum := by decide
  have hdescent : baseEnd_7408850 < baseStart_7408850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408863 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_7408863 : Nat := 118140960795 + 7408863 * 2 ^ 59
def prefixEnd_7408863 : Nat := 4983230072969 + 3 ^ 40 * 7408863 * 2
def baseEnd_7408863 : Nat := 3804307822311951523139765

theorem tailTrace_7408863 : CollatzResearch.WordTrace tailWord_7408863 prefixEnd_7408863 3804307822311951523139765 := by
  unfold tailWord_7408863
  simp only [CollatzResearch.WordTrace]
  refine ⟨270223433357962158907199243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180148955571974772604799495 270223433357962158907199243)
  ·
    refine ⟨405335150036943238360798865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270223433357962158907199243 405335150036943238360798865)
    ·
      refine ⟨304001362527707428770599149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405335150036943238360798865 304001362527707428770599149)
      ·
        refine ⟨114000510947890285788974681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304001362527707428770599149 114000510947890285788974681)
        ·
          refine ⟨85500383210917714341731011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114000510947890285788974681 85500383210917714341731011)
          ·
            refine ⟨128250574816376571512596517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85500383210917714341731011 128250574816376571512596517)
            ·
              refine ⟨24046982778070607158611847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128250574816376571512596517 24046982778070607158611847)
              ·
                refine ⟨36070474167105910737917771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24046982778070607158611847 36070474167105910737917771)
                ·
                  refine ⟨54105711250658866106876657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36070474167105910737917771 54105711250658866106876657)
                  ·
                    refine ⟨40579283437994149580157493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54105711250658866106876657 40579283437994149580157493)
                    ·
                      refine ⟨3804307822311951523139765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40579283437994149580157493 3804307822311951523139765)
                      ·
                        rfl

theorem cell23_7408863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_7408863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408863 prefixEnd_7408863 := by exact prefixLift 7408863
  have htrace : WordTrace (prefixWord ++ tailWord_7408863) baseStart_7408863 baseEnd_7408863 := by
    simpa [prefixWord, tailWord_7408863, baseEnd_7408863] using wordTrace_append hprefix tailTrace_7408863
  have hstable : (prefixWord ++ tailWord_7408863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408863).length < 2 ^ (prefixWord ++ tailWord_7408863).sum := by decide
  have hdescent : baseEnd_7408863 < baseStart_7408863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408890 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2]
def baseStart_7408890 : Nat := 118140960795 + 7408890 * 2 ^ 59
def prefixEnd_7408890 : Nat := 4983230072969 + 3 ^ 40 * 7408890 * 2
def baseEnd_7408890 : Nat := 3804321686289622917502141

theorem tailTrace_7408890 : CollatzResearch.WordTrace tailWord_7408890 prefixEnd_7408890 3804321686289622917502141 := by
  unfold tailWord_7408890
  simp only [CollatzResearch.WordTrace]
  refine ⟨67556104532216085629608031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180149612085909561678954749 67556104532216085629608031)
  ·
    refine ⟨101334156798324128444412047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67556104532216085629608031 101334156798324128444412047)
    ·
      refine ⟨152001235197486192666618071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101334156798324128444412047 152001235197486192666618071)
      ·
        refine ⟨228001852796229288999927107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152001235197486192666618071 228001852796229288999927107)
        ·
          refine ⟨342002779194343933499890661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228001852796229288999927107 342002779194343933499890661)
          ·
            refine ⟨64125521098939487531229499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342002779194343933499890661 64125521098939487531229499)
            ·
              refine ⟨96188281648409231296844249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64125521098939487531229499 96188281648409231296844249)
              ·
                refine ⟨72141211236306923472633187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96188281648409231296844249 72141211236306923472633187)
                ·
                  refine ⟨108211816854460385208949781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72141211236306923472633187 108211816854460385208949781)
                  ·
                    refine ⟨5072428915052830556669521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108211816854460385208949781 5072428915052830556669521)
                    ·
                      refine ⟨3804321686289622917502141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072428915052830556669521 3804321686289622917502141)
                      ·
                        rfl

theorem cell23_7408890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_7408890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408890 prefixEnd_7408890 := by exact prefixLift 7408890
  have htrace : WordTrace (prefixWord ++ tailWord_7408890) baseStart_7408890 baseEnd_7408890 := by
    simpa [prefixWord, tailWord_7408890, baseEnd_7408890] using wordTrace_append hprefix tailTrace_7408890
  have hstable : (prefixWord ++ tailWord_7408890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408890).length < 2 ^ (prefixWord ++ tailWord_7408890).sum := by decide
  have hdescent : baseEnd_7408890 < baseStart_7408890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408913 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 8]
def baseStart_7408913 : Nat := 118140960795 + 7408913 * 2 ^ 59
def prefixEnd_7408913 : Nat := 4983230072969 + 3 ^ 40 * 7408913 * 2
def baseEnd_7408913 : Nat := 422703721816075147501615

theorem tailTrace_7408913 : CollatzResearch.WordTrace tailWord_7408913 prefixEnd_7408913 422703721816075147501615 := by
  unfold tailWord_7408913
  simp only [CollatzResearch.WordTrace]
  refine ⟨270225257007781017446519393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180150171338520678297679595 270225257007781017446519393)
  ·
    refine ⟨202668942755835763084889545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270225257007781017446519393 202668942755835763084889545)
    ·
      refine ⟨152001707066876822313667159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202668942755835763084889545 152001707066876822313667159)
      ·
        refine ⟨228002560600315233470500739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152001707066876822313667159 228002560600315233470500739)
        ·
          refine ⟨342003840900472850205751109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228002560600315233470500739 342003840900472850205751109)
          ·
            refine ⟨64125720168838659413578333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342003840900472850205751109 64125720168838659413578333)
            ·
              refine ⟨24047145063314497280091875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64125720168838659413578333 24047145063314497280091875)
              ·
                refine ⟨36070717594971745920137813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24047145063314497280091875 36070717594971745920137813)
                ·
                  refine ⟨422703721816075147501615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36070717594971745920137813 422703721816075147501615)
                  ·
                    rfl

theorem cell23_7408913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 8].length) (baseStart_7408913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408913 prefixEnd_7408913 := by exact prefixLift 7408913
  have htrace : WordTrace (prefixWord ++ tailWord_7408913) baseStart_7408913 baseEnd_7408913 := by
    simpa [prefixWord, tailWord_7408913, baseEnd_7408913] using wordTrace_append hprefix tailTrace_7408913
  have hstable : (prefixWord ++ tailWord_7408913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408913).length < 2 ^ (prefixWord ++ tailWord_7408913).sum := by decide
  have hdescent : baseEnd_7408913 < baseStart_7408913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408960 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 1, 5]
def baseStart_7408960 : Nat := 118140960795 + 7408960 * 2 ^ 59
def prefixEnd_7408960 : Nat := 4983230072969 + 3 ^ 40 * 7408960 * 2
def baseEnd_7408960 : Nat := 1268119209978479214542273

theorem tailTrace_7408960 : CollatzResearch.WordTrace tailWord_7408960 prefixEnd_7408960 1268119209978479214542273 := by
  unfold tailWord_7408960
  simp only [CollatzResearch.WordTrace]
  refine ⟨135113485619305372236740167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180151314159073829648986889 135113485619305372236740167)
  ·
    refine ⟨202670228428958058355110251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135113485619305372236740167 202670228428958058355110251)
    ·
      refine ⟨304005342643437087532665377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202670228428958058355110251 304005342643437087532665377)
      ·
        refine ⟨228004006982577815649499033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304005342643437087532665377 228004006982577815649499033)
        ·
          refine ⟨171003005236933361737124275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228004006982577815649499033 171003005236933361737124275)
          ·
            refine ⟨256504507855400042605686413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171003005236933361737124275 256504507855400042605686413)
            ·
              refine ⟨96189190445775015977132405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256504507855400042605686413 96189190445775015977132405)
              ·
                refine ⟨9017736604291407747856163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96189190445775015977132405 9017736604291407747856163)
                ·
                  refine ⟨13526604906437111621784245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9017736604291407747856163 13526604906437111621784245)
                  ·
                    refine ⟨1268119209978479214542273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13526604906437111621784245 1268119209978479214542273)
                    ·
                      rfl

theorem cell23_7408960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_7408960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408960 prefixEnd_7408960 := by exact prefixLift 7408960
  have htrace : WordTrace (prefixWord ++ tailWord_7408960) baseStart_7408960 baseEnd_7408960 := by
    simpa [prefixWord, tailWord_7408960, baseEnd_7408960] using wordTrace_append hprefix tailTrace_7408960
  have hstable : (prefixWord ++ tailWord_7408960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408960).length < 2 ^ (prefixWord ++ tailWord_7408960).sum := by decide
  have hdescent : baseEnd_7408960 < baseStart_7408960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7408967 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_7408967 : Nat := 118140960795 + 7408967 * 2 ^ 59
def prefixEnd_7408967 : Nat := 4983230072969 + 3 ^ 40 * 7408967 * 2
def baseEnd_7408967 : Nat := 3804361224300019116239287

theorem tailTrace_7408967 : CollatzResearch.WordTrace tailWord_7408967 prefixEnd_7408967 3804361224300019116239287 := by
  unfold tailWord_7408967
  simp only [CollatzResearch.WordTrace]
  refine ⟨270227226549585384668985155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180151484366390256445990103 270227226549585384668985155)
  ·
    refine ⟨405340839824378077003477733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270227226549585384668985155 405340839824378077003477733)
    ·
      refine ⟨76001407467070889438152075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405340839824378077003477733 76001407467070889438152075)
      ·
        refine ⟨114002111200606334157228113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76001407467070889438152075 114002111200606334157228113)
        ·
          refine ⟨85501583400454750617921085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114002111200606334157228113 85501583400454750617921085)
          ·
            refine ⟨32063093775170531481720407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85501583400454750617921085 32063093775170531481720407)
            ·
              refine ⟨48094640662755797222580611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32063093775170531481720407 48094640662755797222580611)
              ·
                refine ⟨72141960994133695833870917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48094640662755797222580611 72141960994133695833870917)
                ·
                  refine ⟨13526617686400067968850797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72141960994133695833870917 13526617686400067968850797)
                  ·
                    refine ⟨5072481632400025488319049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13526617686400067968850797 5072481632400025488319049)
                    ·
                      refine ⟨3804361224300019116239287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072481632400025488319049 3804361224300019116239287)
                      ·
                        rfl

theorem cell23_7408967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_7408967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7408967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7408967 prefixEnd_7408967 := by exact prefixLift 7408967
  have htrace : WordTrace (prefixWord ++ tailWord_7408967) baseStart_7408967 baseEnd_7408967 := by
    simpa [prefixWord, tailWord_7408967, baseEnd_7408967] using wordTrace_append hprefix tailTrace_7408967
  have hstable : (prefixWord ++ tailWord_7408967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7408967).length < 2 ^ (prefixWord ++ tailWord_7408967).sum := by decide
  have hdescent : baseEnd_7408967 < baseStart_7408967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7408967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409017 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 3]
def baseStart_7409017 : Nat := 118140960795 + 7409017 * 2 ^ 59
def prefixEnd_7409017 : Nat := 4983230072969 + 3 ^ 40 * 7409017 * 2
def baseEnd_7409017 : Nat := 3804386898332743920614057

theorem tailTrace_7409017 : CollatzResearch.WordTrace tailWord_7409017 prefixEnd_7409017 3804386898332743920614057 := by
  unfold tailWord_7409017
  simp only [CollatzResearch.WordTrace]
  refine ⟨270229050199404243208305305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180152700132936162138870203 270229050199404243208305305)
  ·
    refine ⟨202671787649553182406228979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270229050199404243208305305 202671787649553182406228979)
    ·
      refine ⟨304007681474329773609343469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202671787649553182406228979 304007681474329773609343469)
      ·
        refine ⟨114002880552873665103503801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304007681474329773609343469 114002880552873665103503801)
        ·
          refine ⟨85502160414655248827627851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114002880552873665103503801 85502160414655248827627851)
          ·
            refine ⟨128253240621982873241441777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85502160414655248827627851 128253240621982873241441777)
            ·
              refine ⟨96189930466487154931081333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128253240621982873241441777 96189930466487154931081333)
              ·
                refine ⟨9017805981233170774788875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96189930466487154931081333 9017805981233170774788875)
                ·
                  refine ⟨13526708971849756162183313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9017805981233170774788875 13526708971849756162183313)
                  ·
                    refine ⟨10145031728887317121637485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13526708971849756162183313 10145031728887317121637485)
                    ·
                      refine ⟨3804386898332743920614057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10145031728887317121637485 3804386898332743920614057)
                      ·
                        rfl

theorem cell23_7409017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_7409017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409017 prefixEnd_7409017 := by exact prefixLift 7409017
  have htrace : WordTrace (prefixWord ++ tailWord_7409017) baseStart_7409017 baseEnd_7409017 := by
    simpa [prefixWord, tailWord_7409017, baseEnd_7409017] using wordTrace_append hprefix tailTrace_7409017
  have hstable : (prefixWord ++ tailWord_7409017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409017).length < 2 ^ (prefixWord ++ tailWord_7409017).sum := by decide
  have hdescent : baseEnd_7409017 < baseStart_7409017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409025 : List Nat := [1, 2, 4, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_7409025 : Nat := 118140960795 + 7409025 * 2 ^ 59
def prefixEnd_7409025 : Nat := 4983230072969 + 3 ^ 40 * 7409025 * 2
def baseEnd_7409025 : Nat := 3804391006177979889314021

theorem tailTrace_7409025 : CollatzResearch.WordTrace tailWord_7409025 prefixEnd_7409025 3804391006177979889314021 := by
  unfold tailWord_7409025
  simp only [CollatzResearch.WordTrace]
  refine ⟨270229341983375260574596529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180152894655583507049731019 270229341983375260574596529)
  ·
    refine ⟨202672006487531445430947397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270229341983375260574596529 202672006487531445430947397)
    ·
      refine ⟨38001001216412146018302637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202672006487531445430947397 38001001216412146018302637)
      ·
        refine ⟨14250375456154554756863489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38001001216412146018302637 14250375456154554756863489)
        ·
          refine ⟨10687781592115916067647617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14250375456154554756863489 10687781592115916067647617)
          ·
            refine ⟨8015836194086937050735713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10687781592115916067647617 8015836194086937050735713)
            ·
              refine ⟨6011877145565202788051785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8015836194086937050735713 6011877145565202788051785)
              ·
                refine ⟨4508907859173902091038839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6011877145565202788051785 4508907859173902091038839)
                ·
                  refine ⟨6763361788760853136558259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508907859173902091038839 6763361788760853136558259)
                  ·
                    refine ⟨10145042683141279704837389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6763361788760853136558259 10145042683141279704837389)
                    ·
                      refine ⟨3804391006177979889314021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10145042683141279704837389 3804391006177979889314021)
                      ·
                        rfl

theorem cell23_7409025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_7409025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409025 prefixEnd_7409025 := by exact prefixLift 7409025
  have htrace : WordTrace (prefixWord ++ tailWord_7409025) baseStart_7409025 baseEnd_7409025 := by
    simpa [prefixWord, tailWord_7409025, baseEnd_7409025] using wordTrace_append hprefix tailTrace_7409025
  have hstable : (prefixWord ++ tailWord_7409025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409025).length < 2 ^ (prefixWord ++ tailWord_7409025).sum := by decide
  have hdescent : baseEnd_7409025 < baseStart_7409025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409044 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_7409044 : Nat := 118140960795 + 7409044 * 2 ^ 59
def prefixEnd_7409044 : Nat := 4983230072969 + 3 ^ 40 * 7409044 * 2
def baseEnd_7409044 : Nat := 3804400762310415314976433

theorem tailTrace_7409044 : CollatzResearch.WordTrace tailWord_7409044 prefixEnd_7409044 3804400762310415314976433 := by
  unfold tailWord_7409044
  simp only [CollatzResearch.WordTrace]
  refine ⟨135115017485153213409769093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180153356646870951213025457 135115017485153213409769093)
  ·
    refine ⟨25334065778466227514331705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135115017485153213409769093 25334065778466227514331705)
    ·
      refine ⟨19000549333849670635748779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25334065778466227514331705 19000549333849670635748779)
      ·
        refine ⟨28500824000774505953623169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19000549333849670635748779 28500824000774505953623169)
        ·
          refine ⟨21375618000580879465217377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28500824000774505953623169 21375618000580879465217377)
          ·
            refine ⟨16031713500435659598913033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21375618000580879465217377 16031713500435659598913033)
            ·
              refine ⟨12023785125326744699184775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16031713500435659598913033 12023785125326744699184775)
              ·
                refine ⟨18035677687990117048777163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12023785125326744699184775 18035677687990117048777163)
                ·
                  refine ⟨27053516531985175573165745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18035677687990117048777163 27053516531985175573165745)
                  ·
                    refine ⟨20290137398988881679874309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27053516531985175573165745 20290137398988881679874309)
                    ·
                      refine ⟨3804400762310415314976433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20290137398988881679874309 3804400762310415314976433)
                      ·
                        rfl

theorem cell23_7409044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_7409044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409044 prefixEnd_7409044 := by exact prefixLift 7409044
  have htrace : WordTrace (prefixWord ++ tailWord_7409044) baseStart_7409044 baseEnd_7409044 := by
    simpa [prefixWord, tailWord_7409044, baseEnd_7409044] using wordTrace_append hprefix tailTrace_7409044
  have hstable : (prefixWord ++ tailWord_7409044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409044).length < 2 ^ (prefixWord ++ tailWord_7409044).sum := by decide
  have hdescent : baseEnd_7409044 < baseStart_7409044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409047 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_7409047 : Nat := 118140960795 + 7409047 * 2 ^ 59
def prefixEnd_7409047 : Nat := 4983230072969 + 3 ^ 40 * 7409047 * 2
def baseEnd_7409047 : Nat := 3804402302752378803238919

theorem tailTrace_7409047 : CollatzResearch.WordTrace tailWord_7409047 prefixEnd_7409047 3804402302752378803238919 := by
  unfold tailWord_7409047
  simp only [CollatzResearch.WordTrace]
  refine ⟨270230144389295558331897395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180153429592863705554598263 270230144389295558331897395)
  ·
    refine ⟨405345216583943337497846093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270230144389295558331897395 405345216583943337497846093)
    ·
      refine ⟨152004456218978751561692285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405345216583943337497846093 152004456218978751561692285)
      ·
        refine ⟨57001671082117031835634607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152004456218978751561692285 57001671082117031835634607)
        ·
          refine ⟨85502506623175547753451911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57001671082117031835634607 85502506623175547753451911)
          ·
            refine ⟨128253759934763321630177867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85502506623175547753451911 128253759934763321630177867)
            ·
              refine ⟨192380639902144982445266801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128253759934763321630177867 192380639902144982445266801)
              ·
                refine ⟨144285479926608736833950101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192380639902144982445266801 144285479926608736833950101)
                ·
                  refine ⟨6763381871559784539091411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144285479926608736833950101 6763381871559784539091411)
                  ·
                    refine ⟨10145072807339676808637117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6763381871559784539091411 10145072807339676808637117)
                    ·
                      refine ⟨3804402302752378803238919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10145072807339676808637117 3804402302752378803238919)
                      ·
                        rfl

theorem cell23_7409047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_7409047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409047 prefixEnd_7409047 := by exact prefixLift 7409047
  have htrace : WordTrace (prefixWord ++ tailWord_7409047) baseStart_7409047 baseEnd_7409047 := by
    simpa [prefixWord, tailWord_7409047, baseEnd_7409047] using wordTrace_append hprefix tailTrace_7409047
  have hstable : (prefixWord ++ tailWord_7409047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409047).length < 2 ^ (prefixWord ++ tailWord_7409047).sum := by decide
  have hdescent : baseEnd_7409047 < baseStart_7409047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409050 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_7409050 : Nat := 118140960795 + 7409050 * 2 ^ 59
def prefixEnd_7409050 : Nat := 4983230072969 + 3 ^ 40 * 7409050 * 2
def baseEnd_7409050 : Nat := 1268134614398114097167135

theorem tailTrace_7409050 : CollatzResearch.WordTrace tailWord_7409050 prefixEnd_7409050 1268134614398114097167135 := by
  unfold tailWord_7409050
  simp only [CollatzResearch.WordTrace]
  refine ⟨67557563452071172461064151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180153502538856459896171069 67557563452071172461064151)
  ·
    refine ⟨101336345178106758691596227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67557563452071172461064151 101336345178106758691596227)
    ·
      refine ⟨152004517767160138037394341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101336345178106758691596227 152004517767160138037394341)
      ·
        refine ⟨28500847081342525882011439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152004517767160138037394341 28500847081342525882011439)
        ·
          refine ⟨42751270622013788823017159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28500847081342525882011439 42751270622013788823017159)
          ·
            refine ⟨64126905933020683234525739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42751270622013788823017159 64126905933020683234525739)
            ·
              refine ⟨96190358899531024851788609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64126905933020683234525739 96190358899531024851788609)
              ·
                refine ⟨72142769174648268638841457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96190358899531024851788609 72142769174648268638841457)
                ·
                  refine ⟨54107076880986201479131093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72142769174648268638841457 54107076880986201479131093)
                  ·
                    refine ⟨1268134614398114097167135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54107076880986201479131093 1268134614398114097167135)
                    ·
                      rfl

theorem cell23_7409050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_7409050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409050 prefixEnd_7409050 := by exact prefixLift 7409050
  have htrace : WordTrace (prefixWord ++ tailWord_7409050) baseStart_7409050 baseEnd_7409050 := by
    simpa [prefixWord, tailWord_7409050, baseEnd_7409050] using wordTrace_append hprefix tailTrace_7409050
  have hstable : (prefixWord ++ tailWord_7409050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409050).length < 2 ^ (prefixWord ++ tailWord_7409050).sum := by decide
  have hdescent : baseEnd_7409050 < baseStart_7409050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409060 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_7409060 : Nat := 118140960795 + 7409060 * 2 ^ 59
def prefixEnd_7409060 : Nat := 4983230072969 + 3 ^ 40 * 7409060 * 2
def baseEnd_7409060 : Nat := 3804408978000887252376359

theorem tailTrace_7409060 : CollatzResearch.WordTrace tailWord_7409060 prefixEnd_7409060 3804408978000887252376359 := by
  unfold tailWord_7409060
  simp only [CollatzResearch.WordTrace]
  refine ⟨135115309269124230776060317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180153745692165641034747089 135115309269124230776060317)
  ·
    refine ⟨50668240975921586541022619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135115309269124230776060317 50668240975921586541022619)
    ·
      refine ⟨76002361463882379811533929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50668240975921586541022619 76002361463882379811533929)
      ·
        refine ⟨57001771097911784858650447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76002361463882379811533929 57001771097911784858650447)
        ·
          refine ⟨85502656646867677287975671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57001771097911784858650447 85502656646867677287975671)
          ·
            refine ⟨128253984970301515931963507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85502656646867677287975671 128253984970301515931963507)
            ·
              refine ⟨192380977455452273897945261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128253984970301515931963507 192380977455452273897945261)
              ·
                refine ⟨72142866545794602711729473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192380977455452273897945261 72142866545794602711729473)
                ·
                  refine ⟨54107149909345952033797105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72142866545794602711729473 54107149909345952033797105)
                  ·
                    refine ⟨40580362432009464025347829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54107149909345952033797105 40580362432009464025347829)
                    ·
                      refine ⟨3804408978000887252376359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40580362432009464025347829 3804408978000887252376359)
                      ·
                        rfl

theorem cell23_7409060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_7409060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409060 prefixEnd_7409060 := by exact prefixLift 7409060
  have htrace : WordTrace (prefixWord ++ tailWord_7409060) baseStart_7409060 baseEnd_7409060 := by
    simpa [prefixWord, tailWord_7409060, baseEnd_7409060] using wordTrace_append hprefix tailTrace_7409060
  have hstable : (prefixWord ++ tailWord_7409060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409060).length < 2 ^ (prefixWord ++ tailWord_7409060).sum := by decide
  have hdescent : baseEnd_7409060 < baseStart_7409060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409080 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 2, 6]
def baseStart_7409080 : Nat := 118140960795 + 7409080 * 2 ^ 59
def prefixEnd_7409080 : Nat := 4983230072969 + 3 ^ 40 * 7409080 * 2
def baseEnd_7409080 : Nat := 1268139749204659058042089

theorem tailTrace_7409080 : CollatzResearch.WordTrace tailWord_7409080 prefixEnd_7409080 1268139749204659058042089 := by
  unfold tailWord_7409080
  simp only [CollatzResearch.WordTrace]
  refine ⟨135115673999088002483924347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180154231998784003311899129 135115673999088002483924347)
  ·
    refine ⟨202673510998632003725886521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135115673999088002483924347 202673510998632003725886521)
    ·
      refine ⟨152005133248974002794414891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202673510998632003725886521 152005133248974002794414891)
      ·
        refine ⟨228007699873461004191622337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152005133248974002794414891 228007699873461004191622337)
        ·
          refine ⟨171005774905095753143716753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228007699873461004191622337 171005774905095753143716753)
          ·
            refine ⟨128254331178821814857787565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171005774905095753143716753 128254331178821814857787565)
            ·
              refine ⟨48095374192058180571670337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128254331178821814857787565 48095374192058180571670337)
              ·
                refine ⟨36071530644043635428752753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48095374192058180571670337 36071530644043635428752753)
                ·
                  refine ⟨27053647983032726571564565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36071530644043635428752753 27053647983032726571564565)
                  ·
                    refine ⟨1268139749204659058042089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27053647983032726571564565 1268139749204659058042089)
                    ·
                      rfl

theorem cell23_7409080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_7409080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409080 prefixEnd_7409080 := by exact prefixLift 7409080
  have htrace : WordTrace (prefixWord ++ tailWord_7409080) baseStart_7409080 baseEnd_7409080 := by
    simpa [prefixWord, tailWord_7409080, baseEnd_7409080] using wordTrace_append hprefix tailTrace_7409080
  have hstable : (prefixWord ++ tailWord_7409080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409080).length < 2 ^ (prefixWord ++ tailWord_7409080).sum := by decide
  have hdescent : baseEnd_7409080 < baseStart_7409080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409087 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 3, 4, 2]
def baseStart_7409087 : Nat := 118140960795 + 7409087 * 2 ^ 59
def prefixEnd_7409087 : Nat := 4983230072969 + 3 ^ 40 * 7409087 * 2
def baseEnd_7409087 : Nat := 3804422841978558646738735

theorem tailTrace_7409087 : CollatzResearch.WordTrace tailWord_7409087 prefixEnd_7409087 3804422841978558646738735 := by
  unfold tailWord_7409087
  simp only [CollatzResearch.WordTrace]
  refine ⟨270231603309150645163353515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180154402206100430108902343 270231603309150645163353515)
  ·
    refine ⟨405347404963725967745030273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270231603309150645163353515 405347404963725967745030273)
    ·
      refine ⟨304010553722794475808772705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405347404963725967745030273 304010553722794475808772705)
      ·
        refine ⟨228007915292095856856579529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304010553722794475808772705 228007915292095856856579529)
        ·
          refine ⟨171005936469071892642434647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228007915292095856856579529 171005936469071892642434647)
          ·
            refine ⟨256508904703607838963651971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171005936469071892642434647 256508904703607838963651971)
            ·
              refine ⟨384763357055411758445477957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256508904703607838963651971 384763357055411758445477957)
              ·
                refine ⟨72143129447889704708527117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384763357055411758445477957 72143129447889704708527117)
                ·
                  refine ⟨27053673542958639265697669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72143129447889704708527117 27053673542958639265697669)
                  ·
                    refine ⟨5072563789304744862318313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27053673542958639265697669 5072563789304744862318313)
                    ·
                      refine ⟨3804422841978558646738735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072563789304744862318313 3804422841978558646738735)
                      ·
                        rfl

theorem cell23_7409087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_7409087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409087 prefixEnd_7409087 := by exact prefixLift 7409087
  have htrace : WordTrace (prefixWord ++ tailWord_7409087) baseStart_7409087 baseEnd_7409087 := by
    simpa [prefixWord, tailWord_7409087, baseEnd_7409087] using wordTrace_append hprefix tailTrace_7409087
  have hstable : (prefixWord ++ tailWord_7409087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409087).length < 2 ^ (prefixWord ++ tailWord_7409087).sum := by decide
  have hdescent : baseEnd_7409087 < baseStart_7409087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409108 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_7409108 : Nat := 118140960795 + 7409108 * 2 ^ 59
def prefixEnd_7409108 : Nat := 4983230072969 + 3 ^ 40 * 7409108 * 2
def baseEnd_7409108 : Nat := 3804433625072303064576139

theorem tailTrace_7409108 : CollatzResearch.WordTrace tailWord_7409108 prefixEnd_7409108 3804433625072303064576139 := by
  unfold tailWord_7409108
  simp only [CollatzResearch.WordTrace]
  refine ⟨135116184621037282874933989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180154912828049710499911985 135116184621037282874933989)
  ·
    refine ⟨25334284616444490539050123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135116184621037282874933989 25334284616444490539050123)
    ·
      refine ⟨38001426924666735808575185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25334284616444490539050123 38001426924666735808575185)
      ·
        refine ⟨28501070193500051856431389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38001426924666735808575185 28501070193500051856431389)
        ·
          refine ⟨10687901322562519446161771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28501070193500051856431389 10687901322562519446161771)
          ·
            refine ⟨16031851983843779169242657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10687901322562519446161771 16031851983843779169242657)
            ·
              refine ⟨12023888987882834376931993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16031851983843779169242657 12023888987882834376931993)
              ·
                refine ⟨9017916740912125782698995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12023888987882834376931993 9017916740912125782698995)
                ·
                  refine ⟨13526875111368188674048493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9017916740912125782698995 13526875111368188674048493)
                  ·
                    refine ⟨5072578166763070752768185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13526875111368188674048493 5072578166763070752768185)
                    ·
                      refine ⟨3804433625072303064576139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072578166763070752768185 3804433625072303064576139)
                      ·
                        rfl

theorem cell23_7409108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_7409108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409108 prefixEnd_7409108 := by exact prefixLift 7409108
  have htrace : WordTrace (prefixWord ++ tailWord_7409108) baseStart_7409108 baseEnd_7409108 := by
    simpa [prefixWord, tailWord_7409108, baseEnd_7409108] using wordTrace_append hprefix tailTrace_7409108
  have hstable : (prefixWord ++ tailWord_7409108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409108).length < 2 ^ (prefixWord ++ tailWord_7409108).sum := by decide
  have hdescent : baseEnd_7409108 < baseStart_7409108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409147 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 1, 7, 2]
def baseStart_7409147 : Nat := 118140960795 + 7409147 * 2 ^ 59
def prefixEnd_7409147 : Nat := 4983230072969 + 3 ^ 40 * 7409147 * 2
def baseEnd_7409147 : Nat := 3804453650817828411988459

theorem tailTrace_7409147 : CollatzResearch.WordTrace tailWord_7409147 prefixEnd_7409147 3804453650817828411988459 := by
  unfold tailWord_7409147
  simp only [CollatzResearch.WordTrace]
  refine ⟨270233791688933275410537695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180155861125955516940358463 270233791688933275410537695)
  ·
    refine ⟨405350687533399913115806543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270233791688933275410537695 405350687533399913115806543)
    ·
      refine ⟨608026031300099869673709815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405350687533399913115806543 608026031300099869673709815)
      ·
        refine ⟨912039046950149804510564723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608026031300099869673709815 912039046950149804510564723)
        ·
          refine ⟨1368058570425224706765847085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912039046950149804510564723 1368058570425224706765847085)
          ·
            refine ⟨513021963909459265037192657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1368058570425224706765847085 513021963909459265037192657)
            ·
              refine ⟨384766472932094448777894493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513021963909459265037192657 384766472932094448777894493)
              ·
                refine ⟨144287427349535418291710435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384766472932094448777894493 144287427349535418291710435)
                ·
                  refine ⟨216431141024303127437565653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144287427349535418291710435 216431141024303127437565653)
                  ·
                    refine ⟨5072604867757104549317945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 216431141024303127437565653 5072604867757104549317945)
                    ·
                      refine ⟨3804453650817828411988459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072604867757104549317945 3804453650817828411988459)
                      ·
                        rfl

theorem cell23_7409147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 7, 2].length) (baseStart_7409147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409147 prefixEnd_7409147 := by exact prefixLift 7409147
  have htrace : WordTrace (prefixWord ++ tailWord_7409147) baseStart_7409147 baseEnd_7409147 := by
    simpa [prefixWord, tailWord_7409147, baseEnd_7409147] using wordTrace_append hprefix tailTrace_7409147
  have hstable : (prefixWord ++ tailWord_7409147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409147).length < 2 ^ (prefixWord ++ tailWord_7409147).sum := by decide
  have hdescent : baseEnd_7409147 < baseStart_7409147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409194 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7409194 : Nat := 118140960795 + 7409194 * 2 ^ 59
def prefixEnd_7409194 : Nat := 4983230072969 + 3 ^ 40 * 7409194 * 2
def baseEnd_7409194 : Nat := 3804477784408589728100743

theorem tailTrace_7409194 : CollatzResearch.WordTrace tailWord_7409194 prefixEnd_7409194 3804477784408589728100743 := by
  unfold tailWord_7409194
  simp only [CollatzResearch.WordTrace]
  refine ⟨67558876479940750609374659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180157003946508668291665757 67558876479940750609374659)
  ·
    refine ⟨101338314719911125914061989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67558876479940750609374659 101338314719911125914061989)
    ·
      refine ⟨19000934009983336108886623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101338314719911125914061989 19000934009983336108886623)
      ·
        refine ⟨28501401014975004163329935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19000934009983336108886623 28501401014975004163329935)
        ·
          refine ⟨42752101522462506244994903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28501401014975004163329935 42752101522462506244994903)
          ·
            refine ⟨64128152283693759367492355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42752101522462506244994903 64128152283693759367492355)
            ·
              refine ⟨96192228425540639051238533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64128152283693759367492355 96192228425540639051238533)
              ·
                refine ⟨18036042829788869822107225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96192228425540639051238533 18036042829788869822107225)
                ·
                  refine ⟨13527032122341652366580419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18036042829788869822107225 13527032122341652366580419)
                  ·
                    refine ⟨20290548183512478549870629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13527032122341652366580419 20290548183512478549870629)
                    ·
                      refine ⟨3804477784408589728100743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20290548183512478549870629 3804477784408589728100743)
                      ·
                        rfl

theorem cell23_7409194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7409194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409194 prefixEnd_7409194 := by exact prefixLift 7409194
  have htrace : WordTrace (prefixWord ++ tailWord_7409194) baseStart_7409194 baseEnd_7409194 := by
    simpa [prefixWord, tailWord_7409194, baseEnd_7409194] using wordTrace_append hprefix tailTrace_7409194
  have hstable : (prefixWord ++ tailWord_7409194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409194).length < 2 ^ (prefixWord ++ tailWord_7409194).sum := by decide
  have hdescent : baseEnd_7409194 < baseStart_7409194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409281 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 1, 5]
def baseStart_7409281 : Nat := 118140960795 + 7409281 * 2 ^ 59
def prefixEnd_7409281 : Nat := 4983230072969 + 3 ^ 40 * 7409281 * 2
def baseEnd_7409281 : Nat := 1268174152408510295904281

theorem tailTrace_7409281 : CollatzResearch.WordTrace tailWord_7409281 prefixEnd_7409281 1268174152408510295904281 := by
  unfold tailWord_7409281
  simp only [CollatzResearch.WordTrace]
  refine ⟨270238679070447816295915697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180159119380298544197277131 270238679070447816295915697)
  ·
    refine ⟨202679009302835862221936773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270238679070447816295915697 202679009302835862221936773)
    ·
      refine ⟨38002314244281724166613145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202679009302835862221936773 38002314244281724166613145)
      ·
        refine ⟨28501735683211293124959859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38002314244281724166613145 28501735683211293124959859)
        ·
          refine ⟨42752603524816939687439789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28501735683211293124959859 42752603524816939687439789)
          ·
            refine ⟨16032226321806352382789921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42752603524816939687439789 16032226321806352382789921)
            ·
              refine ⟨12024169741354764287092441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16032226321806352382789921 12024169741354764287092441)
              ·
                refine ⟨9018127306016073215319331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12024169741354764287092441 9018127306016073215319331)
                ·
                  refine ⟨13527190959024109822978997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018127306016073215319331 13527190959024109822978997)
                  ·
                    refine ⟨1268174152408510295904281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13527190959024109822978997 1268174152408510295904281)
                    ·
                      rfl

theorem cell23_7409281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_7409281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409281 prefixEnd_7409281 := by exact prefixLift 7409281
  have htrace : WordTrace (prefixWord ++ tailWord_7409281) baseStart_7409281 baseEnd_7409281 := by
    simpa [prefixWord, tailWord_7409281, baseEnd_7409281] using wordTrace_append hprefix tailTrace_7409281
  have hstable : (prefixWord ++ tailWord_7409281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409281).length < 2 ^ (prefixWord ++ tailWord_7409281).sum := by decide
  have hdescent : baseEnd_7409281 < baseStart_7409281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409301 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_7409301 : Nat := 118140960795 + 7409301 * 2 ^ 59
def prefixEnd_7409301 : Nat := 4983230072969 + 3 ^ 40 * 7409301 * 2
def baseEnd_7409301 : Nat := 3804532726838620809462751

theorem tailTrace_7409301 : CollatzResearch.WordTrace tailWord_7409301 prefixEnd_7409301 3804532726838620809462751 := by
  unfold tailWord_7409301
  simp only [CollatzResearch.WordTrace]
  refine ⟨270239408530375359711643757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180159605686916906474429171 270239408530375359711643757)
  ·
    refine ⟨101339778198890759891866409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270239408530375359711643757 101339778198890759891866409)
    ·
      refine ⟨76004833649168069918899807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101339778198890759891866409 76004833649168069918899807)
      ·
        refine ⟨114007250473752104878349711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76004833649168069918899807 114007250473752104878349711)
        ·
          refine ⟨171010875710628157317524567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114007250473752104878349711 171010875710628157317524567)
          ·
            refine ⟨256516313565942235976286851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171010875710628157317524567 256516313565942235976286851)
            ·
              refine ⟨384774470348913353964430277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256516313565942235976286851 384774470348913353964430277)
              ·
                refine ⟨72145213190421253868330677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384774470348913353964430277 72145213190421253868330677)
                ·
                  refine ⟨6763613736601992550156001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72145213190421253868330677 6763613736601992550156001)
                  ·
                    refine ⟨5072710302451494412617001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6763613736601992550156001 5072710302451494412617001)
                    ·
                      refine ⟨3804532726838620809462751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072710302451494412617001 3804532726838620809462751)
                      ·
                        rfl

theorem cell23_7409301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_7409301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409301 prefixEnd_7409301 := by exact prefixLift 7409301
  have htrace : WordTrace (prefixWord ++ tailWord_7409301) baseStart_7409301 baseEnd_7409301 := by
    simpa [prefixWord, tailWord_7409301, baseEnd_7409301] using wordTrace_append hprefix tailTrace_7409301
  have hstable : (prefixWord ++ tailWord_7409301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409301).length < 2 ^ (prefixWord ++ tailWord_7409301).sum := by decide
  have hdescent : baseEnd_7409301 < baseStart_7409301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409304 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7409304 : Nat := 118140960795 + 7409304 * 2 ^ 59
def prefixEnd_7409304 : Nat := 4983230072969 + 3 ^ 40 * 7409304 * 2
def baseEnd_7409304 : Nat := 3804534267280584297725237

theorem tailTrace_7409304 : CollatzResearch.WordTrace tailWord_7409304 prefixEnd_7409304 3804534267280584297725237 := by
  unfold tailWord_7409304
  simp only [CollatzResearch.WordTrace]
  refine ⟨135119758974682245612001483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180159678632909660816001977 135119758974682245612001483)
  ·
    refine ⟨202679638462023368418002225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135119758974682245612001483 202679638462023368418002225)
    ·
      refine ⟨152009728846517526313501669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202679638462023368418002225 152009728846517526313501669)
      ·
        refine ⟨28501824158722036183781563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152009728846517526313501669 28501824158722036183781563)
        ·
          refine ⟨42752736238083054275672345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28501824158722036183781563 42752736238083054275672345)
          ·
            refine ⟨32064552178562290706754259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42752736238083054275672345 32064552178562290706754259)
            ·
              refine ⟨48096828267843436060131389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32064552178562290706754259 48096828267843436060131389)
              ·
                refine ⟨18036310600441288522549271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48096828267843436060131389 18036310600441288522549271)
                ·
                  refine ⟨27054465900661932783823907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18036310600441288522549271 27054465900661932783823907)
                  ·
                    refine ⟨40581698850992899175735861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27054465900661932783823907 40581698850992899175735861)
                    ·
                      refine ⟨3804534267280584297725237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40581698850992899175735861 3804534267280584297725237)
                      ·
                        rfl

theorem cell23_7409304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7409304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409304 prefixEnd_7409304 := by exact prefixLift 7409304
  have htrace : WordTrace (prefixWord ++ tailWord_7409304) baseStart_7409304 baseEnd_7409304 := by
    simpa [prefixWord, tailWord_7409304, baseEnd_7409304] using wordTrace_append hprefix tailTrace_7409304
  have hstable : (prefixWord ++ tailWord_7409304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409304).length < 2 ^ (prefixWord ++ tailWord_7409304).sum := by decide
  have hdescent : baseEnd_7409304 < baseStart_7409304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409327 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_7409327 : Nat := 118140960795 + 7409327 * 2 ^ 59
def prefixEnd_7409327 : Nat := 4983230072969 + 3 ^ 40 * 7409327 * 2
def baseEnd_7409327 : Nat := 3804546077335637707737631

theorem tailTrace_7409327 : CollatzResearch.WordTrace tailWord_7409327 prefixEnd_7409327 3804546077335637707737631 := by
  unfold tailWord_7409327
  simp only [CollatzResearch.WordTrace]
  refine ⟨270240356828281166152090235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180160237885520777434726823 270240356828281166152090235)
  ·
    refine ⟨405360535242421749228135353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270240356828281166152090235 405360535242421749228135353)
    ·
      refine ⟨304020401431816311921101515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 405360535242421749228135353 304020401431816311921101515)
      ·
        refine ⟨456030602147724467881652273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304020401431816311921101515 456030602147724467881652273)
        ·
          refine ⟨342022951610793350911239205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456030602147724467881652273 342022951610793350911239205)
          ·
            refine ⟨64129303427023753295857351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342022951610793350911239205 64129303427023753295857351)
            ·
              refine ⟨96193955140535629943786027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64129303427023753295857351 96193955140535629943786027)
              ·
                refine ⟨144290932710803444915679041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96193955140535629943786027 144290932710803444915679041)
                ·
                  refine ⟨108218199533102583686759281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144290932710803444915679041 108218199533102583686759281)
                  ·
                    refine ⟨81163649649826937765069461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108218199533102583686759281 81163649649826937765069461)
                    ·
                      refine ⟨3804546077335637707737631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81163649649826937765069461 3804546077335637707737631)
                      ·
                        rfl

theorem cell23_7409327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_7409327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409327 prefixEnd_7409327 := by exact prefixLift 7409327
  have htrace : WordTrace (prefixWord ++ tailWord_7409327) baseStart_7409327 baseEnd_7409327 := by
    simpa [prefixWord, tailWord_7409327, baseEnd_7409327] using wordTrace_append hprefix tailTrace_7409327
  have hstable : (prefixWord ++ tailWord_7409327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409327).length < 2 ^ (prefixWord ++ tailWord_7409327).sum := by decide
  have hdescent : baseEnd_7409327 < baseStart_7409327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409338 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_7409338 : Nat := 118140960795 + 7409338 * 2 ^ 59
def prefixEnd_7409338 : Nat := 4983230072969 + 3 ^ 40 * 7409338 * 2
def baseEnd_7409338 : Nat := 3804551725622837164700081

theorem tailTrace_7409338 : CollatzResearch.WordTrace tailWord_7409338 prefixEnd_7409338 3804551725622837164700081 := by
  unfold tailWord_7409338
  simp only [CollatzResearch.WordTrace]
  refine ⟨67560189507810328757685167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180160505354160876687160445 67560189507810328757685167)
  ·
    refine ⟨101340284261715493136527751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67560189507810328757685167 101340284261715493136527751)
    ·
      refine ⟨152010426392573239704791627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101340284261715493136527751 152010426392573239704791627)
      ·
        refine ⟨228015639588859859557187441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152010426392573239704791627 228015639588859859557187441)
        ·
          refine ⟨171011729691644894667890581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228015639588859859557187441 171011729691644894667890581)
          ·
            refine ⟨8016174829295854437557371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171011729691644894667890581 8016174829295854437557371)
            ·
              refine ⟨12024262243943781656336057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8016174829295854437557371 12024262243943781656336057)
              ·
                refine ⟨9018196682957836242252043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12024262243943781656336057 9018196682957836242252043)
                ·
                  refine ⟨13527295024436754363378065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018196682957836242252043 13527295024436754363378065)
                  ·
                    refine ⟨10145471268327565772533549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13527295024436754363378065 10145471268327565772533549)
                    ·
                      refine ⟨3804551725622837164700081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10145471268327565772533549 3804551725622837164700081)
                      ·
                        rfl

theorem cell23_7409338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_7409338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409338 prefixEnd_7409338 := by exact prefixLift 7409338
  have htrace : WordTrace (prefixWord ++ tailWord_7409338) baseStart_7409338 baseEnd_7409338 := by
    simpa [prefixWord, tailWord_7409338, baseEnd_7409338] using wordTrace_append hprefix tailTrace_7409338
  have hstable : (prefixWord ++ tailWord_7409338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409338).length < 2 ^ (prefixWord ++ tailWord_7409338).sum := by decide
  have hdescent : baseEnd_7409338 < baseStart_7409338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409368 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_7409368 : Nat := 118140960795 + 7409368 * 2 ^ 59
def prefixEnd_7409368 : Nat := 4983230072969 + 3 ^ 40 * 7409368 * 2
def baseEnd_7409368 : Nat := 3804567130042472047324943

theorem tailTrace_7409368 : CollatzResearch.WordTrace tailWord_7409368 prefixEnd_7409368 3804567130042472047324943 := by
  unfold tailWord_7409368
  simp only [CollatzResearch.WordTrace]
  refine ⟨135120926110566315077166379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180161234814088420102888505 135120926110566315077166379)
  ·
    refine ⟨202681389165849472615749569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135120926110566315077166379 202681389165849472615749569)
    ·
      refine ⟨152011041874387104461812177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202681389165849472615749569 152011041874387104461812177)
      ·
        refine ⟨114008281405790328346359133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152011041874387104461812177 114008281405790328346359133)
        ·
          refine ⟨42753105527171373129884675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114008281405790328346359133 42753105527171373129884675)
          ·
            refine ⟨64129658290757059694827013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42753105527171373129884675 64129658290757059694827013)
            ·
              refine ⟨12024310929516948692780065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64129658290757059694827013 12024310929516948692780065)
              ·
                refine ⟨9018233197137711519585049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12024310929516948692780065 9018233197137711519585049)
                ·
                  refine ⟨6763674897853283639688787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9018233197137711519585049 6763674897853283639688787)
                  ·
                    refine ⟨10145512346779925459533181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6763674897853283639688787 10145512346779925459533181)
                    ·
                      refine ⟨3804567130042472047324943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10145512346779925459533181 3804567130042472047324943)
                      ·
                        rfl

theorem cell23_7409368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_7409368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409368 prefixEnd_7409368 := by exact prefixLift 7409368
  have htrace : WordTrace (prefixWord ++ tailWord_7409368) baseStart_7409368 baseEnd_7409368 := by
    simpa [prefixWord, tailWord_7409368, baseEnd_7409368] using wordTrace_append hprefix tailTrace_7409368
  have hstable : (prefixWord ++ tailWord_7409368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409368).length < 2 ^ (prefixWord ++ tailWord_7409368).sum := by decide
  have hdescent : baseEnd_7409368 < baseStart_7409368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409384 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 1, 8]
def baseStart_7409384 : Nat := 118140960795 + 7409384 * 2 ^ 59
def prefixEnd_7409384 : Nat := 4983230072969 + 3 ^ 40 * 7409384 * 2
def baseEnd_7409384 : Nat := 1268191781910981328241623

theorem tailTrace_7409384 : CollatzResearch.WordTrace tailWord_7409384 prefixEnd_7409384 1268191781910981328241623 := by
  unfold tailWord_7409384
  simp only [CollatzResearch.WordTrace]
  refine ⟨135121217894537332443457603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180161623859383109924610137 135121217894537332443457603)
  ·
    refine ⟨202681826841805998665186405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135121217894537332443457603 202681826841805998665186405)
    ·
      refine ⟨38002842532838624749722451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202681826841805998665186405 38002842532838624749722451)
      ·
        refine ⟨57004263799257937124583677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38002842532838624749722451 57004263799257937124583677)
        ·
          refine ⟨21376598924721726421718879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57004263799257937124583677 21376598924721726421718879)
          ·
            refine ⟨32064898387082589632578319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21376598924721726421718879 32064898387082589632578319)
            ·
              refine ⟨48097347580623884448867479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32064898387082589632578319 48097347580623884448867479)
              ·
                refine ⟨72146021370935826673301219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48097347580623884448867479 72146021370935826673301219)
                ·
                  refine ⟨108219032056403740009951829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72146021370935826673301219 108219032056403740009951829)
                  ·
                    refine ⟨1268191781910981328241623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108219032056403740009951829 1268191781910981328241623)
                    ·
                      rfl

theorem cell23_7409384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_7409384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409384 prefixEnd_7409384 := by exact prefixLift 7409384
  have htrace : WordTrace (prefixWord ++ tailWord_7409384) baseStart_7409384 baseEnd_7409384 := by
    simpa [prefixWord, tailWord_7409384, baseEnd_7409384] using wordTrace_append hprefix tailTrace_7409384
  have hstable : (prefixWord ++ tailWord_7409384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409384).length < 2 ^ (prefixWord ++ tailWord_7409384).sum := by decide
  have hdescent : baseEnd_7409384 < baseStart_7409384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409404 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_7409404 : Nat := 118140960795 + 7409404 * 2 ^ 59
def prefixEnd_7409404 : Nat := 4983230072969 + 3 ^ 40 * 7409404 * 2
def baseEnd_7409404 : Nat := 3804585615346033906474777

theorem tailTrace_7409404 : CollatzResearch.WordTrace tailWord_7409404 prefixEnd_7409404 3804585615346033906474777 := by
  unfold tailWord_7409404
  simp only [CollatzResearch.WordTrace]
  refine ⟨135121582624501104151321633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180162110166001472201762177 135121582624501104151321633)
  ·
    refine ⟨101341186968375828113491225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135121582624501104151321633 101341186968375828113491225)
    ·
      refine ⟨76005890226281871085118419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101341186968375828113491225 76005890226281871085118419)
      ·
        refine ⟨114008835339422806627677629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76005890226281871085118419 114008835339422806627677629)
        ·
          refine ⟨42753313252283552485379111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114008835339422806627677629 42753313252283552485379111)
          ·
            refine ⟨64129969878425328728068667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42753313252283552485379111 64129969878425328728068667)
            ·
              refine ⟨96194954817637993092103001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64129969878425328728068667 96194954817637993092103001)
              ·
                refine ⟨72146216113228494819077251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96194954817637993092103001 72146216113228494819077251)
                ·
                  refine ⟨108219324169842742228615877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72146216113228494819077251 108219324169842742228615877)
                  ·
                    refine ⟨20291123281845514167865477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108219324169842742228615877 20291123281845514167865477)
                    ·
                      refine ⟨3804585615346033906474777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20291123281845514167865477 3804585615346033906474777)
                      ·
                        rfl

theorem cell23_7409404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_7409404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409404 prefixEnd_7409404 := by exact prefixLift 7409404
  have htrace : WordTrace (prefixWord ++ tailWord_7409404) baseStart_7409404 baseEnd_7409404 := by
    simpa [prefixWord, tailWord_7409404, baseEnd_7409404] using wordTrace_append hprefix tailTrace_7409404
  have hstable : (prefixWord ++ tailWord_7409404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409404).length < 2 ^ (prefixWord ++ tailWord_7409404).sum := by decide
  have hdescent : baseEnd_7409404 < baseStart_7409404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7409412 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_7409412 : Nat := 118140960795 + 7409412 * 2 ^ 59
def prefixEnd_7409412 : Nat := 4983230072969 + 3 ^ 40 * 7409412 * 2
def baseEnd_7409412 : Nat := 3804589723191269875174741

theorem tailTrace_7409412 : CollatzResearch.WordTrace tailWord_7409412 prefixEnd_7409412 3804589723191269875174741 := by
  unfold tailWord_7409412
  simp only [CollatzResearch.WordTrace]
  refine ⟨135121728516486612834467245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180162304688648817112622993 135121728516486612834467245)
  ·
    refine ⟨50670648193682479812925217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135121728516486612834467245 50670648193682479812925217)
    ·
      refine ⟨38002986145261859859693913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50670648193682479812925217 38002986145261859859693913)
      ·
        refine ⟨28502239608946394894770435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38002986145261859859693913 28502239608946394894770435)
        ·
          refine ⟨42753359413419592342155653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28502239608946394894770435 42753359413419592342155653)
          ·
            refine ⟨8016254890016173564154185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42753359413419592342155653 8016254890016173564154185)
            ·
              refine ⟨6012191167512130173115639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8016254890016173564154185 6012191167512130173115639)
              ·
                refine ⟨9018286751268195259673459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012191167512130173115639 9018286751268195259673459)
                ·
                  refine ⟨13527430126902292889510189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018286751268195259673459 13527430126902292889510189)
                  ·
                    refine ⟨5072786297588359833566321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13527430126902292889510189 5072786297588359833566321)
                    ·
                      refine ⟨3804589723191269875174741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5072786297588359833566321 3804589723191269875174741)
                      ·
                        rfl

theorem cell23_7409412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_7409412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7409412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7409412 prefixEnd_7409412 := by exact prefixLift 7409412
  have htrace : WordTrace (prefixWord ++ tailWord_7409412) baseStart_7409412 baseEnd_7409412 := by
    simpa [prefixWord, tailWord_7409412, baseEnd_7409412] using wordTrace_append hprefix tailTrace_7409412
  have hstable : (prefixWord ++ tailWord_7409412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7409412).length < 2 ^ (prefixWord ++ tailWord_7409412).sum := by decide
  have hdescent : baseEnd_7409412 < baseStart_7409412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7409412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
