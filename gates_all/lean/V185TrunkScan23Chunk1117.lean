import V185TrunkScan23Chunk1116

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6616018 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_6616018 : Nat := 118140960795 + 6616018 * 2 ^ 59
def prefixEnd_6616018 : Nat := 4983230072969 + 3 ^ 40 * 6616018 * 2
def baseEnd_6616018 : Nat := 1132399084266000344282831

theorem tailTrace_6616018 : CollatzResearch.WordTrace tailWord_6616018 prefixEnd_6616018 1132399084266000344282831 := by
  unfold tailWord_6616018
  simp only [CollatzResearch.WordTrace]
  refine ⟨60326500136326046690378177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160870667030202791174341805 60326500136326046690378177)
  ·
    refine ⟨45244875102244535017783633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60326500136326046690378177 45244875102244535017783633)
    ·
      refine ⟨33933656326683401263337725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45244875102244535017783633 33933656326683401263337725)
      ·
        refine ⟨12725121122506275473751647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33933656326683401263337725 12725121122506275473751647)
        ·
          refine ⟨19087681683759413210627471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12725121122506275473751647 19087681683759413210627471)
          ·
            refine ⟨28631522525639119815941207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19087681683759413210627471 28631522525639119815941207)
            ·
              refine ⟨42947283788458679723911811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28631522525639119815941207 42947283788458679723911811)
              ·
                refine ⟨64420925682688019585867717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42947283788458679723911811 64420925682688019585867717)
                ·
                  refine ⟨12078923565504003672350197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64420925682688019585867717 12078923565504003672350197)
                  ·
                    refine ⟨1132399084266000344282831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12078923565504003672350197 1132399084266000344282831)
                    ·
                      rfl

theorem cell23_6616018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_6616018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616018 prefixEnd_6616018 := by exact prefixLift 6616018
  have htrace : WordTrace (prefixWord ++ tailWord_6616018) baseStart_6616018 baseEnd_6616018 := by
    simpa [prefixWord, tailWord_6616018, baseEnd_6616018] using wordTrace_append hprefix tailTrace_6616018
  have hstable : (prefixWord ++ tailWord_6616018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616018).length < 2 ^ (prefixWord ++ tailWord_6616018).sum := by decide
  have hdescent : baseEnd_6616018 < baseStart_6616018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616078 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_6616078 : Nat := 118140960795 + 6616078 * 2 ^ 59
def prefixEnd_6616078 : Nat := 4983230072969 + 3 ^ 40 * 6616078 * 2
def baseEnd_6616078 : Nat := 377469784626363422010913

theorem tailTrace_6616078 : CollatzResearch.WordTrace tailWord_6616078 prefixEnd_6616078 377469784626363422010913 := by
  unfold tailWord_6616078
  simp only [CollatzResearch.WordTrace]
  refine ⟨30163523615635852126087111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160872125950057878005797925 30163523615635852126087111)
  ·
    refine ⟨45245285423453778189130667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30163523615635852126087111 45245285423453778189130667)
    ·
      refine ⟨67867928135180667283696001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45245285423453778189130667 67867928135180667283696001)
      ·
        refine ⟨50900946101385500462772001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67867928135180667283696001 50900946101385500462772001)
        ·
          refine ⟨38175709576039125347079001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50900946101385500462772001 38175709576039125347079001)
          ·
            refine ⟨28631782182029344010309251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38175709576039125347079001 28631782182029344010309251)
            ·
              refine ⟨42947673273044016015463877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28631782182029344010309251 42947673273044016015463877)
              ·
                refine ⟨8052688738695753002899477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42947673273044016015463877 8052688738695753002899477)
                ·
                  refine ⟨377469784626363422010913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8052688738695753002899477 377469784626363422010913)
                  ·
                    rfl

theorem cell23_6616078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_6616078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616078 prefixEnd_6616078 := by exact prefixLift 6616078
  have htrace : WordTrace (prefixWord ++ tailWord_6616078) baseStart_6616078 baseEnd_6616078 := by
    simpa [prefixWord, tailWord_6616078, baseEnd_6616078] using wordTrace_append hprefix tailTrace_6616078
  have hstable : (prefixWord ++ tailWord_6616078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616078).length < 2 ^ (prefixWord ++ tailWord_6616078).sum := by decide
  have hdescent : baseEnd_6616078 < baseStart_6616078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616101 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_6616101 : Nat := 118140960795 + 6616101 * 2 ^ 59
def prefixEnd_6616101 : Nat := 4983230072969 + 3 ^ 40 * 6616101 * 2
def baseEnd_6616101 : Nat := 3397239871692324208110611

theorem tailTrace_6616101 : CollatzResearch.WordTrace tailWord_6616101 prefixEnd_6616101 3397239871692324208110611 := by
  unfold tailWord_6616101
  simp only [CollatzResearch.WordTrace]
  refine ⟨241309027804003491936784157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160872685202668994624522771 241309027804003491936784157)
  ·
    refine ⟨90490885426501309476294059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241309027804003491936784157 90490885426501309476294059)
    ·
      refine ⟨135736328139751964214441089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90490885426501309476294059 135736328139751964214441089)
      ·
        refine ⟨101802246104813973160830817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135736328139751964214441089 101802246104813973160830817)
        ·
          refine ⟨76351684578610479870623113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101802246104813973160830817 76351684578610479870623113)
          ·
            refine ⟨57263763433957859902967335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76351684578610479870623113 57263763433957859902967335)
            ·
              refine ⟨85895645150936789854451003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57263763433957859902967335 85895645150936789854451003)
              ·
                refine ⟨128843467726405184781676505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85895645150936789854451003 128843467726405184781676505)
                ·
                  refine ⟨96632600794803888586257379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128843467726405184781676505 96632600794803888586257379)
                  ·
                    refine ⟨144948901192205832879386069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96632600794803888586257379 144948901192205832879386069)
                    ·
                      refine ⟨3397239871692324208110611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144948901192205832879386069 3397239871692324208110611)
                      ·
                        rfl

theorem cell23_6616101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_6616101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616101 prefixEnd_6616101 := by exact prefixLift 6616101
  have htrace : WordTrace (prefixWord ++ tailWord_6616101) baseStart_6616101 baseEnd_6616101 := by
    simpa [prefixWord, tailWord_6616101, baseEnd_6616101] using wordTrace_append hprefix tailTrace_6616101
  have hstable : (prefixWord ++ tailWord_6616101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616101).length < 2 ^ (prefixWord ++ tailWord_6616101).sum := by decide
  have hdescent : baseEnd_6616101 < baseStart_6616101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616108 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_6616108 : Nat := 118140960795 + 6616108 * 2 ^ 59
def prefixEnd_6616108 : Nat := 4983230072969 + 3 ^ 40 * 6616108 * 2
def baseEnd_6616108 : Nat := 1132414488685635226907693

theorem tailTrace_6616108 : CollatzResearch.WordTrace tailWord_6616108 prefixEnd_6616108 1132414488685635226907693 := by
  unfold tailWord_6616108
  simp only [CollatzResearch.WordTrace]
  refine ⟨120654641557489066066144489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160872855409985421421525985 120654641557489066066144489)
  ·
    refine ⟨90490981168116799549608367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120654641557489066066144489 90490981168116799549608367)
    ·
      refine ⟨135736471752175199324412551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90490981168116799549608367 135736471752175199324412551)
      ·
        refine ⟨203604707628262798986618827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135736471752175199324412551 203604707628262798986618827)
        ·
          refine ⟨305407061442394198479928241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203604707628262798986618827 305407061442394198479928241)
          ·
            refine ⟨229055296081795648859946181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305407061442394198479928241 229055296081795648859946181)
            ·
              refine ⟨42947868015336684161239909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229055296081795648859946181 42947868015336684161239909)
              ·
                refine ⟨8052725252875628280232483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42947868015336684161239909 8052725252875628280232483)
                ·
                  refine ⟨12079087879313442420348725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8052725252875628280232483 12079087879313442420348725)
                  ·
                    refine ⟨1132414488685635226907693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12079087879313442420348725 1132414488685635226907693)
                    ·
                      rfl

theorem cell23_6616108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_6616108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616108 prefixEnd_6616108 := by exact prefixLift 6616108
  have htrace : WordTrace (prefixWord ++ tailWord_6616108) baseStart_6616108 baseEnd_6616108 := by
    simpa [prefixWord, tailWord_6616108, baseEnd_6616108] using wordTrace_append hprefix tailTrace_6616108
  have hstable : (prefixWord ++ tailWord_6616108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616108).length < 2 ^ (prefixWord ++ tailWord_6616108).sum := by decide
  have hdescent : baseEnd_6616108 < baseStart_6616108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616122 : List Nat := [3, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3]
def baseStart_6616122 : Nat := 118140960795 + 6616122 * 2 ^ 59
def prefixEnd_6616122 : Nat := 4983230072969 + 3 ^ 40 * 6616122 * 2
def baseEnd_6616122 : Nat := 3397250654786068625948015

theorem tailTrace_6616122 : CollatzResearch.WordTrace tailWord_6616122 prefixEnd_6616122 3397250654786068625948015 := by
  unfold tailWord_6616122
  simp only [CollatzResearch.WordTrace]
  refine ⟨60327448434231853130824655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160873195824618275015532413 60327448434231853130824655)
  ·
    refine ⟨90491172651347779696236983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60327448434231853130824655 90491172651347779696236983)
    ·
      refine ⟨135736758977021669544355475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90491172651347779696236983 135736758977021669544355475)
      ·
        refine ⟨203605138465532504316533213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135736758977021669544355475 203605138465532504316533213)
        ·
          refine ⟨76351926924574689118699955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203605138465532504316533213 76351926924574689118699955)
          ·
            refine ⟨114527890386862033678049933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76351926924574689118699955 114527890386862033678049933)
            ·
              refine ⟨42947958895073262629268725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114527890386862033678049933 42947958895073262629268725)
              ·
                refine ⟨4026371146413118371493943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42947958895073262629268725 4026371146413118371493943)
                ·
                  refine ⟨6039556719619677557240915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026371146413118371493943 6039556719619677557240915)
                  ·
                    refine ⟨9059335079429516335861373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039556719619677557240915 9059335079429516335861373)
                    ·
                      refine ⟨3397250654786068625948015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059335079429516335861373 3397250654786068625948015)
                      ·
                        rfl

theorem cell23_6616122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_6616122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616122 prefixEnd_6616122 := by exact prefixLift 6616122
  have htrace : WordTrace (prefixWord ++ tailWord_6616122) baseStart_6616122 baseEnd_6616122 := by
    simpa [prefixWord, tailWord_6616122, baseEnd_6616122] using wordTrace_append hprefix tailTrace_6616122
  have hstable : (prefixWord ++ tailWord_6616122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616122).length < 2 ^ (prefixWord ++ tailWord_6616122).sum := by decide
  have hdescent : baseEnd_6616122 < baseStart_6616122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616125 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_6616125 : Nat := 118140960795 + 6616125 * 2 ^ 59
def prefixEnd_6616125 : Nat := 4983230072969 + 3 ^ 40 * 6616125 * 2
def baseEnd_6616125 : Nat := 1132417398409344038070167

theorem tailTrace_6616125 : CollatzResearch.WordTrace tailWord_6616125 prefixEnd_6616125 1132417398409344038070167 := by
  unfold tailWord_6616125
  simp only [CollatzResearch.WordTrace]
  refine ⟨241309903155916544035657829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160873268770611029357105219 241309903155916544035657829)
  ·
    refine ⟨45245606841734352006685843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241309903155916544035657829 45245606841734352006685843)
    ·
      refine ⟨67868410262601528010028765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45245606841734352006685843 67868410262601528010028765)
      ·
        refine ⟨25450653848475573003760787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67868410262601528010028765 25450653848475573003760787)
        ·
          refine ⟨38175980772713359505641181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25450653848475573003760787 38175980772713359505641181)
          ·
            refine ⟨14315992789767509814615443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38175980772713359505641181 14315992789767509814615443)
            ·
              refine ⟨21473989184651264721923165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14315992789767509814615443 21473989184651264721923165)
              ·
                refine ⟨8052745944244224270721187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21473989184651264721923165 8052745944244224270721187)
                ·
                  refine ⟨12079118916366336406081781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8052745944244224270721187 12079118916366336406081781)
                  ·
                    refine ⟨1132417398409344038070167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12079118916366336406081781 1132417398409344038070167)
                    ·
                      rfl

theorem cell23_6616125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_6616125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616125 prefixEnd_6616125 := by exact prefixLift 6616125
  have htrace : WordTrace (prefixWord ++ tailWord_6616125) baseStart_6616125 baseEnd_6616125 := by
    simpa [prefixWord, tailWord_6616125, baseEnd_6616125] using wordTrace_append hprefix tailTrace_6616125
  have hstable : (prefixWord ++ tailWord_6616125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616125).length < 2 ^ (prefixWord ++ tailWord_6616125).sum := by decide
  have hdescent : baseEnd_6616125 < baseStart_6616125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616148 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_6616148 : Nat := 118140960795 + 6616148 * 2 ^ 59
def prefixEnd_6616148 : Nat := 4983230072969 + 3 ^ 40 * 6616148 * 2
def baseEnd_6616148 : Nat := 3397264005283085524222895

theorem tailTrace_6616148 : CollatzResearch.WordTrace tailWord_6616148 prefixEnd_6616148 3397264005283085524222895 := by
  unfold tailWord_6616148
  simp only [CollatzResearch.WordTrace]
  refine ⟨120655371017416609481872549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160873828023222145975830065 120655371017416609481872549)
  ·
    refine ⟨22622882065765614277851103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120655371017416609481872549 22622882065765614277851103)
    ·
      refine ⟨33934323098648421416776655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22622882065765614277851103 33934323098648421416776655)
      ·
        refine ⟨50901484647972632125164983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33934323098648421416776655 50901484647972632125164983)
        ·
          refine ⟨76352226971958948187747475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50901484647972632125164983 76352226971958948187747475)
          ·
            refine ⟨114528340457938422281621213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76352226971958948187747475 114528340457938422281621213)
            ·
              refine ⟨42948127671726908355607955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114528340457938422281621213 42948127671726908355607955)
              ·
                refine ⟨64422191507590362533411933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42948127671726908355607955 64422191507590362533411933)
                ·
                  refine ⟨24158321815346385950029475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64422191507590362533411933 24158321815346385950029475)
                  ·
                    refine ⟨36237482723019578925044213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24158321815346385950029475 36237482723019578925044213)
                    ·
                      refine ⟨3397264005283085524222895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36237482723019578925044213 3397264005283085524222895)
                      ·
                        rfl

theorem cell23_6616148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_6616148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616148 prefixEnd_6616148 := by exact prefixLift 6616148
  have htrace : WordTrace (prefixWord ++ tailWord_6616148) baseStart_6616148 baseEnd_6616148 := by
    simpa [prefixWord, tailWord_6616148, baseEnd_6616148] using wordTrace_append hprefix tailTrace_6616148
  have hstable : (prefixWord ++ tailWord_6616148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616148).length < 2 ^ (prefixWord ++ tailWord_6616148).sum := by decide
  have hdescent : baseEnd_6616148 < baseStart_6616148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616151 : List Nat := [1, 1, 3, 2, 2, 1, 1, 12]
def baseStart_6616151 : Nat := 118140960795 + 6616151 * 2 ^ 59
def prefixEnd_6616151 : Nat := 4983230072969 + 3 ^ 40 * 6616151 * 2
def baseEnd_6616151 : Nat := 125824649841668481943903

theorem tailTrace_6616151 : CollatzResearch.WordTrace tailWord_6616151 prefixEnd_6616151 125824649841668481943903 := by
  unfold tailWord_6616151
  simp only [CollatzResearch.WordTrace]
  refine ⟨241310851453822350476104307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160873900969214900317402871 241310851453822350476104307)
  ·
    refine ⟨361966277180733525714156461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241310851453822350476104307 361966277180733525714156461)
    ·
      refine ⟨135737353942775072142808673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361966277180733525714156461 135737353942775072142808673)
      ·
        refine ⟨101803015457081304107106505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135737353942775072142808673 101803015457081304107106505)
        ·
          refine ⟨76352261592810978080329879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101803015457081304107106505 76352261592810978080329879)
          ·
            refine ⟨114528392389216467120494819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76352261592810978080329879 114528392389216467120494819)
            ·
              refine ⟨171792588583824700680742229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114528392389216467120494819 171792588583824700680742229)
              ·
                refine ⟨125824649841668481943903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 171792588583824700680742229 125824649841668481943903)
                ·
                  rfl

theorem cell23_6616151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 12].length) (baseStart_6616151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616151 prefixEnd_6616151 := by exact prefixLift 6616151
  have htrace : WordTrace (prefixWord ++ tailWord_6616151) baseStart_6616151 baseEnd_6616151 := by
    simpa [prefixWord, tailWord_6616151, baseEnd_6616151] using wordTrace_append hprefix tailTrace_6616151
  have hstable : (prefixWord ++ tailWord_6616151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616151).length < 2 ^ (prefixWord ++ tailWord_6616151).sum := by decide
  have hdescent : baseEnd_6616151 < baseStart_6616151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616162 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6616162 : Nat := 118140960795 + 6616162 * 2 ^ 59
def prefixEnd_6616162 : Nat := 4983230072969 + 3 ^ 40 * 6616162 * 2
def baseEnd_6616162 : Nat := 3397271194012248469447831

theorem tailTrace_6616162 : CollatzResearch.WordTrace tailWord_6616162 prefixEnd_6616162 3397271194012248469447831 := by
  unfold tailWord_6616162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60327813164195624838688685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160874168437854999569836493 60327813164195624838688685)
  ·
    refine ⟨22622929936573359314508257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60327813164195624838688685 22622929936573359314508257)
    ·
      refine ⟨16967197452430019485881193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22622929936573359314508257 16967197452430019485881193)
      ·
        refine ⟨12725398089322514614410895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16967197452430019485881193 12725398089322514614410895)
        ·
          refine ⟨19088097133983771921616343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12725398089322514614410895 19088097133983771921616343)
          ·
            refine ⟨28632145700975657882424515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19088097133983771921616343 28632145700975657882424515)
            ·
              refine ⟨42948218551463486823636773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28632145700975657882424515 42948218551463486823636773)
              ·
                refine ⟨8052790978399403779431895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42948218551463486823636773 8052790978399403779431895)
                ·
                  refine ⟨12079186467599105669147843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8052790978399403779431895 12079186467599105669147843)
                  ·
                    refine ⟨18118779701398658503721765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12079186467599105669147843 18118779701398658503721765)
                    ·
                      refine ⟨3397271194012248469447831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18118779701398658503721765 3397271194012248469447831)
                      ·
                        rfl

theorem cell23_6616162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6616162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616162 prefixEnd_6616162 := by exact prefixLift 6616162
  have htrace : WordTrace (prefixWord ++ tailWord_6616162) baseStart_6616162 baseEnd_6616162 := by
    simpa [prefixWord, tailWord_6616162, baseEnd_6616162] using wordTrace_append hprefix tailTrace_6616162
  have hstable : (prefixWord ++ tailWord_6616162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616162).length < 2 ^ (prefixWord ++ tailWord_6616162).sum := by decide
  have hdescent : baseEnd_6616162 < baseStart_6616162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616171 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 6]
def baseStart_6616171 : Nat := 118140960795 + 6616171 * 2 ^ 59
def prefixEnd_6616171 : Nat := 4983230072969 + 3 ^ 40 * 6616171 * 2
def baseEnd_6616171 : Nat := 3397275815338138934235289

theorem tailTrace_6616171 : CollatzResearch.WordTrace tailWord_6616171 prefixEnd_6616171 3397275815338138934235289 := by
  unfold tailWord_6616171
  simp only [CollatzResearch.WordTrace]
  refine ⟨241311580913749893891832367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160874387275833262594554911 241311580913749893891832367)
  ·
    refine ⟨361967371370624840837748551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241311580913749893891832367 361967371370624840837748551)
    ·
      refine ⟨542951057055937261256622827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361967371370624840837748551 542951057055937261256622827)
      ·
        refine ⟨814426585583905891884934241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542951057055937261256622827 814426585583905891884934241)
        ·
          refine ⟨610819939187929418913700681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814426585583905891884934241 610819939187929418913700681)
          ·
            refine ⟨458114954390947064185275511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610819939187929418913700681 458114954390947064185275511)
            ·
              refine ⟨687172431586420596277913267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458114954390947064185275511 687172431586420596277913267)
              ·
                refine ⟨1030758647379630894416869901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687172431586420596277913267 1030758647379630894416869901)
                ·
                  refine ⟨386534492767361585406326213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030758647379630894416869901 386534492767361585406326213)
                  ·
                    refine ⟨72475217393880297263686165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 386534492767361585406326213 72475217393880297263686165)
                    ·
                      refine ⟨3397275815338138934235289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72475217393880297263686165 3397275815338138934235289)
                      ·
                        rfl

theorem cell23_6616171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_6616171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616171 prefixEnd_6616171 := by exact prefixLift 6616171
  have htrace : WordTrace (prefixWord ++ tailWord_6616171) baseStart_6616171 baseEnd_6616171 := by
    simpa [prefixWord, tailWord_6616171, baseEnd_6616171] using wordTrace_append hprefix tailTrace_6616171
  have hstable : (prefixWord ++ tailWord_6616171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616171).length < 2 ^ (prefixWord ++ tailWord_6616171).sum := by decide
  have hdescent : baseEnd_6616171 < baseStart_6616171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616182 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_6616182 : Nat := 118140960795 + 6616182 * 2 ^ 59
def prefixEnd_6616182 : Nat := 4983230072969 + 3 ^ 40 * 6616182 * 2
def baseEnd_6616182 : Nat := 3397281463625338391197739

theorem tailTrace_6616182 : CollatzResearch.WordTrace tailWord_6616182 prefixEnd_6616182 3397281463625338391197739 := by
  unfold tailWord_6616182
  simp only [CollatzResearch.WordTrace]
  refine ⟨15081998882294377673155175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160874654744473361846988533 15081998882294377673155175)
  ·
    refine ⟨22622998323441566509732763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15081998882294377673155175 22622998323441566509732763)
    ·
      refine ⟨33934497485162349764599145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22622998323441566509732763 33934497485162349764599145)
      ·
        refine ⟨25450873113871762323449359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33934497485162349764599145 25450873113871762323449359)
        ·
          refine ⟨38176309670807643485174039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25450873113871762323449359 38176309670807643485174039)
          ·
            refine ⟨57264464506211465227761059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38176309670807643485174039 57264464506211465227761059)
            ·
              refine ⟨85896696759317197841641589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57264464506211465227761059 85896696759317197841641589)
              ·
                refine ⟨8052815321185987297653899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85896696759317197841641589 8052815321185987297653899)
                ·
                  refine ⟨12079222981778980946480849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8052815321185987297653899 12079222981778980946480849)
                  ·
                    refine ⟨9059417236334235709860637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12079222981778980946480849 9059417236334235709860637)
                    ·
                      refine ⟨3397281463625338391197739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059417236334235709860637 3397281463625338391197739)
                      ·
                        rfl

theorem cell23_6616182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_6616182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616182 prefixEnd_6616182 := by exact prefixLift 6616182
  have htrace : WordTrace (prefixWord ++ tailWord_6616182) baseStart_6616182 baseEnd_6616182 := by
    simpa [prefixWord, tailWord_6616182, baseEnd_6616182] using wordTrace_append hprefix tailTrace_6616182
  have hstable : (prefixWord ++ tailWord_6616182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616182).length < 2 ^ (prefixWord ++ tailWord_6616182).sum := by decide
  have hdescent : baseEnd_6616182 < baseStart_6616182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616185 : List Nat := [1, 2, 1, 3, 6, 1, 9]
def baseStart_6616185 : Nat := 118140960795 + 6616185 * 2 ^ 59
def prefixEnd_6616185 : Nat := 4983230072969 + 3 ^ 40 * 6616185 * 2
def baseEnd_6616185 : Nat := 41941765482312368882225

theorem tailTrace_6616185 : CollatzResearch.WordTrace tailWord_6616185 prefixEnd_6616185 41941765482312368882225 := by
  unfold tailWord_6616185
  simp only [CollatzResearch.WordTrace]
  refine ⟨241312091535699174282842009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160874727690466116188561339 241312091535699174282842009)
  ·
    refine ⟨180984068651774380712131507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241312091535699174282842009 180984068651774380712131507)
    ·
      refine ⟨271476102977661571068197261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180984068651774380712131507 271476102977661571068197261)
      ·
        refine ⟨101803538616623089150573973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271476102977661571068197261 101803538616623089150573973)
        ·
          refine ⟨4772040872654207303933155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101803538616623089150573973 4772040872654207303933155)
          ·
            refine ⟨7158061308981310955899733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772040872654207303933155 7158061308981310955899733)
            ·
              refine ⟨41941765482312368882225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7158061308981310955899733 41941765482312368882225)
              ·
                rfl

theorem cell23_6616185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 9].length) (baseStart_6616185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616185 prefixEnd_6616185 := by exact prefixLift 6616185
  have htrace : WordTrace (prefixWord ++ tailWord_6616185) baseStart_6616185 baseEnd_6616185 := by
    simpa [prefixWord, tailWord_6616185, baseEnd_6616185] using wordTrace_append hprefix tailTrace_6616185
  have hstable : (prefixWord ++ tailWord_6616185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616185).length < 2 ^ (prefixWord ++ tailWord_6616185).sum := by decide
  have hdescent : baseEnd_6616185 < baseStart_6616185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616190 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6616190 : Nat := 118140960795 + 6616190 * 2 ^ 59
def prefixEnd_6616190 : Nat := 4983230072969 + 3 ^ 40 * 6616190 * 2
def baseEnd_6616190 : Nat := 3397285571470574359897703

theorem tailTrace_6616190 : CollatzResearch.WordTrace tailWord_6616190 prefixEnd_6616190 3397285571470574359897703 := by
  unfold tailWord_6616190
  simp only [CollatzResearch.WordTrace]
  refine ⟨30164034237585132517096753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160874849267120706757849349 30164034237585132517096753)
  ·
    refine ⟨22623025678188849387822565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30164034237585132517096753 22623025678188849387822565)
    ·
      refine ⟨4241817314660409260216731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22623025678188849387822565 4241817314660409260216731)
      ·
        refine ⟨6362725971990613890325097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241817314660409260216731 6362725971990613890325097)
        ·
          refine ⟨4772044478992960417743823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6362725971990613890325097 4772044478992960417743823)
          ·
            refine ⟨7158066718489440626615735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772044478992960417743823 7158066718489440626615735)
            ·
              refine ⟨10737100077734160939923603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158066718489440626615735 10737100077734160939923603)
              ·
                refine ⟨16105650116601241409885405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10737100077734160939923603 16105650116601241409885405)
                ·
                  refine ⟨6039618793725465528707027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16105650116601241409885405 6039618793725465528707027)
                  ·
                    refine ⟨9059428190588198293060541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039618793725465528707027 9059428190588198293060541)
                    ·
                      refine ⟨3397285571470574359897703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059428190588198293060541 3397285571470574359897703)
                      ·
                        rfl

theorem cell23_6616190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6616190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616190 prefixEnd_6616190 := by exact prefixLift 6616190
  have htrace : WordTrace (prefixWord ++ tailWord_6616190) baseStart_6616190 baseEnd_6616190 := by
    simpa [prefixWord, tailWord_6616190, baseEnd_6616190] using wordTrace_append hprefix tailTrace_6616190
  have hstable : (prefixWord ++ tailWord_6616190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616190).length < 2 ^ (prefixWord ++ tailWord_6616190).sum := by decide
  have hdescent : baseEnd_6616190 < baseStart_6616190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616195 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 3]
def baseStart_6616195 : Nat := 118140960795 + 6616195 * 2 ^ 59
def prefixEnd_6616195 : Nat := 4983230072969 + 3 ^ 40 * 6616195 * 2
def baseEnd_6616195 : Nat := 3397288138873846840335179

theorem tailTrace_6616195 : CollatzResearch.WordTrace tailWord_6616195 prefixEnd_6616195 3397288138873846840335179 := by
  unfold tailWord_6616195
  simp only [CollatzResearch.WordTrace]
  refine ⟨241312456265662945990706039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160874970843775297327137359 241312456265662945990706039)
  ·
    refine ⟨361968684398494418986059059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241312456265662945990706039 361968684398494418986059059)
    ·
      refine ⟨542953026597741628479088589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361968684398494418986059059 542953026597741628479088589)
      ·
        refine ⟨203607384974153110679658221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542953026597741628479088589 203607384974153110679658221)
        ·
          refine ⟨76352769365307416504871833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203607384974153110679658221 76352769365307416504871833)
          ·
            refine ⟨57264577023980562378653875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76352769365307416504871833 57264577023980562378653875)
            ·
              refine ⟨85896865535970843567980813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57264577023980562378653875 85896865535970843567980813)
              ·
                refine ⟨32211324575989066337992805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85896865535970843567980813 32211324575989066337992805)
                ·
                  refine ⟨6039623357997949938373651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32211324575989066337992805 6039623357997949938373651)
                  ·
                    refine ⟨9059435036996924907560477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039623357997949938373651 9059435036996924907560477)
                    ·
                      refine ⟨3397288138873846840335179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059435036996924907560477 3397288138873846840335179)
                      ·
                        rfl

theorem cell23_6616195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_6616195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616195 prefixEnd_6616195 := by exact prefixLift 6616195
  have htrace : WordTrace (prefixWord ++ tailWord_6616195) baseStart_6616195 baseEnd_6616195 := by
    simpa [prefixWord, tailWord_6616195, baseEnd_6616195] using wordTrace_append hprefix tailTrace_6616195
  have hstable : (prefixWord ++ tailWord_6616195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616195).length < 2 ^ (prefixWord ++ tailWord_6616195).sum := by decide
  have hdescent : baseEnd_6616195 < baseStart_6616195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616303 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 2, 2, 2]
def baseStart_6616303 : Nat := 118140960795 + 6616303 * 2 ^ 59
def prefixEnd_6616303 : Nat := 4983230072969 + 3 ^ 40 * 6616303 * 2
def baseEnd_6616303 : Nat := 3397343594784532417784683

theorem tailTrace_6616303 : CollatzResearch.WordTrace tailWord_6616303 prefixEnd_6616303 3397343594784532417784683 := by
  unfold tailWord_6616303
  simp only [CollatzResearch.WordTrace]
  refine ⟨241316395349271680435637563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160877596899514453623758375 241316395349271680435637563)
  ·
    refine ⟨361974593023907520653456345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241316395349271680435637563 361974593023907520653456345)
    ·
      refine ⟨271480944767930640490092259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361974593023907520653456345 271480944767930640490092259)
      ·
        refine ⟨407221417151895960735138389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271480944767930640490092259 407221417151895960735138389)
        ·
          refine ⟨4772125982248780789864903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 407221417151895960735138389 4772125982248780789864903)
          ·
            refine ⟨7158188973373171184797355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772125982248780789864903 7158188973373171184797355)
            ·
              refine ⟨10737283460059756777196033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158188973373171184797355 10737283460059756777196033)
              ·
                refine ⟨8052962595044817582897025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10737283460059756777196033 8052962595044817582897025)
                ·
                  refine ⟨6039721946283613187172769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8052962595044817582897025 6039721946283613187172769)
                  ·
                    refine ⟨4529791459712709890379577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6039721946283613187172769 4529791459712709890379577)
                    ·
                      refine ⟨3397343594784532417784683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529791459712709890379577 3397343594784532417784683)
                      ·
                        rfl

theorem cell23_6616303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 2, 2].length) (baseStart_6616303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616303 prefixEnd_6616303 := by exact prefixLift 6616303
  have htrace : WordTrace (prefixWord ++ tailWord_6616303) baseStart_6616303 baseEnd_6616303 := by
    simpa [prefixWord, tailWord_6616303, baseEnd_6616303] using wordTrace_append hprefix tailTrace_6616303
  have hstable : (prefixWord ++ tailWord_6616303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616303).length < 2 ^ (prefixWord ++ tailWord_6616303).sum := by decide
  have hdescent : baseEnd_6616303 < baseStart_6616303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616345 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 3]
def baseStart_6616345 : Nat := 118140960795 + 6616345 * 2 ^ 59
def prefixEnd_6616345 : Nat := 4983230072969 + 3 ^ 40 * 6616345 * 2
def baseEnd_6616345 : Nat := 3397365160972021253459489

theorem tailTrace_6616345 : CollatzResearch.WordTrace tailWord_6616345 prefixEnd_6616345 3397365160972021253459489 := by
  unfold tailWord_6616345
  simp only [CollatzResearch.WordTrace]
  refine ⟨241317927215119521608666489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160878618143413014405777659 241317927215119521608666489)
  ·
    refine ⟨180988445411339641206499867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241317927215119521608666489 180988445411339641206499867)
    ·
      refine ⟨271482668117009461809749801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180988445411339641206499867 271482668117009461809749801)
      ·
        refine ⟨203612001087757096357312351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271482668117009461809749801 203612001087757096357312351)
        ·
          refine ⟨305418001631635644535968527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203612001087757096357312351 305418001631635644535968527)
          ·
            refine ⟨458127002447453466803952791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305418001631635644535968527 458127002447453466803952791)
            ·
              refine ⟨687190503671180200205929187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458127002447453466803952791 687190503671180200205929187)
              ·
                refine ⟨1030785755506770300308893781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687190503671180200205929187 1030785755506770300308893781)
                ·
                  refine ⟨12079520572344964456744849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1030785755506770300308893781 12079520572344964456744849)
                  ·
                    refine ⟨9059640429258723342558637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12079520572344964456744849 9059640429258723342558637)
                    ·
                      refine ⟨3397365160972021253459489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059640429258723342558637 3397365160972021253459489)
                      ·
                        rfl

theorem cell23_6616345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_6616345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616345 prefixEnd_6616345 := by exact prefixLift 6616345
  have htrace : WordTrace (prefixWord ++ tailWord_6616345) baseStart_6616345 baseEnd_6616345 := by
    simpa [prefixWord, tailWord_6616345, baseEnd_6616345] using wordTrace_append hprefix tailTrace_6616345
  have hstable : (prefixWord ++ tailWord_6616345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616345).length < 2 ^ (prefixWord ++ tailWord_6616345).sum := by decide
  have hdescent : baseEnd_6616345 < baseStart_6616345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616369 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 3, 4]
def baseStart_6616369 : Nat := 118140960795 + 6616369 * 2 ^ 59
def prefixEnd_6616369 : Nat := 4983230072969 + 3 ^ 40 * 6616369 * 2
def baseEnd_6616369 : Nat := 1132459161502576386519793

theorem tailTrace_6616369 : CollatzResearch.WordTrace tailWord_6616369 prefixEnd_6616369 1132459161502576386519793 := by
  unfold tailWord_6616369
  simp only [CollatzResearch.WordTrace]
  refine ⟨241318802567032573707540161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160879201711355049138360107 241318802567032573707540161)
  ·
    refine ⟨180989101925274430280655121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241318802567032573707540161 180989101925274430280655121)
    ·
      refine ⟨135741826443955822710491341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180989101925274430280655121 135741826443955822710491341)
      ·
        refine ⟨50903184916483433516434253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135741826443955822710491341 50903184916483433516434253)
        ·
          refine ⟨19088694343681287568662845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50903184916483433516434253 19088694343681287568662845)
          ·
            refine ⟨7158260378880482838248567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19088694343681287568662845 7158260378880482838248567)
            ·
              refine ⟨10737390568320724257372851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158260378880482838248567 10737390568320724257372851)
              ·
                refine ⟨16106085852481086386059277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10737390568320724257372851 16106085852481086386059277)
                ·
                  refine ⟨6039782194680407394772229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16106085852481086386059277 6039782194680407394772229)
                  ·
                    refine ⟨1132459161502576386519793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6039782194680407394772229 1132459161502576386519793)
                    ·
                      rfl

theorem cell23_6616369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_6616369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616369 prefixEnd_6616369 := by exact prefixLift 6616369
  have htrace : WordTrace (prefixWord ++ tailWord_6616369) baseStart_6616369 baseEnd_6616369 := by
    simpa [prefixWord, tailWord_6616369, baseEnd_6616369] using wordTrace_append hprefix tailTrace_6616369
  have hstable : (prefixWord ++ tailWord_6616369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616369).length < 2 ^ (prefixWord ++ tailWord_6616369).sum := by decide
  have hdescent : baseEnd_6616369 < baseStart_6616369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616382 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_6616382 : Nat := 118140960795 + 6616382 * 2 ^ 59
def prefixEnd_6616382 : Nat := 4983230072969 + 3 ^ 40 * 6616382 * 2
def baseEnd_6616382 : Nat := 377487128861804178744091

theorem tailTrace_6616382 : CollatzResearch.WordTrace tailWord_6616382 prefixEnd_6616382 377487128861804178744091 := by
  unfold tailWord_6616382
  simp only [CollatzResearch.WordTrace]
  refine ⟨30164909589498184615970425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160879517810656984618508933 30164909589498184615970425)
  ·
    refine ⟨22623682192123638461977819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30164909589498184615970425 22623682192123638461977819)
    ·
      refine ⟨33935523288185457692966729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22623682192123638461977819 33935523288185457692966729)
      ·
        refine ⟨25451642466139093269725047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33935523288185457692966729 25451642466139093269725047)
        ·
          refine ⟨38177463699208639904587571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25451642466139093269725047 38177463699208639904587571)
          ·
            refine ⟨57266195548812959856881357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38177463699208639904587571 57266195548812959856881357)
            ·
              refine ⟨21474823330804859946330509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57266195548812959856881357 21474823330804859946330509)
              ·
                refine ⟨8053058749051822479873941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21474823330804859946330509 8053058749051822479873941)
                ·
                  refine ⟨377487128861804178744091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8053058749051822479873941 377487128861804178744091)
                  ·
                    rfl

theorem cell23_6616382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_6616382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616382 prefixEnd_6616382 := by exact prefixLift 6616382
  have htrace : WordTrace (prefixWord ++ tailWord_6616382) baseStart_6616382 baseEnd_6616382 := by
    simpa [prefixWord, tailWord_6616382, baseEnd_6616382] using wordTrace_append hprefix tailTrace_6616382
  have hstable : (prefixWord ++ tailWord_6616382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616382).length < 2 ^ (prefixWord ++ tailWord_6616382).sum := by decide
  have hdescent : baseEnd_6616382 < baseStart_6616382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616392 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_6616392 : Nat := 118140960795 + 6616392 * 2 ^ 59
def prefixEnd_6616392 : Nat := 4983230072969 + 3 ^ 40 * 6616392 * 2
def baseEnd_6616392 : Nat := 3397389294562782569571773

theorem tailTrace_6616392 : CollatzResearch.WordTrace tailWord_6616392 prefixEnd_6616392 3397389294562782569571773 := by
  unfold tailWord_6616392
  simp only [CollatzResearch.WordTrace]
  refine ⟨120659820722974624317813715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160879760963966165757084953 120659820722974624317813715)
  ·
    refine ⟨180989731084461936476720573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120659820722974624317813715 180989731084461936476720573)
    ·
      refine ⟨67871149156673226178770215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180989731084461936476720573 67871149156673226178770215)
      ·
        refine ⟨101806723735009839268155323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67871149156673226178770215 101806723735009839268155323)
        ·
          refine ⟨152710085602514758902232985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101806723735009839268155323 152710085602514758902232985)
          ·
            refine ⟨114532564201886069176674739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152710085602514758902232985 114532564201886069176674739)
            ·
              refine ⟨171798846302829103765012109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114532564201886069176674739 171798846302829103765012109)
              ·
                refine ⟨64424567363560913911879541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171798846302829103765012109 64424567363560913911879541)
                ·
                  refine ⟨6039803190333835679238707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64424567363560913911879541 6039803190333835679238707)
                  ·
                    refine ⟨9059704785500753518858061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039803190333835679238707 9059704785500753518858061)
                    ·
                      refine ⟨3397389294562782569571773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059704785500753518858061 3397389294562782569571773)
                      ·
                        rfl

theorem cell23_6616392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_6616392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616392 prefixEnd_6616392 := by exact prefixLift 6616392
  have htrace : WordTrace (prefixWord ++ tailWord_6616392) baseStart_6616392 baseEnd_6616392 := by
    simpa [prefixWord, tailWord_6616392, baseEnd_6616392] using wordTrace_append hprefix tailTrace_6616392
  have hstable : (prefixWord ++ tailWord_6616392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616392).length < 2 ^ (prefixWord ++ tailWord_6616392).sum := by decide
  have hdescent : baseEnd_6616392 < baseStart_6616392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616419 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 2, 3, 2]
def baseStart_6616419 : Nat := 118140960795 + 6616419 * 2 ^ 59
def prefixEnd_6616419 : Nat := 4983230072969 + 3 ^ 40 * 6616419 * 2
def baseEnd_6616419 : Nat := 3397403158540453963934149

theorem tailTrace_6616419 : CollatzResearch.WordTrace tailWord_6616419 prefixEnd_6616419 3397403158540453963934149 := by
  unfold tailWord_6616419
  simp only [CollatzResearch.WordTrace]
  refine ⟨241320626216851432246860311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160880417477900954831240207 241320626216851432246860311)
  ·
    refine ⟨361980939325277148370290467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241320626216851432246860311 361980939325277148370290467)
    ·
      refine ⟨542971408987915722555435701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361980939325277148370290467 542971408987915722555435701)
      ·
        refine ⟨50903569592617098989572097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 542971408987915722555435701 50903569592617098989572097)
        ·
          refine ⟨38177677194462824242179073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50903569592617098989572097 38177677194462824242179073)
          ·
            refine ⟨28633257895847118181634305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38177677194462824242179073 28633257895847118181634305)
            ·
              refine ⟨21474943421885338636225729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28633257895847118181634305 21474943421885338636225729)
              ·
                refine ⟨16106207566414003977169297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21474943421885338636225729 16106207566414003977169297)
                ·
                  refine ⟨12079655674810502982876973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16106207566414003977169297 12079655674810502982876973)
                  ·
                    refine ⟨4529870878053938618578865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12079655674810502982876973 4529870878053938618578865)
                    ·
                      refine ⟨3397403158540453963934149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529870878053938618578865 3397403158540453963934149)
                      ·
                        rfl

theorem cell23_6616419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_6616419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616419 prefixEnd_6616419 := by exact prefixLift 6616419
  have htrace : WordTrace (prefixWord ++ tailWord_6616419) baseStart_6616419 baseEnd_6616419 := by
    simpa [prefixWord, tailWord_6616419, baseEnd_6616419] using wordTrace_append hprefix tailTrace_6616419
  have hstable : (prefixWord ++ tailWord_6616419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616419).length < 2 ^ (prefixWord ++ tailWord_6616419).sum := by decide
  have hdescent : baseEnd_6616419 < baseStart_6616419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616435 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 3]
def baseStart_6616435 : Nat := 118140960795 + 6616435 * 2 ^ 59
def prefixEnd_6616435 : Nat := 4983230072969 + 3 ^ 40 * 6616435 * 2
def baseEnd_6616435 : Nat := 3397411374230925901334075

theorem tailTrace_6616435 : CollatzResearch.WordTrace tailWord_6616435 prefixEnd_6616435 3397411374230925901334075 := by
  unfold tailWord_6616435
  simp only [CollatzResearch.WordTrace]
  refine ⟨241321209784793466979442759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160880806523195644652961839 241321209784793466979442759)
  ·
    refine ⟨361981814677190200469164139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241321209784793466979442759 361981814677190200469164139)
    ·
      refine ⟨542972722015785300703746209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361981814677190200469164139 542972722015785300703746209)
      ·
        refine ⟨407229541511838975527809657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542972722015785300703746209 407229541511838975527809657)
        ·
          refine ⟨305422156133879231645857243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407229541511838975527809657 305422156133879231645857243)
          ·
            refine ⟨458133234200818847468785865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305422156133879231645857243 458133234200818847468785865)
            ·
              refine ⟨343599925650614135601589399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458133234200818847468785865 343599925650614135601589399)
              ·
                refine ⟨515399888475921203402384099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343599925650614135601589399 515399888475921203402384099)
                ·
                  refine ⟨773099832713881805103576149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515399888475921203402384099 773099832713881805103576149)
                  ·
                    refine ⟨9059763664615802403557533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 773099832713881805103576149 9059763664615802403557533)
                    ·
                      refine ⟨3397411374230925901334075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059763664615802403557533 3397411374230925901334075)
                      ·
                        rfl

theorem cell23_6616435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_6616435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616435 prefixEnd_6616435 := by exact prefixLift 6616435
  have htrace : WordTrace (prefixWord ++ tailWord_6616435) baseStart_6616435 baseEnd_6616435 := by
    simpa [prefixWord, tailWord_6616435, baseEnd_6616435] using wordTrace_append hprefix tailTrace_6616435
  have hstable : (prefixWord ++ tailWord_6616435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616435).length < 2 ^ (prefixWord ++ tailWord_6616435).sum := by decide
  have hdescent : baseEnd_6616435 < baseStart_6616435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616472 : List Nat := [2, 1, 2, 5, 2, 1, 10]
def baseStart_6616472 : Nat := 118140960795 + 6616472 * 2 ^ 59
def prefixEnd_6616472 : Nat := 4983230072969 + 3 ^ 40 * 6616472 * 2
def baseEnd_6616472 : Nat := 41943584852038793291005

theorem tailTrace_6616472 : CollatzResearch.WordTrace tailWord_6616472 prefixEnd_6616472 41943584852038793291005 := by
  unfold tailWord_6616472
  simp only [CollatzResearch.WordTrace]
  refine ⟨120661279642829711149269835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160881706190439614865693113 120661279642829711149269835)
  ·
    refine ⟨180991919464244566723904753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120661279642829711149269835 180991919464244566723904753)
    ·
      refine ⟨135743939598183425042928565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180991919464244566723904753 135743939598183425042928565)
      ·
        refine ⟨12725994337329696097774553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135743939598183425042928565 12725994337329696097774553)
        ·
          refine ⟨9544495752997272073330915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12725994337329696097774553 9544495752997272073330915)
          ·
            refine ⟨14316743629495908109996373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9544495752997272073330915 14316743629495908109996373)
            ·
              refine ⟨41943584852038793291005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14316743629495908109996373 41943584852038793291005)
              ·
                rfl

theorem cell23_6616472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 10].length) (baseStart_6616472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616472 prefixEnd_6616472 := by exact prefixLift 6616472
  have htrace : WordTrace (prefixWord ++ tailWord_6616472) baseStart_6616472 baseEnd_6616472 := by
    simpa [prefixWord, tailWord_6616472, baseEnd_6616472] using wordTrace_append hprefix tailTrace_6616472
  have hstable : (prefixWord ++ tailWord_6616472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616472).length < 2 ^ (prefixWord ++ tailWord_6616472).sum := by decide
  have hdescent : baseEnd_6616472 < baseStart_6616472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616476 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_6616476 : Nat := 118140960795 + 6616476 * 2 ^ 59
def prefixEnd_6616476 : Nat := 4983230072969 + 3 ^ 40 * 6616476 * 2
def baseEnd_6616476 : Nat := 1132477475645920080307129

theorem tailTrace_6616476 : CollatzResearch.WordTrace tailWord_6616476 prefixEnd_6616476 1132477475645920080307129 := by
  unfold tailWord_6616476
  simp only [CollatzResearch.WordTrace]
  refine ⟨120661352588822465490842641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160881803451763287321123521 120661352588822465490842641)
  ·
    refine ⟨90496014441616849118131981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120661352588822465490842641 90496014441616849118131981)
    ·
      refine ⟨33936005415606318419299493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90496014441616849118131981 33936005415606318419299493)
      ·
        refine ⟨6363001015426184703618655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33936005415606318419299493 6363001015426184703618655)
        ·
          refine ⟨9544501523139277055427983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6363001015426184703618655 9544501523139277055427983)
          ·
            refine ⟨14316752284708915583141975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9544501523139277055427983 14316752284708915583141975)
            ·
              refine ⟨21475128427063373374712963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14316752284708915583141975 21475128427063373374712963)
              ·
                refine ⟨32212692640595060062069445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21475128427063373374712963 32212692640595060062069445)
                ·
                  refine ⟨6039879870111573761638021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32212692640595060062069445 6039879870111573761638021)
                  ·
                    refine ⟨1132477475645920080307129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6039879870111573761638021 1132477475645920080307129)
                    ·
                      rfl

theorem cell23_6616476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_6616476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616476 prefixEnd_6616476 := by exact prefixLift 6616476
  have htrace : WordTrace (prefixWord ++ tailWord_6616476) baseStart_6616476 baseEnd_6616476 := by
    simpa [prefixWord, tailWord_6616476, baseEnd_6616476] using wordTrace_append hprefix tailTrace_6616476
  have hstable : (prefixWord ++ tailWord_6616476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616476).length < 2 ^ (prefixWord ++ tailWord_6616476).sum := by decide
  have hdescent : baseEnd_6616476 < baseStart_6616476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616485 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_6616485 : Nat := 118140960795 + 6616485 * 2 ^ 59
def prefixEnd_6616485 : Nat := 4983230072969 + 3 ^ 40 * 6616485 * 2
def baseEnd_6616485 : Nat := 1132479016087883568569615

theorem tailTrace_6616485 : CollatzResearch.WordTrace tailWord_6616485 prefixEnd_6616485 1132479016087883568569615 := by
  unfold tailWord_6616485
  simp only [CollatzResearch.WordTrace]
  refine ⟨241323033434612325518762909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160882022289741550345841939 241323033434612325518762909)
  ·
    refine ⟨90496137537979622069536091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241323033434612325518762909 90496137537979622069536091)
    ·
      refine ⟨135744206306969433104304137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90496137537979622069536091 135744206306969433104304137)
      ·
        refine ⟨101808154730227074828228103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135744206306969433104304137 101808154730227074828228103)
        ·
          refine ⟨152712232095340612242342155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101808154730227074828228103 152712232095340612242342155)
          ·
            refine ⟨229068348143010918363513233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152712232095340612242342155 229068348143010918363513233)
            ·
              refine ⟨171801261107258188772634925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229068348143010918363513233 171801261107258188772634925)
              ·
                refine ⟨64425472915221820789738097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171801261107258188772634925 64425472915221820789738097)
                ·
                  refine ⟨48319104686416365592303573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64425472915221820789738097 48319104686416365592303573)
                  ·
                    refine ⟨1132479016087883568569615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48319104686416365592303573 1132479016087883568569615)
                    ·
                      rfl

theorem cell23_6616485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_6616485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616485 prefixEnd_6616485 := by exact prefixLift 6616485
  have htrace : WordTrace (prefixWord ++ tailWord_6616485) baseStart_6616485 baseEnd_6616485 := by
    simpa [prefixWord, tailWord_6616485, baseEnd_6616485] using wordTrace_append hprefix tailTrace_6616485
  have hstable : (prefixWord ++ tailWord_6616485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616485).length < 2 ^ (prefixWord ++ tailWord_6616485).sum := by decide
  have hdescent : baseEnd_6616485 < baseStart_6616485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616493 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_6616493 : Nat := 118140960795 + 6616493 * 2 ^ 59
def prefixEnd_6616493 : Nat := 4983230072969 + 3 ^ 40 * 6616493 * 2
def baseEnd_6616493 : Nat := 1132480385369628891469603

theorem tailTrace_6616493 : CollatzResearch.WordTrace tailWord_6616493 prefixEnd_6616493 1132480385369628891469603 := by
  unfold tailWord_6616493
  simp only [CollatzResearch.WordTrace]
  refine ⟨241323325218583342885054133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160882216812388895256702755 241323325218583342885054133)
  ·
    refine ⟨22624061739242188395473825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241323325218583342885054133 22624061739242188395473825)
    ·
      refine ⟨16968046304431641296605369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22624061739242188395473825 16968046304431641296605369)
      ·
        refine ⟨12726034728323730972454027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16968046304431641296605369 12726034728323730972454027)
        ·
          refine ⟨19089052092485596458681041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12726034728323730972454027 19089052092485596458681041)
          ·
            refine ⟨14316789069364197344010781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19089052092485596458681041 14316789069364197344010781)
            ·
              refine ⟨5368795901011574004004043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14316789069364197344010781 5368795901011574004004043)
              ·
                refine ⟨8053193851517361006006065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368795901011574004004043 8053193851517361006006065)
                ·
                  refine ⟨6039895388638020754504549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8053193851517361006006065 6039895388638020754504549)
                  ·
                    refine ⟨1132480385369628891469603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6039895388638020754504549 1132480385369628891469603)
                    ·
                      rfl

theorem cell23_6616493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_6616493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616493 prefixEnd_6616493 := by exact prefixLift 6616493
  have htrace : WordTrace (prefixWord ++ tailWord_6616493) baseStart_6616493 baseEnd_6616493 := by
    simpa [prefixWord, tailWord_6616493, baseEnd_6616493] using wordTrace_append hprefix tailTrace_6616493
  have hstable : (prefixWord ++ tailWord_6616493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616493).length < 2 ^ (prefixWord ++ tailWord_6616493).sum := by decide
  have hdescent : baseEnd_6616493 < baseStart_6616493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616495 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_6616495 : Nat := 118140960795 + 6616495 * 2 ^ 59
def prefixEnd_6616495 : Nat := 4983230072969 + 3 ^ 40 * 6616495 * 2
def baseEnd_6616495 : Nat := 3397442183070195666583799

theorem tailTrace_6616495 : CollatzResearch.WordTrace tailWord_6616495 prefixEnd_6616495 3397442183070195666583799 := by
  unfold tailWord_6616495
  simp only [CollatzResearch.WordTrace]
  refine ⟨241323398164576097226626939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160882265443050731484417959 241323398164576097226626939)
  ·
    refine ⟨361985097246864145839940409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241323398164576097226626939 361985097246864145839940409)
    ·
      refine ⟨271488822935148109379955307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361985097246864145839940409 271488822935148109379955307)
      ·
        refine ⟨407233234402722164069932961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271488822935148109379955307 407233234402722164069932961)
        ·
          refine ⟨305424925802041623052449721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407233234402722164069932961 305424925802041623052449721)
          ·
            refine ⟨229068694351531217289337291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305424925802041623052449721 229068694351531217289337291)
            ·
              refine ⟨343603041527296825934005937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229068694351531217289337291 343603041527296825934005937)
              ·
                refine ⟨257702281145472619450504453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343603041527296825934005937 257702281145472619450504453)
                ·
                  refine ⟨48319177714776116146969585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257702281145472619450504453 48319177714776116146969585)
                  ·
                    refine ⟨36239383286082087110227189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48319177714776116146969585 36239383286082087110227189)
                    ·
                      refine ⟨3397442183070195666583799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36239383286082087110227189 3397442183070195666583799)
                      ·
                        rfl

theorem cell23_6616495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_6616495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616495 prefixEnd_6616495 := by exact prefixLift 6616495
  have htrace : WordTrace (prefixWord ++ tailWord_6616495) baseStart_6616495 baseEnd_6616495 := by
    simpa [prefixWord, tailWord_6616495, baseEnd_6616495] using wordTrace_append hprefix tailTrace_6616495
  have hstable : (prefixWord ++ tailWord_6616495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616495).length < 2 ^ (prefixWord ++ tailWord_6616495).sum := by decide
  have hdescent : baseEnd_6616495 < baseStart_6616495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616499 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 3]
def baseStart_6616499 : Nat := 118140960795 + 6616499 * 2 ^ 59
def prefixEnd_6616499 : Nat := 4983230072969 + 3 ^ 40 * 6616499 * 2
def baseEnd_6616499 : Nat := 3397444236992813650933781

theorem tailTrace_6616499 : CollatzResearch.WordTrace tailWord_6616499 prefixEnd_6616499 3397444236992813650933781 := by
  unfold tailWord_6616499
  simp only [CollatzResearch.WordTrace]
  refine ⟨241323544056561605909772551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160882362704374403939848367 241323544056561605909772551)
  ·
    refine ⟨361985316084842408864658827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241323544056561605909772551 361985316084842408864658827)
    ·
      refine ⟨542977974127263613296988241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361985316084842408864658827 542977974127263613296988241)
      ·
        refine ⟨407233480595447709972741181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542977974127263613296988241 407233480595447709972741181)
        ·
          refine ⟨152712555223292891239777943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407233480595447709972741181 152712555223292891239777943)
          ·
            refine ⟨229068832834939336859666915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152712555223292891239777943 229068832834939336859666915)
            ·
              refine ⟨343603249252409005289500373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229068832834939336859666915 343603249252409005289500373)
              ·
                refine ⟨8053201154353336061472665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 343603249252409005289500373 8053201154353336061472665)
                ·
                  refine ⟨6039900865765002046104499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8053201154353336061472665 6039900865765002046104499)
                  ·
                    refine ⟨9059851298647503069156749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039900865765002046104499 9059851298647503069156749)
                    ·
                      refine ⟨3397444236992813650933781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059851298647503069156749 3397444236992813650933781)
                      ·
                        rfl

theorem cell23_6616499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 1, 3].length) (baseStart_6616499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616499 prefixEnd_6616499 := by exact prefixLift 6616499
  have htrace : WordTrace (prefixWord ++ tailWord_6616499) baseStart_6616499 baseEnd_6616499 := by
    simpa [prefixWord, tailWord_6616499, baseEnd_6616499] using wordTrace_append hprefix tailTrace_6616499
  have hstable : (prefixWord ++ tailWord_6616499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616499).length < 2 ^ (prefixWord ++ tailWord_6616499).sum := by decide
  have hdescent : baseEnd_6616499 < baseStart_6616499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616515 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 1, 8]
def baseStart_6616515 : Nat := 118140960795 + 6616515 * 2 ^ 59
def prefixEnd_6616515 : Nat := 4983230072969 + 3 ^ 40 * 6616515 * 2
def baseEnd_6616515 : Nat := 1132484150894428529444569

theorem tailTrace_6616515 : CollatzResearch.WordTrace tailWord_6616515 prefixEnd_6616515 1132484150894428529444569 := by
  unfold tailWord_6616515
  simp only [CollatzResearch.WordTrace]
  refine ⟨241324127624503640642354999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160882751749669093761569999 241324127624503640642354999)
  ·
    refine ⟨361986191436755460963532499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241324127624503640642354999 361986191436755460963532499)
    ·
      refine ⟨542979287155133191445298749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361986191436755460963532499 542979287155133191445298749)
      ·
        refine ⟨203617232683174946791987031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542979287155133191445298749 203617232683174946791987031)
        ·
          refine ⟨305425849024762420187980547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203617232683174946791987031 305425849024762420187980547)
          ·
            refine ⟨458138773537143630281970821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305425849024762420187980547 458138773537143630281970821)
            ·
              refine ⟨85901020038214430677869529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 458138773537143630281970821 85901020038214430677869529)
              ·
                refine ⟨64425765028660823008402147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85901020038214430677869529 64425765028660823008402147)
                ·
                  refine ⟨96638647542991234512603221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64425765028660823008402147 96638647542991234512603221)
                  ·
                    refine ⟨1132484150894428529444569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96638647542991234512603221 1132484150894428529444569)
                    ·
                      rfl

theorem cell23_6616515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 8].length) (baseStart_6616515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616515 prefixEnd_6616515 := by exact prefixLift 6616515
  have htrace : WordTrace (prefixWord ++ tailWord_6616515) baseStart_6616515 baseEnd_6616515 := by
    simpa [prefixWord, tailWord_6616515, baseEnd_6616515] using wordTrace_append hprefix tailTrace_6616515
  have hstable : (prefixWord ++ tailWord_6616515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616515).length < 2 ^ (prefixWord ++ tailWord_6616515).sum := by decide
  have hdescent : baseEnd_6616515 < baseStart_6616515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616516 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_6616516 : Nat := 118140960795 + 6616516 * 2 ^ 59
def prefixEnd_6616516 : Nat := 4983230072969 + 3 ^ 40 * 6616516 * 2
def baseEnd_6616516 : Nat := 3397452966163940084421203

theorem tailTrace_6616516 : CollatzResearch.WordTrace tailWord_6616516 prefixEnd_6616516 3397452966163940084421203 := by
  unfold tailWord_6616516
  simp only [CollatzResearch.WordTrace]
  refine ⟨120662082048750008906570701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160882776065000011875427601 120662082048750008906570701)
  ·
    refine ⟨45248280768281253339964013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120662082048750008906570701 45248280768281253339964013)
    ·
      refine ⟨16968105288105470002486505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45248280768281253339964013 16968105288105470002486505)
      ·
        refine ⟨12726078966079102501864879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16968105288105470002486505 12726078966079102501864879)
        ·
          refine ⟨19089118449118653752797319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12726078966079102501864879 19089118449118653752797319)
          ·
            refine ⟨28633677673677980629195979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19089118449118653752797319 28633677673677980629195979)
            ·
              refine ⟨42950516510516970943793969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28633677673677980629195979 42950516510516970943793969)
              ·
                refine ⟨32212887382887728207845477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42950516510516970943793969 32212887382887728207845477)
                ·
                  refine ⟨6039916384291449038971027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32212887382887728207845477 6039916384291449038971027)
                  ·
                    refine ⟨9059874576437173558456541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039916384291449038971027 9059874576437173558456541)
                    ·
                      refine ⟨3397452966163940084421203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059874576437173558456541 3397452966163940084421203)
                      ·
                        rfl

theorem cell23_6616516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_6616516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616516 prefixEnd_6616516 := by exact prefixLift 6616516
  have htrace : WordTrace (prefixWord ++ tailWord_6616516) baseStart_6616516 baseEnd_6616516 := by
    simpa [prefixWord, tailWord_6616516, baseEnd_6616516] using wordTrace_append hprefix tailTrace_6616516
  have hstable : (prefixWord ++ tailWord_6616516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616516).length < 2 ^ (prefixWord ++ tailWord_6616516).sum := by decide
  have hdescent : baseEnd_6616516 < baseStart_6616516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616526 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_6616526 : Nat := 118140960795 + 6616526 * 2 ^ 59
def prefixEnd_6616526 : Nat := 4983230072969 + 3 ^ 40 * 6616526 * 2
def baseEnd_6616526 : Nat := 3397458100970485045296157

theorem tailTrace_6616526 : CollatzResearch.WordTrace tailWord_6616526 prefixEnd_6616526 3397458100970485045296157 := by
  unfold tailWord_6616526
  simp only [CollatzResearch.WordTrace]
  refine ⟨30165566103432973690125679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160883019218309193014003621 30165566103432973690125679)
  ·
    refine ⟨45248349155149460535188519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30165566103432973690125679 45248349155149460535188519)
    ·
      refine ⟨67872523732724190802782779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45248349155149460535188519 67872523732724190802782779)
      ·
        refine ⟨101808785599086286204174169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67872523732724190802782779 101808785599086286204174169)
        ·
          refine ⟨76356589199314714653130627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101808785599086286204174169 76356589199314714653130627)
          ·
            refine ⟨114534883798972071979695941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76356589199314714653130627 114534883798972071979695941)
            ·
              refine ⟨21475290712307263496192989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114534883798972071979695941 21475290712307263496192989)
              ·
                refine ⟨8053234017115223811072371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21475290712307263496192989 8053234017115223811072371)
                ·
                  refine ⟨12079851025672835716608557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8053234017115223811072371 12079851025672835716608557)
                  ·
                    refine ⟨4529944134627313393728209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12079851025672835716608557 4529944134627313393728209)
                    ·
                      refine ⟨3397458100970485045296157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529944134627313393728209 3397458100970485045296157)
                      ·
                        rfl

theorem cell23_6616526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_6616526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616526 prefixEnd_6616526 := by exact prefixLift 6616526
  have htrace : WordTrace (prefixWord ++ tailWord_6616526) baseStart_6616526 baseEnd_6616526 := by
    simpa [prefixWord, tailWord_6616526, baseEnd_6616526] using wordTrace_append hprefix tailTrace_6616526
  have hstable : (prefixWord ++ tailWord_6616526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616526).length < 2 ^ (prefixWord ++ tailWord_6616526).sum := by decide
  have hdescent : baseEnd_6616526 < baseStart_6616526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616552 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6616552 : Nat := 118140960795 + 6616552 * 2 ^ 59
def prefixEnd_6616552 : Nat := 4983230072969 + 3 ^ 40 * 6616552 * 2
def baseEnd_6616552 : Nat := 3397471451467501943571037

theorem tailTrace_6616552 : CollatzResearch.WordTrace tailWord_6616552 prefixEnd_6616552 3397471451467501943571037 := by
  unfold tailWord_6616552
  simp only [CollatzResearch.WordTrace]
  refine ⟨120662738562684797980725955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160883651416913063974301273 120662738562684797980725955)
  ·
    refine ⟨180994107844027196971088933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120662738562684797980725955 180994107844027196971088933)
    ·
      refine ⟨33936395220755099432079175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180994107844027196971088933 33936395220755099432079175)
      ·
        refine ⟨50904592831132649148118763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33936395220755099432079175 50904592831132649148118763)
        ·
          refine ⟨76356889246698973722178145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50904592831132649148118763 76356889246698973722178145)
          ·
            refine ⟨57267666935024230291633609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76356889246698973722178145 57267666935024230291633609)
            ·
              refine ⟨42950750201268172718725207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57267666935024230291633609 42950750201268172718725207)
              ·
                refine ⟨64426125301902259078087811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42950750201268172718725207 64426125301902259078087811)
                ·
                  refine ⟨96639187952853388617131717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64426125301902259078087811 96639187952853388617131717)
                  ·
                    refine ⟨18119847741160010365712197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96639187952853388617131717 18119847741160010365712197)
                    ·
                      refine ⟨3397471451467501943571037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18119847741160010365712197 3397471451467501943571037)
                      ·
                        rfl

theorem cell23_6616552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6616552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616552 prefixEnd_6616552 := by exact prefixLift 6616552
  have htrace : WordTrace (prefixWord ++ tailWord_6616552) baseStart_6616552 baseEnd_6616552 := by
    simpa [prefixWord, tailWord_6616552, baseEnd_6616552] using wordTrace_append hprefix tailTrace_6616552
  have hstable : (prefixWord ++ tailWord_6616552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616552).length < 2 ^ (prefixWord ++ tailWord_6616552).sum := by decide
  have hdescent : baseEnd_6616552 < baseStart_6616552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616590 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_6616590 : Nat := 118140960795 + 6616590 * 2 ^ 59
def prefixEnd_6616590 : Nat := 4983230072969 + 3 ^ 40 * 6616590 * 2
def baseEnd_6616590 : Nat := 3397490963732372794895863

theorem tailTrace_6616590 : CollatzResearch.WordTrace tailWord_6616590 prefixEnd_6616590 3397490963732372794895863 := by
  unfold tailWord_6616590
  simp only [CollatzResearch.WordTrace]
  refine ⟨30165857887403991056416903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160884575399487952300890149 30165857887403991056416903)
  ·
    refine ⟨45248786831105986584625355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30165857887403991056416903 45248786831105986584625355)
    ·
      refine ⟨67873180246658979876938033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45248786831105986584625355 67873180246658979876938033)
      ·
        refine ⟨50904885184994234907703525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67873180246658979876938033 50904885184994234907703525)
        ·
          refine ⟨9544665972186419045194411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50904885184994234907703525 9544665972186419045194411)
          ·
            refine ⟨14316998958279628567791617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9544665972186419045194411 14316998958279628567791617)
            ·
              refine ⟨10737749218709721425843713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14316998958279628567791617 10737749218709721425843713)
              ·
                refine ⟨8053311914032291069382785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10737749218709721425843713 8053311914032291069382785)
                ·
                  refine ⟨6039983935524218302037089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8053311914032291069382785 6039983935524218302037089)
                  ·
                    refine ⟨4529987951643163726527817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6039983935524218302037089 4529987951643163726527817)
                    ·
                      refine ⟨3397490963732372794895863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529987951643163726527817 3397490963732372794895863)
                      ·
                        rfl

theorem cell23_6616590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_6616590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616590 prefixEnd_6616590 := by exact prefixLift 6616590
  have htrace : WordTrace (prefixWord ++ tailWord_6616590) baseStart_6616590 baseEnd_6616590 := by
    simpa [prefixWord, tailWord_6616590, baseEnd_6616590] using wordTrace_append hprefix tailTrace_6616590
  have hstable : (prefixWord ++ tailWord_6616590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616590).length < 2 ^ (prefixWord ++ tailWord_6616590).sum := by decide
  have hdescent : baseEnd_6616590 < baseStart_6616590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616629 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_6616629 : Nat := 118140960795 + 6616629 * 2 ^ 59
def prefixEnd_6616629 : Nat := 4983230072969 + 3 ^ 40 * 6616629 * 2
def baseEnd_6616629 : Nat := 3397510989477898142308183

theorem tailTrace_6616629 : CollatzResearch.WordTrace tailWord_6616629 prefixEnd_6616629 3397510989477898142308183 := by
  unfold tailWord_6616629
  simp only [CollatzResearch.WordTrace]
  refine ⟨241328285546090638112004941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160885523697393758741336627 241328285546090638112004941)
  ·
    refine ⟨90498107079783989292001853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241328285546090638112004941 90498107079783989292001853)
    ·
      refine ⟨33936790154918995984500695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90498107079783989292001853 33936790154918995984500695)
      ·
        refine ⟨50905185232378493976751043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33936790154918995984500695 50905185232378493976751043)
        ·
          refine ⟨76357777848567740965126565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50905185232378493976751043 76357777848567740965126565)
          ·
            refine ⟨14317083346606451430961231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76357777848567740965126565 14317083346606451430961231)
            ·
              refine ⟨21475625019909677146441847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14317083346606451430961231 21475625019909677146441847)
              ·
                refine ⟨32213437529864515719662771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21475625019909677146441847 32213437529864515719662771)
                ·
                  refine ⟨48320156294796773579494157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32213437529864515719662771 48320156294796773579494157)
                  ·
                    refine ⟨18120058610548790092310309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48320156294796773579494157 18120058610548790092310309)
                    ·
                      refine ⟨3397510989477898142308183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18120058610548790092310309 3397510989477898142308183)
                      ·
                        rfl

theorem cell23_6616629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_6616629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616629 prefixEnd_6616629 := by exact prefixLift 6616629
  have htrace : WordTrace (prefixWord ++ tailWord_6616629) baseStart_6616629 baseEnd_6616629 := by
    simpa [prefixWord, tailWord_6616629, baseEnd_6616629] using wordTrace_append hprefix tailTrace_6616629
  have hstable : (prefixWord ++ tailWord_6616629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616629).length < 2 ^ (prefixWord ++ tailWord_6616629).sum := by decide
  have hdescent : baseEnd_6616629 < baseStart_6616629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616649 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 3]
def baseStart_6616649 : Nat := 118140960795 + 6616649 * 2 ^ 59
def prefixEnd_6616649 : Nat := 4983230072969 + 3 ^ 40 * 6616649 * 2
def baseEnd_6616649 : Nat := 3397521259090988064058091

theorem tailTrace_6616649 : CollatzResearch.WordTrace tailWord_6616649 prefixEnd_6616649 3397521259090988064058091 := by
  unfold tailWord_6616649
  simp only [CollatzResearch.WordTrace]
  refine ⟨241329015006018181527733001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160886010004012121018488667 241329015006018181527733001)
  ·
    refine ⟨180996761254513636145799751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241329015006018181527733001 180996761254513636145799751)
    ·
      refine ⟨271495141881770454218699627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180996761254513636145799751 271495141881770454218699627)
      ·
        refine ⟨407242712822655681328049441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271495141881770454218699627 407242712822655681328049441)
        ·
          refine ⟨305432034616991760996037081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407242712822655681328049441 305432034616991760996037081)
          ·
            refine ⟨229074025962743820747027811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305432034616991760996037081 229074025962743820747027811)
            ·
              refine ⟨343611038944115731120541717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229074025962743820747027811 343611038944115731120541717)
              ·
                refine ⟨16106767450505424896275393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343611038944115731120541717 16106767450505424896275393)
                ·
                  refine ⟨12080075587879068672206545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16106767450505424896275393 12080075587879068672206545)
                  ·
                    refine ⟨9060056690909301504154909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12080075587879068672206545 9060056690909301504154909)
                    ·
                      refine ⟨3397521259090988064058091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9060056690909301504154909 3397521259090988064058091)
                      ·
                        rfl

theorem cell23_6616649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 3].length) (baseStart_6616649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616649 prefixEnd_6616649 := by exact prefixLift 6616649
  have htrace : WordTrace (prefixWord ++ tailWord_6616649) baseStart_6616649 baseEnd_6616649 := by
    simpa [prefixWord, tailWord_6616649, baseEnd_6616649] using wordTrace_append hprefix tailTrace_6616649
  have hstable : (prefixWord ++ tailWord_6616649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616649).length < 2 ^ (prefixWord ++ tailWord_6616649).sum := by decide
  have hdescent : baseEnd_6616649 < baseStart_6616649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616656 : List Nat := [2, 1, 1, 1, 1, 3, 3, 6, 1, 4]
def baseStart_6616656 : Nat := 118140960795 + 6616656 * 2 ^ 59
def prefixEnd_6616656 : Nat := 4983230072969 + 3 ^ 40 * 6616656 * 2
def baseEnd_6616656 : Nat := 1132508284485189845556853

theorem tailTrace_6616656 : CollatzResearch.WordTrace tailWord_6616656 prefixEnd_6616656 1132508284485189845556853 := by
  unfold tailWord_6616656
  simp only [CollatzResearch.WordTrace]
  refine ⟨120664635158496410861618911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160886180211328547815491881 120664635158496410861618911)
  ·
    refine ⟨180996952737744616292428367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120664635158496410861618911 180996952737744616292428367)
    ·
      refine ⟨271495429106616924438642551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180996952737744616292428367 271495429106616924438642551)
      ·
        refine ⟨407243143659925386657963827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271495429106616924438642551 407243143659925386657963827)
        ·
          refine ⟨610864715489888079986945741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407243143659925386657963827 610864715489888079986945741)
          ·
            refine ⟨229074268308708029995104653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 610864715489888079986945741 229074268308708029995104653)
            ·
              refine ⟨85902850615765511248164245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229074268308708029995104653 85902850615765511248164245)
              ·
                refine ⟨4026696122614008339757699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85902850615765511248164245 4026696122614008339757699)
                ·
                  refine ⟨6040044183921012509636549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026696122614008339757699 6040044183921012509636549)
                  ·
                    refine ⟨1132508284485189845556853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040044183921012509636549 1132508284485189845556853)
                    ·
                      rfl

theorem cell23_6616656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 4].length) (baseStart_6616656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616656 prefixEnd_6616656 := by exact prefixLift 6616656
  have htrace : WordTrace (prefixWord ++ tailWord_6616656) baseStart_6616656 baseEnd_6616656 := by
    simpa [prefixWord, tailWord_6616656, baseEnd_6616656] using wordTrace_append hprefix tailTrace_6616656
  have hstable : (prefixWord ++ tailWord_6616656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616656).length < 2 ^ (prefixWord ++ tailWord_6616656).sum := by decide
  have hdescent : baseEnd_6616656 < baseStart_6616656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616672 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_6616672 : Nat := 118140960795 + 6616672 * 2 ^ 59
def prefixEnd_6616672 : Nat := 4983230072969 + 3 ^ 40 * 6616672 * 2
def baseEnd_6616672 : Nat := 3397533069146041474070485

theorem tailTrace_6616672 : CollatzResearch.WordTrace tailWord_6616672 prefixEnd_6616672 3397533069146041474070485 := by
  unfold tailWord_6616672
  simp only [CollatzResearch.WordTrace]
  refine ⟨120664926942467428227910135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160886569256623237637213513 120664926942467428227910135)
  ·
    refine ⟨180997390413701142341865203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120664926942467428227910135 180997390413701142341865203)
    ·
      refine ⟨271496085620551713512797805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180997390413701142341865203 271496085620551713512797805)
      ·
        refine ⟨101811032107706892567299177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271496085620551713512797805 101811032107706892567299177)
        ·
          refine ⟨76358274080780169425474383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101811032107706892567299177 76358274080780169425474383)
          ·
            refine ⟨114537411121170254138211575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76358274080780169425474383 114537411121170254138211575)
            ·
              refine ⟨171806116681755381207317363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114537411121170254138211575 171806116681755381207317363)
              ·
                refine ⟨257709175022633071810976045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171806116681755381207317363 257709175022633071810976045)
                ·
                  refine ⟨96640940633487401929116017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257709175022633071810976045 96640940633487401929116017)
                  ·
                    refine ⟨72480705475115551446837013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96640940633487401929116017 72480705475115551446837013)
                    ·
                      refine ⟨3397533069146041474070485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72480705475115551446837013 3397533069146041474070485)
                      ·
                        rfl

theorem cell23_6616672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_6616672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616672 prefixEnd_6616672 := by exact prefixLift 6616672
  have htrace : WordTrace (prefixWord ++ tailWord_6616672) baseStart_6616672 baseEnd_6616672 := by
    simpa [prefixWord, tailWord_6616672, baseEnd_6616672] using wordTrace_append hprefix tailTrace_6616672
  have hstable : (prefixWord ++ tailWord_6616672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616672).length < 2 ^ (prefixWord ++ tailWord_6616672).sum := by decide
  have hdescent : baseEnd_6616672 < baseStart_6616672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616690 : List Nat := [3, 2, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_6616690 : Nat := 118140960795 + 6616690 * 2 ^ 59
def prefixEnd_6616690 : Nat := 4983230072969 + 3 ^ 40 * 6616690 * 2
def baseEnd_6616690 : Nat := 1132514103932607467881801

theorem tailTrace_6616690 : CollatzResearch.WordTrace tailWord_6616690 prefixEnd_6616690 1132514103932607467881801 := by
  unfold tailWord_6616690
  simp only [CollatzResearch.WordTrace]
  refine ⟨60332627599717411382493881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160887006932579763686650349 60332627599717411382493881)
  ·
    refine ⟨45249470699788058536870411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60332627599717411382493881 45249470699788058536870411)
    ·
      refine ⟨67874206049682087805305617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45249470699788058536870411 67874206049682087805305617)
      ·
        refine ⟨50905654537261565853979213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67874206049682087805305617 50905654537261565853979213)
        ·
          refine ⟨19089620451473087195242205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50905654537261565853979213 19089620451473087195242205)
          ·
            refine ⟨7158607669302407698215827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19089620451473087195242205 7158607669302407698215827)
            ·
              refine ⟨10737911503953611547323741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158607669302407698215827 10737911503953611547323741)
              ·
                refine ⟨4026716813982604330246403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10737911503953611547323741 4026716813982604330246403)
                ·
                  refine ⟨6040075220973906495369605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026716813982604330246403 6040075220973906495369605)
                  ·
                    refine ⟨1132514103932607467881801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040075220973906495369605 1132514103932607467881801)
                    ·
                      rfl

theorem cell23_6616690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_6616690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616690 prefixEnd_6616690 := by exact prefixLift 6616690
  have htrace : WordTrace (prefixWord ++ tailWord_6616690) baseStart_6616690 baseEnd_6616690 := by
    simpa [prefixWord, tailWord_6616690, baseEnd_6616690] using wordTrace_append hprefix tailTrace_6616690
  have hstable : (prefixWord ++ tailWord_6616690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616690).length < 2 ^ (prefixWord ++ tailWord_6616690).sum := by decide
  have hdescent : baseEnd_6616690 < baseStart_6616690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616699 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 1, 5]
def baseStart_6616699 : Nat := 118140960795 + 6616699 * 2 ^ 59
def prefixEnd_6616699 : Nat := 4983230072969 + 3 ^ 40 * 6616699 * 2
def baseEnd_6616699 : Nat := 1132515644374570956144287

theorem tailTrace_6616699 : CollatzResearch.WordTrace tailWord_6616699 prefixEnd_6616699 1132515644374570956144287 := by
  unfold tailWord_6616699
  simp only [CollatzResearch.WordTrace]
  refine ⟨241330838655837040067053151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160887225770558026711368767 241330838655837040067053151)
  ·
    refine ⟨361996257983755560100579727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241330838655837040067053151 361996257983755560100579727)
    ·
      refine ⟨542994386975633340150869591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361996257983755560100579727 542994386975633340150869591)
      ·
        refine ⟨814491580463450010226304387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542994386975633340150869591 814491580463450010226304387)
        ·
          refine ⟨1221737370695175015339456581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814491580463450010226304387 1221737370695175015339456581)
          ·
            refine ⟨229075757005345315376148109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1221737370695175015339456581 229075757005345315376148109)
            ·
              refine ⟨85903408877004493266055541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229075757005345315376148109 85903408877004493266055541)
              ·
                refine ⟨8053444582219171243692707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85903408877004493266055541 8053444582219171243692707)
                ·
                  refine ⟨12080166873328756865539061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8053444582219171243692707 12080166873328756865539061)
                  ·
                    refine ⟨1132515644374570956144287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12080166873328756865539061 1132515644374570956144287)
                    ·
                      rfl

theorem cell23_6616699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 5].length) (baseStart_6616699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616699 prefixEnd_6616699 := by exact prefixLift 6616699
  have htrace : WordTrace (prefixWord ++ tailWord_6616699) baseStart_6616699 baseEnd_6616699 := by
    simpa [prefixWord, tailWord_6616699, baseEnd_6616699] using wordTrace_append hprefix tailTrace_6616699
  have hstable : (prefixWord ++ tailWord_6616699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616699).length < 2 ^ (prefixWord ++ tailWord_6616699).sum := by decide
  have hdescent : baseEnd_6616699 < baseStart_6616699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616713 : List Nat := [1, 2, 1, 1, 4, 1, 2, 6, 1, 1, 3]
def baseStart_6616713 : Nat := 118140960795 + 6616713 * 2 ^ 59
def prefixEnd_6616713 : Nat := 4983230072969 + 3 ^ 40 * 6616713 * 2
def baseEnd_6616713 : Nat := 3397554121852875813657797

theorem tailTrace_6616713 : CollatzResearch.WordTrace tailWord_6616713 prefixEnd_6616713 3397554121852875813657797 := by
  unfold tailWord_6616713
  simp only [CollatzResearch.WordTrace]
  refine ⟨241331349277786320458062793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160887566185190880305375195 241331349277786320458062793)
  ·
    refine ⟨180998511958339740343547095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241331349277786320458062793 180998511958339740343547095)
    ·
      refine ⟨271497767937509610515320643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180998511958339740343547095 271497767937509610515320643)
      ·
        refine ⟨407246651906264415772980965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271497767937509610515320643 407246651906264415772980965)
        ·
          refine ⟨76358747232424577957433931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407246651906264415772980965 76358747232424577957433931)
          ·
            refine ⟨114538120848636866936150897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76358747232424577957433931 114538120848636866936150897)
            ·
              refine ⟨85903590636477650202113173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114538120848636866936150897 85903590636477650202113173)
              ·
                refine ⟨4026730811084889853224055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85903590636477650202113173 4026730811084889853224055)
                ·
                  refine ⟨6040096216627334779836083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026730811084889853224055 6040096216627334779836083)
                  ·
                    refine ⟨9060144324941002169754125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6040096216627334779836083 9060144324941002169754125)
                    ·
                      refine ⟨3397554121852875813657797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9060144324941002169754125 3397554121852875813657797)
                      ·
                        rfl

theorem cell23_6616713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 1, 3].length) (baseStart_6616713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616713 prefixEnd_6616713 := by exact prefixLift 6616713
  have htrace : WordTrace (prefixWord ++ tailWord_6616713) baseStart_6616713 baseEnd_6616713 := by
    simpa [prefixWord, tailWord_6616713, baseEnd_6616713] using wordTrace_append hprefix tailTrace_6616713
  have hstable : (prefixWord ++ tailWord_6616713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616713).length < 2 ^ (prefixWord ++ tailWord_6616713).sum := by decide
  have hdescent : baseEnd_6616713 < baseStart_6616713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616729 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 6, 4]
def baseStart_6616729 : Nat := 118140960795 + 6616729 * 2 ^ 59
def prefixEnd_6616729 : Nat := 4983230072969 + 3 ^ 40 * 6616729 * 2
def baseEnd_6616729 : Nat := 1132520779181115917019241

theorem tailTrace_6616729 : CollatzResearch.WordTrace tailWord_6616729 prefixEnd_6616729 1132520779181115917019241 := by
  unfold tailWord_6616729
  simp only [CollatzResearch.WordTrace]
  refine ⟨241331932845728355190645241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160887955230485570127096827 241331932845728355190645241)
  ·
    refine ⟨180998949634296266392983931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241331932845728355190645241 180998949634296266392983931)
    ·
      refine ⟨271498424451444399589475897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180998949634296266392983931 271498424451444399589475897)
      ·
        refine ⟨203623818338583299692106923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271498424451444399589475897 203623818338583299692106923)
        ·
          refine ⟨305435727507874949538160385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203623818338583299692106923 305435727507874949538160385)
          ·
            refine ⟨229076795630906212153620289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305435727507874949538160385 229076795630906212153620289)
            ·
              refine ⟨171807596723179659115215217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229076795630906212153620289 171807596723179659115215217)
              ·
                refine ⟨128855697542384744336411413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171807596723179659115215217 128855697542384744336411413)
                ·
                  refine ⟨6040110822299284890769285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128855697542384744336411413 6040110822299284890769285)
                  ·
                    refine ⟨1132520779181115917019241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040110822299284890769285 1132520779181115917019241)
                    ·
                      rfl

theorem cell23_6616729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 4].length) (baseStart_6616729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616729 prefixEnd_6616729 := by exact prefixLift 6616729
  have htrace : WordTrace (prefixWord ++ tailWord_6616729) baseStart_6616729 baseEnd_6616729 := by
    simpa [prefixWord, tailWord_6616729, baseEnd_6616729] using wordTrace_append hprefix tailTrace_6616729
  have hstable : (prefixWord ++ tailWord_6616729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616729).length < 2 ^ (prefixWord ++ tailWord_6616729).sum := by decide
  have hdescent : baseEnd_6616729 < baseStart_6616729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616736 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_6616736 : Nat := 118140960795 + 6616736 * 2 ^ 59
def prefixEnd_6616736 : Nat := 4983230072969 + 3 ^ 40 * 6616736 * 2
def baseEnd_6616736 : Nat := 3397565931907929223670191

theorem tailTrace_6616736 : CollatzResearch.WordTrace tailWord_6616736 prefixEnd_6616736 3397565931907929223670191 := by
  unfold tailWord_6616736
  simp only [CollatzResearch.WordTrace]
  refine ⟨120666094078351497693075031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160888125437801996924100041 120666094078351497693075031)
  ·
    refine ⟨180999141117527246539612547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120666094078351497693075031 180999141117527246539612547)
    ·
      refine ⟨271498711676290869809418821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180999141117527246539612547 271498711676290869809418821)
      ·
        refine ⟨50906008439304538089266029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271498711676290869809418821 50906008439304538089266029)
        ·
          refine ⟨19089753164739201783474761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50906008439304538089266029 19089753164739201783474761)
          ·
            refine ⟨14317314873554401337606071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19089753164739201783474761 14317314873554401337606071)
            ·
              refine ⟨21475972310331602006409107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14317314873554401337606071 21475972310331602006409107)
              ·
                refine ⟨32213958465497403009613661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21475972310331602006409107 32213958465497403009613661)
                ·
                  refine ⟨12080234424561526128605123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32213958465497403009613661 12080234424561526128605123)
                  ·
                    refine ⟨18120351636842289192907685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12080234424561526128605123 18120351636842289192907685)
                    ·
                      refine ⟨3397565931907929223670191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18120351636842289192907685 3397565931907929223670191)
                      ·
                        rfl

theorem cell23_6616736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_6616736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616736 prefixEnd_6616736 := by exact prefixLift 6616736
  have htrace : WordTrace (prefixWord ++ tailWord_6616736) baseStart_6616736 baseEnd_6616736 := by
    simpa [prefixWord, tailWord_6616736, baseEnd_6616736] using wordTrace_append hprefix tailTrace_6616736
  have hstable : (prefixWord ++ tailWord_6616736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616736).length < 2 ^ (prefixWord ++ tailWord_6616736).sum := by decide
  have hdescent : baseEnd_6616736 < baseStart_6616736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616799 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_6616799 : Nat := 118140960795 + 6616799 * 2 ^ 59
def prefixEnd_6616799 : Nat := 4983230072969 + 3 ^ 40 * 6616799 * 2
def baseEnd_6616799 : Nat := 3397598281189162477182401

theorem tailTrace_6616799 : CollatzResearch.WordTrace tailWord_6616799 prefixEnd_6616799 3397598281189162477182401 := by
  unfold tailWord_6616799
  simp only [CollatzResearch.WordTrace]
  refine ⟨241334485955474757145693451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160889657303649838097128967 241334485955474757145693451)
  ·
    refine ⟨362001728933212135718540177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241334485955474757145693451 362001728933212135718540177)
    ·
      refine ⟨271501296699909101788905133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362001728933212135718540177 271501296699909101788905133)
      ·
        refine ⟨101812986262465913170839425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271501296699909101788905133 101812986262465913170839425)
        ·
          refine ⟨76359739696849434878129569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101812986262465913170839425 76359739696849434878129569)
          ·
            refine ⟨57269804772637076158597177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76359739696849434878129569 57269804772637076158597177)
            ·
              refine ⟨42952353579477807118947883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57269804772637076158597177 42952353579477807118947883)
              ·
                refine ⟨64428530369216710678421825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42952353579477807118947883 64428530369216710678421825)
                ·
                  refine ⟨48321397776912533008816369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64428530369216710678421825 48321397776912533008816369)
                  ·
                    refine ⟨36241048332684399756612277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48321397776912533008816369 36241048332684399756612277)
                    ·
                      refine ⟨3397598281189162477182401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36241048332684399756612277 3397598281189162477182401)
                      ·
                        rfl

theorem cell23_6616799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_6616799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616799 prefixEnd_6616799 := by exact prefixLift 6616799
  have htrace : WordTrace (prefixWord ++ tailWord_6616799) baseStart_6616799 baseEnd_6616799 := by
    simpa [prefixWord, tailWord_6616799, baseEnd_6616799] using wordTrace_append hprefix tailTrace_6616799
  have hstable : (prefixWord ++ tailWord_6616799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616799).length < 2 ^ (prefixWord ++ tailWord_6616799).sum := by decide
  have hdescent : baseEnd_6616799 < baseStart_6616799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616819 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 2, 6]
def baseStart_6616819 : Nat := 118140960795 + 6616819 * 2 ^ 59
def prefixEnd_6616819 : Nat := 4983230072969 + 3 ^ 40 * 6616819 * 2
def baseEnd_6616819 : Nat := 1132536183600750799644103

theorem tailTrace_6616819 : CollatzResearch.WordTrace tailWord_6616819 prefixEnd_6616819 1132536183600750799644103 := by
  unfold tailWord_6616819
  simp only [CollatzResearch.WordTrace]
  refine ⟨241335215415402300561421511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160890143610268200374281007 241335215415402300561421511)
  ·
    refine ⟨362002823123103450842132267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241335215415402300561421511 362002823123103450842132267)
    ·
      refine ⟨543004234684655176263198401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362002823123103450842132267 543004234684655176263198401)
      ·
        refine ⟨407253176013491382197398801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543004234684655176263198401 407253176013491382197398801)
        ·
          refine ⟨305439882010118536648049101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407253176013491382197398801 305439882010118536648049101)
          ·
            refine ⟨114539955753794451243018413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305439882010118536648049101 114539955753794451243018413)
            ·
              refine ⟨42952483407672919216131905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114539955753794451243018413 42952483407672919216131905)
              ·
                refine ⟨32214362555754689412098929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42952483407672919216131905 32214362555754689412098929)
                ·
                  refine ⟨24160771916816017059074197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32214362555754689412098929 24160771916816017059074197)
                  ·
                    refine ⟨1132536183600750799644103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24160771916816017059074197 1132536183600750799644103)
                    ·
                      rfl

theorem cell23_6616819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 6].length) (baseStart_6616819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616819 prefixEnd_6616819 := by exact prefixLift 6616819
  have htrace : WordTrace (prefixWord ++ tailWord_6616819) baseStart_6616819 baseEnd_6616819 := by
    simpa [prefixWord, tailWord_6616819, baseEnd_6616819] using wordTrace_append hprefix tailTrace_6616819
  have hstable : (prefixWord ++ tailWord_6616819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616819).length < 2 ^ (prefixWord ++ tailWord_6616819).sum := by decide
  have hdescent : baseEnd_6616819 < baseStart_6616819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616829 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_6616829 : Nat := 118140960795 + 6616829 * 2 ^ 59
def prefixEnd_6616829 : Nat := 4983230072969 + 3 ^ 40 * 6616829 * 2
def baseEnd_6616829 : Nat := 3397613685608797359807263

theorem tailTrace_6616829 : CollatzResearch.WordTrace tailWord_6616829 prefixEnd_6616829 3397613685608797359807263 := by
  unfold tailWord_6616829
  simp only [CollatzResearch.WordTrace]
  refine ⟨241335580145366072269285541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160890386763577381512857027 241335580145366072269285541)
  ·
    refine ⟨45250421277256138550491039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241335580145366072269285541 45250421277256138550491039)
    ·
      refine ⟨67875631915884207825736559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45250421277256138550491039 67875631915884207825736559)
      ·
        refine ⟨101813447873826311738604839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67875631915884207825736559 101813447873826311738604839)
        ·
          refine ⟨152720171810739467607907259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101813447873826311738604839 152720171810739467607907259)
          ·
            refine ⟨229080257716109201411860889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152720171810739467607907259 229080257716109201411860889)
            ·
              refine ⟨171810193287081901058895667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229080257716109201411860889 171810193287081901058895667)
              ·
                refine ⟨257715289930622851588343501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171810193287081901058895667 257715289930622851588343501)
                ·
                  refine ⟨96643233723983569345628813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257715289930622851588343501 96643233723983569345628813)
                  ·
                    refine ⟨36241212646493838504610805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96643233723983569345628813 36241212646493838504610805)
                    ·
                      refine ⟨3397613685608797359807263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36241212646493838504610805 3397613685608797359807263)
                      ·
                        rfl

theorem cell23_6616829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_6616829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616829 prefixEnd_6616829 := by exact prefixLift 6616829
  have htrace : WordTrace (prefixWord ++ tailWord_6616829) baseStart_6616829 baseEnd_6616829 := by
    simpa [prefixWord, tailWord_6616829, baseEnd_6616829] using wordTrace_append hprefix tailTrace_6616829
  have hstable : (prefixWord ++ tailWord_6616829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616829).length < 2 ^ (prefixWord ++ tailWord_6616829).sum := by decide
  have hdescent : baseEnd_6616829 < baseStart_6616829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616836 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_6616836 : Nat := 118140960795 + 6616836 * 2 ^ 59
def prefixEnd_6616836 : Nat := 4983230072969 + 3 ^ 40 * 6616836 * 2
def baseEnd_6616836 : Nat := 1132539093324459610806577

theorem tailTrace_6616836 : CollatzResearch.WordTrace tailWord_6616836 prefixEnd_6616836 1132539093324459610806577 := by
  unfold tailWord_6616836
  simp only [CollatzResearch.WordTrace]
  refine ⟨120667917728170356232395181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160890556970893808309860241 120667917728170356232395181)
  ·
    refine ⟨45250469148063883587148193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120667917728170356232395181 45250469148063883587148193)
    ·
      refine ⟨33937851861047912690361145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45250469148063883587148193 33937851861047912690361145)
      ·
        refine ⟨25453388895785934517770859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33937851861047912690361145 25453388895785934517770859)
        ·
          refine ⟨38180083343678901776656289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25453388895785934517770859 38180083343678901776656289)
          ·
            refine ⟨28635062507759176332492217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38180083343678901776656289 28635062507759176332492217)
            ·
              refine ⟨21476296880819382249369163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28635062507759176332492217 21476296880819382249369163)
              ·
                refine ⟨32214445321229073374053745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21476296880819382249369163 32214445321229073374053745)
                ·
                  refine ⟨24160833990921805030540309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32214445321229073374053745 24160833990921805030540309)
                  ·
                    refine ⟨1132539093324459610806577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24160833990921805030540309 1132539093324459610806577)
                    ·
                      rfl

theorem cell23_6616836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_6616836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616836 prefixEnd_6616836 := by exact prefixLift 6616836
  have htrace : WordTrace (prefixWord ++ tailWord_6616836) baseStart_6616836 baseEnd_6616836 := by
    simpa [prefixWord, tailWord_6616836, baseEnd_6616836] using wordTrace_append hprefix tailTrace_6616836
  have hstable : (prefixWord ++ tailWord_6616836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616836).length < 2 ^ (prefixWord ++ tailWord_6616836).sum := by decide
  have hdescent : baseEnd_6616836 < baseStart_6616836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616843 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 1, 4, 2]
def baseStart_6616843 : Nat := 118140960795 + 6616843 * 2 ^ 59
def prefixEnd_6616843 : Nat := 4983230072969 + 3 ^ 40 * 6616843 * 2
def baseEnd_6616843 : Nat := 3397620874337960305032199

theorem tailTrace_6616843 : CollatzResearch.WordTrace tailWord_6616843 prefixEnd_6616843 3397620874337960305032199 := by
  unfold tailWord_6616843
  simp only [CollatzResearch.WordTrace]
  refine ⟨241336090767315352660295183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160890727178210235106863455 241336090767315352660295183)
  ·
    refine ⟨362004136150973028990442775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241336090767315352660295183 362004136150973028990442775)
    ·
      refine ⟨543006204226459543485664163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362004136150973028990442775 543006204226459543485664163)
      ·
        refine ⟨814509306339689315228496245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543006204226459543485664163 814509306339689315228496245)
        ·
          refine ⟨76360247469345873302671523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 814509306339689315228496245 76360247469345873302671523)
          ·
            refine ⟨114540371204018809954007285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76360247469345873302671523 114540371204018809954007285)
            ·
              refine ⟨10738159800376763433188183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114540371204018809954007285 10738159800376763433188183)
              ·
                refine ⟨16107239700565145149782275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738159800376763433188183 16107239700565145149782275)
                ·
                  refine ⟨24160859550847717724673413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16107239700565145149782275 24160859550847717724673413)
                  ·
                    refine ⟨4530161165783947073376265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24160859550847717724673413 4530161165783947073376265)
                    ·
                      refine ⟨3397620874337960305032199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530161165783947073376265 3397620874337960305032199)
                      ·
                        rfl

theorem cell23_6616843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 4, 2].length) (baseStart_6616843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616843 prefixEnd_6616843 := by exact prefixLift 6616843
  have htrace : WordTrace (prefixWord ++ tailWord_6616843) baseStart_6616843 baseEnd_6616843 := by
    simpa [prefixWord, tailWord_6616843, baseEnd_6616843] using wordTrace_append hprefix tailTrace_6616843
  have hstable : (prefixWord ++ tailWord_6616843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616843).length < 2 ^ (prefixWord ++ tailWord_6616843).sum := by decide
  have hdescent : baseEnd_6616843 < baseStart_6616843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616846 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_6616846 : Nat := 118140960795 + 6616846 * 2 ^ 59
def prefixEnd_6616846 : Nat := 4983230072969 + 3 ^ 40 * 6616846 * 2
def baseEnd_6616846 : Nat := 3397622414779923793294685

theorem tailTrace_6616846 : CollatzResearch.WordTrace tailWord_6616846 prefixEnd_6616846 3397622414779923793294685 := by
  unfold tailWord_6616846
  simp only [CollatzResearch.WordTrace]
  refine ⟨30167025023288060521581799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160890800124202989448436261 30167025023288060521581799)
  ·
    refine ⟨45250537534932090782372699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30167025023288060521581799 45250537534932090782372699)
    ·
      refine ⟨67875806302398136173559049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45250537534932090782372699 67875806302398136173559049)
      ·
        refine ⟨50906854726798602130169287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67875806302398136173559049 50906854726798602130169287)
        ·
          refine ⟨76360282090197903195253931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50906854726798602130169287 76360282090197903195253931)
          ·
            refine ⟨114540423135296854792880897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76360282090197903195253931 114540423135296854792880897)
            ·
              refine ⟨85905317351472641094660673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114540423135296854792880897 85905317351472641094660673)
              ·
                refine ⟨64428988013604480820995505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85905317351472641094660673 64428988013604480820995505)
                ·
                  refine ⟨48321741010203360615746629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64428988013604480820995505 48321741010203360615746629)
                  ·
                    refine ⟨9060326439413130115452493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48321741010203360615746629 9060326439413130115452493)
                    ·
                      refine ⟨3397622414779923793294685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9060326439413130115452493 3397622414779923793294685)
                      ·
                        rfl

theorem cell23_6616846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_6616846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616846 prefixEnd_6616846 := by exact prefixLift 6616846
  have htrace : WordTrace (prefixWord ++ tailWord_6616846) baseStart_6616846 baseEnd_6616846 := by
    simpa [prefixWord, tailWord_6616846, baseEnd_6616846] using wordTrace_append hprefix tailTrace_6616846
  have hstable : (prefixWord ++ tailWord_6616846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616846).length < 2 ^ (prefixWord ++ tailWord_6616846).sum := by decide
  have hdescent : baseEnd_6616846 < baseStart_6616846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616883 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 7]
def baseStart_6616883 : Nat := 118140960795 + 6616883 * 2 ^ 59
def prefixEnd_6616883 : Nat := 4983230072969 + 3 ^ 40 * 6616883 * 2
def baseEnd_6616883 : Nat := 377515712618237794281335

theorem tailTrace_6616883 : CollatzResearch.WordTrace tailWord_6616883 prefixEnd_6616883 377515712618237794281335 := by
  unfold tailWord_6616883
  simp only [CollatzResearch.WordTrace]
  refine ⟨241337549687170439491751303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160891699791446959661167535 241337549687170439491751303)
  ·
    refine ⟨362006324530755659237626955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241337549687170439491751303 362006324530755659237626955)
    ·
      refine ⟨543009486796133488856440433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362006324530755659237626955 543009486796133488856440433)
      ·
        refine ⟨407257115097100116642330325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543009486796133488856440433 407257115097100116642330325)
        ·
          refine ⟨9545088635088283983804617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 407257115097100116642330325 9545088635088283983804617)
          ·
            refine ⟨7158816476316212987853463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9545088635088283983804617 7158816476316212987853463)
            ·
              refine ⟨10738224714474319481780195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158816476316212987853463 10738224714474319481780195)
              ·
                refine ⟨16107337071711479222670293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738224714474319481780195 16107337071711479222670293)
                ·
                  refine ⟨377515712618237794281335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16107337071711479222670293 377515712618237794281335)
                  ·
                    rfl

theorem cell23_6616883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 7].length) (baseStart_6616883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616883 prefixEnd_6616883 := by exact prefixLift 6616883
  have htrace : WordTrace (prefixWord ++ tailWord_6616883) baseStart_6616883 baseEnd_6616883 := by
    simpa [prefixWord, tailWord_6616883, baseEnd_6616883] using wordTrace_append hprefix tailTrace_6616883
  have hstable : (prefixWord ++ tailWord_6616883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616883).length < 2 ^ (prefixWord ++ tailWord_6616883).sum := by decide
  have hdescent : baseEnd_6616883 < baseStart_6616883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616894 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_6616894 : Nat := 118140960795 + 6616894 * 2 ^ 59
def prefixEnd_6616894 : Nat := 4983230072969 + 3 ^ 40 * 6616894 * 2
def baseEnd_6616894 : Nat := 3397647061851339605494465

theorem tailTrace_6616894 : CollatzResearch.WordTrace tailWord_6616894 prefixEnd_6616894 3397647061851339605494465 := by
  unfold tailWord_6616894
  simp only [CollatzResearch.WordTrace]
  refine ⟨30167243861266323546300217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160891967260087058913601157 30167243861266323546300217)
  ·
    refine ⟨22625432895949742659725163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30167243861266323546300217 22625432895949742659725163)
    ·
      refine ⟨33938149343924613989587745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22625432895949742659725163 33938149343924613989587745)
      ·
        refine ⟨25453612007943460492190809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33938149343924613989587745 25453612007943460492190809)
        ·
          refine ⟨19090209005957595369143107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25453612007943460492190809 19090209005957595369143107)
          ·
            refine ⟨28635313508936393053714661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19090209005957595369143107 28635313508936393053714661)
            ·
              refine ⟨5369121282925573697571499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28635313508936393053714661 5369121282925573697571499)
              ·
                refine ⟨8053681924388360546357249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369121282925573697571499 8053681924388360546357249)
                ·
                  refine ⟨6040261443291270409767937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8053681924388360546357249 6040261443291270409767937)
                  ·
                    refine ⟨4530196082468452807325953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6040261443291270409767937 4530196082468452807325953)
                    ·
                      refine ⟨3397647061851339605494465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530196082468452807325953 3397647061851339605494465)
                      ·
                        rfl

theorem cell23_6616894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_6616894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616894 prefixEnd_6616894 := by exact prefixLift 6616894
  have htrace : WordTrace (prefixWord ++ tailWord_6616894) baseStart_6616894 baseEnd_6616894 := by
    simpa [prefixWord, tailWord_6616894, baseEnd_6616894] using wordTrace_append hprefix tailTrace_6616894
  have hstable : (prefixWord ++ tailWord_6616894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616894).length < 2 ^ (prefixWord ++ tailWord_6616894).sum := by decide
  have hdescent : baseEnd_6616894 < baseStart_6616894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616913 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 2, 5]
def baseStart_6616913 : Nat := 118140960795 + 6616913 * 2 ^ 59
def prefixEnd_6616913 : Nat := 4983230072969 + 3 ^ 40 * 6616913 * 2
def baseEnd_6616913 : Nat := 1132552272661258343718959

theorem tailTrace_6616913 : CollatzResearch.WordTrace tailWord_6616913 prefixEnd_6616913 1132552272661258343718959 := by
  unfold tailWord_6616913
  simp only [CollatzResearch.WordTrace]
  refine ⟨241338643877061754615343393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160892429251374503076895595 241338643877061754615343393)
  ·
    refine ⟨181003982907796315961507545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241338643877061754615343393 181003982907796315961507545)
    ·
      refine ⟨135752987180847236971130659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181003982907796315961507545 135752987180847236971130659)
      ·
        refine ⟨203629480771270855456695989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135752987180847236971130659 203629480771270855456695989)
        ·
          refine ⟨19090263822306642699065249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203629480771270855456695989 19090263822306642699065249)
          ·
            refine ⟨14317697866729982024298937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19090263822306642699065249 14317697866729982024298937)
            ·
              refine ⟨10738273400047486518224203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14317697866729982024298937 10738273400047486518224203)
              ·
                refine ⟨16107410100071229777336305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738273400047486518224203 16107410100071229777336305)
                ·
                  refine ⟨12080557575053422333002229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16107410100071229777336305 12080557575053422333002229)
                  ·
                    refine ⟨1132552272661258343718959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12080557575053422333002229 1132552272661258343718959)
                    ·
                      rfl

theorem cell23_6616913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_6616913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616913 prefixEnd_6616913 := by exact prefixLift 6616913
  have htrace : WordTrace (prefixWord ++ tailWord_6616913) baseStart_6616913 baseEnd_6616913 := by
    simpa [prefixWord, tailWord_6616913, baseEnd_6616913] using wordTrace_append hprefix tailTrace_6616913
  have hstable : (prefixWord ++ tailWord_6616913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616913).length < 2 ^ (prefixWord ++ tailWord_6616913).sum := by decide
  have hdescent : baseEnd_6616913 < baseStart_6616913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616933 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 2, 4, 2]
def baseStart_6616933 : Nat := 118140960795 + 6616933 * 2 ^ 59
def prefixEnd_6616933 : Nat := 4983230072969 + 3 ^ 40 * 6616933 * 2
def baseEnd_6616933 : Nat := 3397667087596864952906785

theorem tailTrace_6616933 : CollatzResearch.WordTrace tailWord_6616933 prefixEnd_6616933 3397667087596864952906785 := by
  unfold tailWord_6616933
  simp only [CollatzResearch.WordTrace]
  refine ⟨241339373336989298031071453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160892915557992865354047635 241339373336989298031071453)
  ·
    refine ⟨90502265001370986761651795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241339373336989298031071453 90502265001370986761651795)
    ·
      refine ⟨135753397502056480142477693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90502265001370986761651795 135753397502056480142477693)
      ·
        refine ⟨50907524063271180053429135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135753397502056480142477693 50907524063271180053429135)
        ·
          refine ⟨76361286094906770080143703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50907524063271180053429135 76361286094906770080143703)
          ·
            refine ⟨114541929142360155120215555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76361286094906770080143703 114541929142360155120215555)
            ·
              refine ⟨171812893713540232680323333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114541929142360155120215555 171812893713540232680323333)
              ·
                refine ⟨32214917571288793627560625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171812893713540232680323333 32214917571288793627560625)
                ·
                  refine ⟨24161188178466595220670469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32214917571288793627560625 24161188178466595220670469)
                  ·
                    refine ⟨4530222783462486603875713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24161188178466595220670469 4530222783462486603875713)
                    ·
                      refine ⟨3397667087596864952906785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530222783462486603875713 3397667087596864952906785)
                      ·
                        rfl

theorem cell23_6616933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_6616933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616933 prefixEnd_6616933 := by exact prefixLift 6616933
  have htrace : WordTrace (prefixWord ++ tailWord_6616933) baseStart_6616933 baseEnd_6616933 := by
    simpa [prefixWord, tailWord_6616933, baseEnd_6616933] using wordTrace_append hprefix tailTrace_6616933
  have hstable : (prefixWord ++ tailWord_6616933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616933).length < 2 ^ (prefixWord ++ tailWord_6616933).sum := by decide
  have hdescent : baseEnd_6616933 < baseStart_6616933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616936 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6616936 : Nat := 118140960795 + 6616936 * 2 ^ 59
def prefixEnd_6616936 : Nat := 4983230072969 + 3 ^ 40 * 6616936 * 2
def baseEnd_6616936 : Nat := 3397668628038828441169271

theorem tailTrace_6616936 : CollatzResearch.WordTrace tailWord_6616936 prefixEnd_6616936 3397668628038828441169271 := by
  unfold tailWord_6616936
  simp only [CollatzResearch.WordTrace]
  refine ⟨120669741377989214771715331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160892988503985619695620441 120669741377989214771715331)
  ·
    refine ⟨181004612066983822157572997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120669741377989214771715331 181004612066983822157572997)
    ·
      refine ⟨33938364762559466654544937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181004612066983822157572997 33938364762559466654544937)
      ·
        refine ⟨25453773571919599990908703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33938364762559466654544937 25453773571919599990908703)
        ·
          refine ⟨38180660357879399986363055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25453773571919599990908703 38180660357879399986363055)
          ·
            refine ⟨57270990536819099979544583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38180660357879399986363055 57270990536819099979544583)
            ·
              refine ⟨85906485805228649969316875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57270990536819099979544583 85906485805228649969316875)
              ·
                refine ⟨128859728707842974953975313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85906485805228649969316875 128859728707842974953975313)
                ·
                  refine ⟨96644796530882231215481485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128859728707842974953975313 96644796530882231215481485)
                  ·
                    refine ⟨36241798699080836705805557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96644796530882231215481485 36241798699080836705805557)
                    ·
                      refine ⟨3397668628038828441169271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36241798699080836705805557 3397668628038828441169271)
                      ·
                        rfl

theorem cell23_6616936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6616936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616936 prefixEnd_6616936 := by exact prefixLift 6616936
  have htrace : WordTrace (prefixWord ++ tailWord_6616936) baseStart_6616936 baseEnd_6616936 := by
    simpa [prefixWord, tailWord_6616936, baseEnd_6616936] using wordTrace_append hprefix tailTrace_6616936
  have hstable : (prefixWord ++ tailWord_6616936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616936).length < 2 ^ (prefixWord ++ tailWord_6616936).sum := by decide
  have hdescent : baseEnd_6616936 < baseStart_6616936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616946 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_6616946 : Nat := 118140960795 + 6616946 * 2 ^ 59
def prefixEnd_6616946 : Nat := 4983230072969 + 3 ^ 40 * 6616946 * 2
def baseEnd_6616946 : Nat := 3397673762845373402044225

theorem tailTrace_6616946 : CollatzResearch.WordTrace tailWord_6616946 prefixEnd_6616946 3397673762845373402044225 := by
  unfold tailWord_6616946
  simp only [CollatzResearch.WordTrace]
  refine ⟨60334961871485550312823673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160893231657294800834196461 60334961871485550312823673)
  ·
    refine ⟨45251221403614162734617755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60334961871485550312823673 45251221403614162734617755)
    ·
      refine ⟨67876832105421244101926633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45251221403614162734617755 67876832105421244101926633)
      ·
        refine ⟨50907624079065933076444975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67876832105421244101926633 50907624079065933076444975)
        ·
          refine ⟨76361436118598899614667463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50907624079065933076444975 76361436118598899614667463)
          ·
            refine ⟨114542154177898349422001195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76361436118598899614667463 114542154177898349422001195)
            ·
              refine ⟨171813231266847524133001793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114542154177898349422001195 171813231266847524133001793)
              ·
                refine ⟨128859923450135643099751345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171813231266847524133001793 128859923450135643099751345)
                ·
                  refine ⟨96644942587601732324813509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128859923450135643099751345 96644942587601732324813509)
                  ·
                    refine ⟨18120926735175324810902533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96644942587601732324813509 18120926735175324810902533)
                    ·
                      refine ⟨3397673762845373402044225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18120926735175324810902533 3397673762845373402044225)
                      ·
                        rfl

theorem cell23_6616946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_6616946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616946 prefixEnd_6616946 := by exact prefixLift 6616946
  have htrace : WordTrace (prefixWord ++ tailWord_6616946) baseStart_6616946 baseEnd_6616946 := by
    simpa [prefixWord, tailWord_6616946, baseEnd_6616946] using wordTrace_append hprefix tailTrace_6616946
  have hstable : (prefixWord ++ tailWord_6616946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616946).length < 2 ^ (prefixWord ++ tailWord_6616946).sum := by decide
  have hdescent : baseEnd_6616946 < baseStart_6616946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616967 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_6616967 : Nat := 118140960795 + 6616967 * 2 ^ 59
def prefixEnd_6616967 : Nat := 4983230072969 + 3 ^ 40 * 6616967 * 2
def baseEnd_6616967 : Nat := 3397684545939117819881629

theorem tailTrace_6616967 : CollatzResearch.WordTrace tailWord_6616967 prefixEnd_6616967 3397684545939117819881629 := by
  unfold tailWord_6616967
  simp only [CollatzResearch.WordTrace]
  refine ⟨241340613418866121837809155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160893742279244081225206103 241340613418866121837809155)
  ·
    refine ⟨362010920128299182756713733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241340613418866121837809155 362010920128299182756713733)
    ·
      refine ⟨67877047524056096766883825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362010920128299182756713733 67877047524056096766883825)
      ·
        refine ⟨50907785643042072575162869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67877047524056096766883825 50907785643042072575162869)
        ·
          refine ⟨4772604904035194303921519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50907785643042072575162869 4772604904035194303921519)
          ·
            refine ⟨7158907356052791455882279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772604904035194303921519 7158907356052791455882279)
            ·
              refine ⟨10738361034079187183823419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158907356052791455882279 10738361034079187183823419)
              ·
                refine ⟨16107541551118780775735129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738361034079187183823419 16107541551118780775735129)
                ·
                  refine ⟨12080656163339085581801347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16107541551118780775735129 12080656163339085581801347)
                  ·
                    refine ⟨18120984245008628372702021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12080656163339085581801347 18120984245008628372702021)
                    ·
                      refine ⟨3397684545939117819881629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18120984245008628372702021 3397684545939117819881629)
                      ·
                        rfl

theorem cell23_6616967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_6616967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616967 prefixEnd_6616967 := by exact prefixLift 6616967
  have htrace : WordTrace (prefixWord ++ tailWord_6616967) baseStart_6616967 baseEnd_6616967 := by
    simpa [prefixWord, tailWord_6616967, baseEnd_6616967] using wordTrace_append hprefix tailTrace_6616967
  have hstable : (prefixWord ++ tailWord_6616967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616967).length < 2 ^ (prefixWord ++ tailWord_6616967).sum := by decide
  have hdescent : baseEnd_6616967 < baseStart_6616967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6616970 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_6616970 : Nat := 118140960795 + 6616970 * 2 ^ 59
def prefixEnd_6616970 : Nat := 4983230072969 + 3 ^ 40 * 6616970 * 2
def baseEnd_6616970 : Nat := 3397686086381081308144115

theorem tailTrace_6616970 : CollatzResearch.WordTrace tailWord_6616970 prefixEnd_6616970 3397686086381081308144115 := by
  unfold tailWord_6616970
  simp only [CollatzResearch.WordTrace]
  refine ⟨60335180709463813337542091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160893815225236835566778909 60335180709463813337542091)
  ·
    refine ⟨90502771064195720006313137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60335180709463813337542091 90502771064195720006313137)
    ·
      refine ⟨67877078298146790004734853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90502771064195720006313137 67877078298146790004734853)
      ·
        refine ⟨12726952180902523125887785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67877078298146790004734853 12726952180902523125887785)
        ·
          refine ⟨9545214135676892344415839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12726952180902523125887785 9545214135676892344415839)
          ·
            refine ⟨14317821203515338516623759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9545214135676892344415839 14317821203515338516623759)
            ·
              refine ⟨21476731805273007774935639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14317821203515338516623759 21476731805273007774935639)
              ·
                refine ⟨32215097707909511662403459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21476731805273007774935639 32215097707909511662403459)
                ·
                  refine ⟨48322646561864267493605189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32215097707909511662403459 48322646561864267493605189)
                  ·
                    refine ⟨9060496230349550155050973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48322646561864267493605189 9060496230349550155050973)
                    ·
                      refine ⟨3397686086381081308144115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9060496230349550155050973 3397686086381081308144115)
                      ·
                        rfl

theorem cell23_6616970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_6616970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6616970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6616970 prefixEnd_6616970 := by exact prefixLift 6616970
  have htrace : WordTrace (prefixWord ++ tailWord_6616970) baseStart_6616970 baseEnd_6616970 := by
    simpa [prefixWord, tailWord_6616970, baseEnd_6616970] using wordTrace_append hprefix tailTrace_6616970
  have hstable : (prefixWord ++ tailWord_6616970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6616970).length < 2 ^ (prefixWord ++ tailWord_6616970).sum := by decide
  have hdescent : baseEnd_6616970 < baseStart_6616970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6616970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617023 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 2, 6, 2]
def baseStart_6617023 : Nat := 118140960795 + 6617023 * 2 ^ 59
def prefixEnd_6617023 : Nat := 4983230072969 + 3 ^ 40 * 6617023 * 2
def baseEnd_6617023 : Nat := 3397713300855769600781371

theorem tailTrace_6617023 : CollatzResearch.WordTrace tailWord_6617023 prefixEnd_6617023 3397713300855769600781371 := by
  unfold tailWord_6617023
  simp only [CollatzResearch.WordTrace]
  refine ⟨241342655906663243401847723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160895103937775495601231815 241342655906663243401847723)
  ·
    refine ⟨362013983859994865102771585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241342655906663243401847723 362013983859994865102771585)
    ·
      refine ⟨271510487894996148827078689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362013983859994865102771585 271510487894996148827078689)
      ·
        refine ⟨203632865921247111620309017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271510487894996148827078689 203632865921247111620309017)
        ·
          refine ⟨152724649440935333715231763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203632865921247111620309017 152724649440935333715231763)
          ·
            refine ⟨229086974161403000572847645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152724649440935333715231763 229086974161403000572847645)
            ·
              refine ⟨85907615310526125214817867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229086974161403000572847645 85907615310526125214817867)
              ·
                refine ⟨128861422965789187822226801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85907615310526125214817867 128861422965789187822226801)
                ·
                  refine ⟨96646067224341890866670101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128861422965789187822226801 96646067224341890866670101)
                  ·
                    refine ⟨4530284401141026134375161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96646067224341890866670101 4530284401141026134375161)
                    ·
                      refine ⟨3397713300855769600781371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530284401141026134375161 3397713300855769600781371)
                      ·
                        rfl

theorem cell23_6617023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_6617023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617023 prefixEnd_6617023 := by exact prefixLift 6617023
  have htrace : WordTrace (prefixWord ++ tailWord_6617023) baseStart_6617023 baseEnd_6617023 := by
    simpa [prefixWord, tailWord_6617023, baseEnd_6617023] using wordTrace_append hprefix tailTrace_6617023
  have hstable : (prefixWord ++ tailWord_6617023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617023).length < 2 ^ (prefixWord ++ tailWord_6617023).sum := by decide
  have hdescent : baseEnd_6617023 < baseStart_6617023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617040 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 5, 2, 2]
def baseStart_6617040 : Nat := 118140960795 + 6617040 * 2 ^ 59
def prefixEnd_6617040 : Nat := 4983230072969 + 3 ^ 40 * 6617040 * 2
def baseEnd_6617040 : Nat := 3397722030026896034268793

theorem tailTrace_6617040 : CollatzResearch.WordTrace tailWord_6617040 prefixEnd_6617040 3397722030026896034268793 := by
  unfold tailWord_6617040
  simp only [CollatzResearch.WordTrace]
  refine ⟨120671637973800827652608287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160895517298401103536811049 120671637973800827652608287)
  ·
    refine ⟨181007456960701241478912431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120671637973800827652608287 181007456960701241478912431)
    ·
      refine ⟨271511185441051862218368647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181007456960701241478912431 271511185441051862218368647)
      ·
        refine ⟨407266778161577793327552971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271511185441051862218368647 407266778161577793327552971)
        ·
          refine ⟨610900167242366689991329457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407266778161577793327552971 610900167242366689991329457)
          ·
            refine ⟨458175125431775017493497093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610900167242366689991329457 458175125431775017493497093)
            ·
              refine ⟨85907836018457815780030705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 458175125431775017493497093 85907836018457815780030705)
              ·
                refine ⟨64430877013843361835023029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85907836018457815780030705 64430877013843361835023029)
                ·
                  refine ⟨6040394720047815172033409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64430877013843361835023029 6040394720047815172033409)
                  ·
                    refine ⟨4530296040035861379025057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6040394720047815172033409 4530296040035861379025057)
                    ·
                      refine ⟨3397722030026896034268793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530296040035861379025057 3397722030026896034268793)
                      ·
                        rfl

theorem cell23_6617040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 2, 2].length) (baseStart_6617040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617040 prefixEnd_6617040 := by exact prefixLift 6617040
  have htrace : WordTrace (prefixWord ++ tailWord_6617040) baseStart_6617040 baseEnd_6617040 := by
    simpa [prefixWord, tailWord_6617040, baseEnd_6617040] using wordTrace_append hprefix tailTrace_6617040
  have hstable : (prefixWord ++ tailWord_6617040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617040).length < 2 ^ (prefixWord ++ tailWord_6617040).sum := by decide
  have hdescent : baseEnd_6617040 < baseStart_6617040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617057 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_6617057 : Nat := 118140960795 + 6617057 * 2 ^ 59
def prefixEnd_6617057 : Nat := 4983230072969 + 3 ^ 40 * 6617057 * 2
def baseEnd_6617057 : Nat := 3397730759198022467756215

theorem tailTrace_6617057 : CollatzResearch.WordTrace tailWord_6617057 prefixEnd_6617057 3397730759198022467756215 := by
  unfold tailWord_6617057
  simp only [CollatzResearch.WordTrace]
  refine ⟨241343895988540067208585425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160895930659026711472390283 241343895988540067208585425)
  ·
    refine ⟨181007921991405050406439069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241343895988540067208585425 181007921991405050406439069)
    ·
      refine ⟨67877970746776893902414651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181007921991405050406439069 67877970746776893902414651)
      ·
        refine ⟨101816956120165340853621977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67877970746776893902414651 101816956120165340853621977)
        ·
          refine ⟨76362717090124005640216483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101816956120165340853621977 76362717090124005640216483)
          ·
            refine ⟨114544075635186008460324725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76362717090124005640216483 114544075635186008460324725)
            ·
              refine ⟨10738507090798688293155443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114544075635186008460324725 10738507090798688293155443)
              ·
                refine ⟨16107760636198032439733165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738507090798688293155443 16107760636198032439733165)
                ·
                  refine ⟨6040410238574262164899937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16107760636198032439733165 6040410238574262164899937)
                  ·
                    refine ⟨4530307678930696623674953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6040410238574262164899937 4530307678930696623674953)
                    ·
                      refine ⟨3397730759198022467756215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530307678930696623674953 3397730759198022467756215)
                      ·
                        rfl

theorem cell23_6617057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_6617057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617057 prefixEnd_6617057 := by exact prefixLift 6617057
  have htrace : WordTrace (prefixWord ++ tailWord_6617057) baseStart_6617057 baseEnd_6617057 := by
    simpa [prefixWord, tailWord_6617057, baseEnd_6617057] using wordTrace_append hprefix tailTrace_6617057
  have hstable : (prefixWord ++ tailWord_6617057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617057).length < 2 ^ (prefixWord ++ tailWord_6617057).sum := by decide
  have hdescent : baseEnd_6617057 < baseStart_6617057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617117 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_6617117 : Nat := 118140960795 + 6617117 * 2 ^ 59
def prefixEnd_6617117 : Nat := 4983230072969 + 3 ^ 40 * 6617117 * 2
def baseEnd_6617117 : Nat := 3397761568037292233005939

theorem tailTrace_6617117 : CollatzResearch.WordTrace tailWord_6617117 prefixEnd_6617117 3397761568037292233005939 := by
  unfold tailWord_6617117
  simp only [CollatzResearch.WordTrace]
  refine ⟨241346084368322697455769605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160897389578881798303846403 241346084368322697455769605)
  ·
    refine ⟨45252390819060505772956801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241346084368322697455769605 45252390819060505772956801)
    ·
      refine ⟨33939293114295379329717601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45252390819060505772956801 33939293114295379329717601)
      ·
        refine ⟨25454469835721534497288201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33939293114295379329717601 25454469835721534497288201)
        ·
          refine ⟨19090852376791150872966151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25454469835721534497288201 19090852376791150872966151)
          ·
            refine ⟨28636278565186726309449227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19090852376791150872966151 28636278565186726309449227)
            ·
              refine ⟨42954417847780089464173841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28636278565186726309449227 42954417847780089464173841)
              ·
                refine ⟨32215813385835067098130381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42954417847780089464173841 32215813385835067098130381)
                ·
                  refine ⟨12080930019688150161798893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32215813385835067098130381 12080930019688150161798893)
                  ·
                    refine ⟨4530348757383056310674585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12080930019688150161798893 4530348757383056310674585)
                    ·
                      refine ⟨3397761568037292233005939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530348757383056310674585 3397761568037292233005939)
                      ·
                        rfl

theorem cell23_6617117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_6617117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617117 prefixEnd_6617117 := by exact prefixLift 6617117
  have htrace : WordTrace (prefixWord ++ tailWord_6617117) baseStart_6617117 baseEnd_6617117 := by
    simpa [prefixWord, tailWord_6617117, baseEnd_6617117] using wordTrace_append hprefix tailTrace_6617117
  have hstable : (prefixWord ++ tailWord_6617117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617117).length < 2 ^ (prefixWord ++ tailWord_6617117).sum := by decide
  have hdescent : baseEnd_6617117 < baseStart_6617117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617123 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 2, 6]
def baseStart_6617123 : Nat := 118140960795 + 6617123 * 2 ^ 59
def prefixEnd_6617123 : Nat := 4983230072969 + 3 ^ 40 * 6617123 * 2
def baseEnd_6617123 : Nat := 1132588216307073069843637

theorem tailTrace_6617123 : CollatzResearch.WordTrace tailWord_6617123 prefixEnd_6617123 1132588216307073069843637 := by
  unfold tailWord_6617123
  simp only [CollatzResearch.WordTrace]
  refine ⟨241346303206300960480488023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160897535470867306986992015 241346303206300960480488023)
  ·
    refine ⟨362019454809451440720732035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241346303206300960480488023 362019454809451440720732035)
    ·
      refine ⟨543029182214177161081098053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362019454809451440720732035 543029182214177161081098053)
      ·
        refine ⟨101817971665158217702705885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 543029182214177161081098053 101817971665158217702705885)
        ·
          refine ⟨38181739374434331638514707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101817971665158217702705885 38181739374434331638514707)
          ·
            refine ⟨57272609061651497457772061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38181739374434331638514707 57272609061651497457772061)
            ·
              refine ⟨21477228398119311546664523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57272609061651497457772061 21477228398119311546664523)
              ·
                refine ⟨32215842597178967319996785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21477228398119311546664523 32215842597178967319996785)
                ·
                  refine ⟨24161881947884225489997589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32215842597178967319996785 24161881947884225489997589)
                  ·
                    refine ⟨1132588216307073069843637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24161881947884225489997589 1132588216307073069843637)
                    ·
                      rfl

theorem cell23_6617123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 6].length) (baseStart_6617123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617123 prefixEnd_6617123 := by exact prefixLift 6617123
  have htrace : WordTrace (prefixWord ++ tailWord_6617123) baseStart_6617123 baseEnd_6617123 := by
    simpa [prefixWord, tailWord_6617123, baseEnd_6617123] using wordTrace_append hprefix tailTrace_6617123
  have hstable : (prefixWord ++ tailWord_6617123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617123).length < 2 ^ (prefixWord ++ tailWord_6617123).sum := by decide
  have hdescent : baseEnd_6617123 < baseStart_6617123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617163 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 3]
def baseStart_6617163 : Nat := 118140960795 + 6617163 * 2 ^ 59
def prefixEnd_6617163 : Nat := 4983230072969 + 3 ^ 40 * 6617163 * 2
def baseEnd_6617163 : Nat := 3397785188147399053030727

theorem tailTrace_6617163 : CollatzResearch.WordTrace tailWord_6617163 prefixEnd_6617163 3397785188147399053030727 := by
  unfold tailWord_6617163
  simp only [CollatzResearch.WordTrace]
  refine ⟨241347762126156047311944143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160898508084104031541296095 241347762126156047311944143)
  ·
    refine ⟨362021643189234070967916215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241347762126156047311944143 362021643189234070967916215)
    ·
      refine ⟨543032464783851106451874323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362021643189234070967916215 543032464783851106451874323)
      ·
        refine ⟨814548697175776659677811485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543032464783851106451874323 814548697175776659677811485)
        ·
          refine ⟨305455761440916247379179307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814548697175776659677811485 305455761440916247379179307)
          ·
            refine ⟨458183642161374371068768961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305455761440916247379179307 458183642161374371068768961)
            ·
              refine ⟨343637731621030778301576721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458183642161374371068768961 343637731621030778301576721)
              ·
                refine ⟨257728298715773083726182541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343637731621030778301576721 257728298715773083726182541)
                ·
                  refine ⟨96648112018414906397318453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257728298715773083726182541 96648112018414906397318453)
                  ·
                    refine ⟨9060760501726397474748605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96648112018414906397318453 9060760501726397474748605)
                    ·
                      refine ⟨3397785188147399053030727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9060760501726397474748605 3397785188147399053030727)
                      ·
                        rfl

theorem cell23_6617163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 3].length) (baseStart_6617163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617163 prefixEnd_6617163 := by exact prefixLift 6617163
  have htrace : WordTrace (prefixWord ++ tailWord_6617163) baseStart_6617163 baseEnd_6617163 := by
    simpa [prefixWord, tailWord_6617163, baseEnd_6617163] using wordTrace_append hprefix tailTrace_6617163
  have hstable : (prefixWord ++ tailWord_6617163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617163).length < 2 ^ (prefixWord ++ tailWord_6617163).sum := by decide
  have hdescent : baseEnd_6617163 < baseStart_6617163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617164 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 2, 2, 2]
def baseStart_6617164 : Nat := 118140960795 + 6617164 * 2 ^ 59
def prefixEnd_6617164 : Nat := 4983230072969 + 3 ^ 40 * 6617164 * 2
def baseEnd_6617164 : Nat := 3397785701628053549118223

theorem tailTrace_6617164 : CollatzResearch.WordTrace tailWord_6617164 prefixEnd_6617164 3397785701628053549118223 := by
  unfold tailWord_6617164
  simp only [CollatzResearch.WordTrace]
  refine ⟨120673899299576212241365273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160898532399434949655153697 120673899299576212241365273)
  ·
    refine ⟨90505424474682159181023955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120673899299576212241365273 90505424474682159181023955)
    ·
      refine ⟨135758136712023238771535933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90505424474682159181023955 135758136712023238771535933)
      ·
        refine ⟨50909301267008714539325975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135758136712023238771535933 50909301267008714539325975)
        ·
          refine ⟨76363951900513071808988963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50909301267008714539325975 76363951900513071808988963)
          ·
            refine ⟨114545927850769607713483445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76363951900513071808988963 114545927850769607713483445)
            ·
              refine ⟨10738680736009650723139073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114545927850769607713483445 10738680736009650723139073)
              ·
                refine ⟨8054010552007238042354305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10738680736009650723139073 8054010552007238042354305)
                ·
                  refine ⟨6040507914005428531765729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8054010552007238042354305 6040507914005428531765729)
                  ·
                    refine ⟨4530380935504071398824297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6040507914005428531765729 4530380935504071398824297)
                    ·
                      refine ⟨3397785701628053549118223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530380935504071398824297 3397785701628053549118223)
                      ·
                        rfl

theorem cell23_6617164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_6617164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617164 prefixEnd_6617164 := by exact prefixLift 6617164
  have htrace : WordTrace (prefixWord ++ tailWord_6617164) baseStart_6617164 baseEnd_6617164 := by
    simpa [prefixWord, tailWord_6617164, baseEnd_6617164] using wordTrace_append hprefix tailTrace_6617164
  have hstable : (prefixWord ++ tailWord_6617164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617164).length < 2 ^ (prefixWord ++ tailWord_6617164).sum := by decide
  have hdescent : baseEnd_6617164 < baseStart_6617164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617181 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6617181 : Nat := 118140960795 + 6617181 * 2 ^ 59
def prefixEnd_6617181 : Nat := 4983230072969 + 3 ^ 40 * 6617181 * 2
def baseEnd_6617181 : Nat := 3397794430799179982605645

theorem tailTrace_6617181 : CollatzResearch.WordTrace tailWord_6617181 prefixEnd_6617181 3397794430799179982605645 := by
  unfold tailWord_6617181
  simp only [CollatzResearch.WordTrace]
  refine ⟨241348418640090836386099397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160898945760060557590732931 241348418640090836386099397)
  ·
    refine ⟨45252828495017031822393637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241348418640090836386099397 45252828495017031822393637)
    ·
      refine ⟨8484905342815693466698807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45252828495017031822393637 8484905342815693466698807)
      ·
        refine ⟨12727358014223540200048211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8484905342815693466698807 12727358014223540200048211)
        ·
          refine ⟨19091037021335310300072317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12727358014223540200048211 19091037021335310300072317)
          ·
            refine ⟨7159138883000741362527119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19091037021335310300072317 7159138883000741362527119)
            ·
              refine ⟨10738708324501112043790679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7159138883000741362527119 10738708324501112043790679)
              ·
                refine ⟨16108062486751668065686019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738708324501112043790679 16108062486751668065686019)
                ·
                  refine ⟨24162093730127502098529029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16108062486751668065686019 24162093730127502098529029)
                  ·
                    refine ⟨4530392574398906643474193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24162093730127502098529029 4530392574398906643474193)
                    ·
                      refine ⟨3397794430799179982605645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530392574398906643474193 3397794430799179982605645)
                      ·
                        rfl

theorem cell23_6617181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6617181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617181 prefixEnd_6617181 := by exact prefixLift 6617181
  have htrace : WordTrace (prefixWord ++ tailWord_6617181) baseStart_6617181 baseEnd_6617181 := by
    simpa [prefixWord, tailWord_6617181, baseEnd_6617181] using wordTrace_append hprefix tailTrace_6617181
  have hstable : (prefixWord ++ tailWord_6617181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617181).length < 2 ^ (prefixWord ++ tailWord_6617181).sum := by decide
  have hdescent : baseEnd_6617181 < baseStart_6617181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617183 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 6, 5]
def baseStart_6617183 : Nat := 118140960795 + 6617183 * 2 ^ 59
def prefixEnd_6617183 : Nat := 4983230072969 + 3 ^ 40 * 6617183 * 2
def baseEnd_6617183 : Nat := 1132598485920162991593545

theorem tailTrace_6617183 : CollatzResearch.WordTrace tailWord_6617183 prefixEnd_6617183 1132598485920162991593545 := by
  unfold tailWord_6617183
  simp only [CollatzResearch.WordTrace]
  refine ⟨241348491586083590727672203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160898994390722393818448135 241348491586083590727672203)
  ·
    refine ⟨362022737379125386091508305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241348491586083590727672203 362022737379125386091508305)
    ·
      refine ⟨271517053034344039568631229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362022737379125386091508305 271517053034344039568631229)
      ·
        refine ⟨101818894887879014838236711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271517053034344039568631229 101818894887879014838236711)
        ·
          refine ⟨152728342331818522257355067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101818894887879014838236711 152728342331818522257355067)
          ·
            refine ⟨229092513497727783386032601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152728342331818522257355067 229092513497727783386032601)
            ·
              refine ⟨171819385123295837539524451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229092513497727783386032601 171819385123295837539524451)
              ·
                refine ⟨257729077684943756309286677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171819385123295837539524451 257729077684943756309286677)
                ·
                  refine ⟨12081050516481738576997813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 257729077684943756309286677 12081050516481738576997813)
                  ·
                    refine ⟨1132598485920162991593545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12081050516481738576997813 1132598485920162991593545)
                    ·
                      rfl

theorem cell23_6617183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_6617183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617183 prefixEnd_6617183 := by exact prefixLift 6617183
  have htrace : WordTrace (prefixWord ++ tailWord_6617183) baseStart_6617183 baseEnd_6617183 := by
    simpa [prefixWord, tailWord_6617183, baseEnd_6617183] using wordTrace_append hprefix tailTrace_6617183
  have hstable : (prefixWord ++ tailWord_6617183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617183).length < 2 ^ (prefixWord ++ tailWord_6617183).sum := by decide
  have hdescent : baseEnd_6617183 < baseStart_6617183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617217 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 2, 5]
def baseStart_6617217 : Nat := 118140960795 + 6617217 * 2 ^ 59
def prefixEnd_6617217 : Nat := 4983230072969 + 3 ^ 40 * 6617217 * 2
def baseEnd_6617217 : Nat := 1132604305367580613918493

theorem tailTrace_6617217 : CollatzResearch.WordTrace tailWord_6617217 prefixEnd_6617217 1132604305367580613918493 := by
  unfold tailWord_6617217
  simp only [CollatzResearch.WordTrace]
  refine ⟨241349731667960414534409905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160899821111973609689606603 241349731667960414534409905)
  ·
    refine ⟨181012298750970310900807429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241349731667960414534409905 181012298750970310900807429)
    ·
      refine ⟨33939806015806933293901393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181012298750970310900807429 33939806015806933293901393)
      ·
        refine ⟨25454854511855199970426045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33939806015806933293901393 25454854511855199970426045)
        ·
          refine ⟨9545570441945699988909767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25454854511855199970426045 9545570441945699988909767)
          ·
            refine ⟨14318355662918549983364651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9545570441945699988909767 14318355662918549983364651)
            ·
              refine ⟨21477533494377824975046977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14318355662918549983364651 21477533494377824975046977)
              ·
                refine ⟨16108150120783368731285233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21477533494377824975046977 16108150120783368731285233)
                ·
                  refine ⟨12081112590587526548463925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16108150120783368731285233 12081112590587526548463925)
                  ·
                    refine ⟨1132604305367580613918493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12081112590587526548463925 1132604305367580613918493)
                    ·
                      rfl

theorem cell23_6617217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_6617217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617217 prefixEnd_6617217 := by exact prefixLift 6617217
  have htrace : WordTrace (prefixWord ++ tailWord_6617217) baseStart_6617217 baseEnd_6617217 := by
    simpa [prefixWord, tailWord_6617217, baseEnd_6617217] using wordTrace_append hprefix tailTrace_6617217
  have hstable : (prefixWord ++ tailWord_6617217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617217).length < 2 ^ (prefixWord ++ tailWord_6617217).sum := by decide
  have hdescent : baseEnd_6617217 < baseStart_6617217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617263 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_6617263 : Nat := 118140960795 + 6617263 * 2 ^ 59
def prefixEnd_6617263 : Nat := 4983230072969 + 3 ^ 40 * 6617263 * 2
def baseEnd_6617263 : Nat := 3397836536212848661780267

theorem tailTrace_6617263 : CollatzResearch.WordTrace tailWord_6617263 prefixEnd_6617263 3397836536212848661780267 := by
  unfold tailWord_6617263
  simp only [CollatzResearch.WordTrace]
  refine ⟨241351409425793764390584443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160900939617195842927056295 241351409425793764390584443)
  ·
    refine ⟨362027114138690646585876665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241351409425793764390584443 362027114138690646585876665)
    ·
      refine ⟨271520335604017984939407499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362027114138690646585876665 271520335604017984939407499)
      ·
        refine ⟨407280503406026977409111249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271520335604017984939407499 407280503406026977409111249)
        ·
          refine ⟨305460377554520233056833437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407280503406026977409111249 305460377554520233056833437)
          ·
            refine ⟨114547641582945087396312539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305460377554520233056833437 114547641582945087396312539)
            ·
              refine ⟨171821462374417631094468809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114547641582945087396312539 171821462374417631094468809)
              ·
                refine ⟨128866096780813223320851607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171821462374417631094468809 128866096780813223320851607)
                ·
                  refine ⟨193299145171219834981277411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128866096780813223320851607 193299145171219834981277411)
                  ·
                    refine ⟨289948717756829752471916117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193299145171219834981277411 289948717756829752471916117)
                    ·
                      refine ⟨3397836536212848661780267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 289948717756829752471916117 3397836536212848661780267)
                      ·
                        rfl

theorem cell23_6617263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_6617263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617263 prefixEnd_6617263 := by exact prefixLift 6617263
  have htrace : WordTrace (prefixWord ++ tailWord_6617263) baseStart_6617263 baseEnd_6617263 := by
    simpa [prefixWord, tailWord_6617263, baseEnd_6617263] using wordTrace_append hprefix tailTrace_6617263
  have hstable : (prefixWord ++ tailWord_6617263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617263).length < 2 ^ (prefixWord ++ tailWord_6617263).sum := by decide
  have hdescent : baseEnd_6617263 < baseStart_6617263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617290 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_6617290 : Nat := 118140960795 + 6617290 * 2 ^ 59
def prefixEnd_6617290 : Nat := 4983230072969 + 3 ^ 40 * 6617290 * 2
def baseEnd_6617290 : Nat := 1132616800063506685380881

theorem tailTrace_6617290 : CollatzResearch.WordTrace tailWord_6617290 prefixEnd_6617290 1132616800063506685380881 := by
  unfold tailWord_6617290
  simp only [CollatzResearch.WordTrace]
  refine ⟨60338098549173987000454331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160901596131130632001211549 60338098549173987000454331)
  ·
    refine ⟨90507147823760980500681497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60338098549173987000454331 90507147823760980500681497)
    ·
      refine ⟨67880360867820735375511123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90507147823760980500681497 67880360867820735375511123)
      ·
        refine ⟨101820541301731103063266685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67880360867820735375511123 101820541301731103063266685)
        ·
          refine ⟨38182702988149163648725007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101820541301731103063266685 38182702988149163648725007)
          ·
            refine ⟨57274054482223745473087511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38182702988149163648725007 57274054482223745473087511)
            ·
              refine ⟨85911081723335618209631267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57274054482223745473087511 85911081723335618209631267)
              ·
                refine ⟨128866622585003427314446901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85911081723335618209631267 128866622585003427314446901)
                ·
                  refine ⟨12081245867344071310729397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128866622585003427314446901 12081245867344071310729397)
                  ·
                    refine ⟨1132616800063506685380881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12081245867344071310729397 1132616800063506685380881)
                    ·
                      rfl

theorem cell23_6617290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_6617290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617290 prefixEnd_6617290 := by exact prefixLift 6617290
  have htrace : WordTrace (prefixWord ++ tailWord_6617290) baseStart_6617290 baseEnd_6617290 := by
    simpa [prefixWord, tailWord_6617290, baseEnd_6617290] using wordTrace_append hprefix tailTrace_6617290
  have hstable : (prefixWord ++ tailWord_6617290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617290).length < 2 ^ (prefixWord ++ tailWord_6617290).sum := by decide
  have hdescent : baseEnd_6617290 < baseStart_6617290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617297 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 4, 3, 2]
def baseStart_6617297 : Nat := 118140960795 + 6617297 * 2 ^ 59
def prefixEnd_6617297 : Nat := 4983230072969 + 3 ^ 40 * 6617297 * 2
def baseEnd_6617297 : Nat := 3397853994555101528755111

theorem tailTrace_6617297 : CollatzResearch.WordTrace tailWord_6617297 prefixEnd_6617297 3397853994555101528755111 := by
  unfold tailWord_6617297
  simp only [CollatzResearch.WordTrace]
  refine ⟨241352649507670588197322145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160901766338447058798214763 241352649507670588197322145)
  ·
    refine ⟨181014487130752941147991609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241352649507670588197322145 181014487130752941147991609)
    ·
      refine ⟨135760865348064705860993707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181014487130752941147991609 135760865348064705860993707)
      ·
        refine ⟨203641298022097058791490561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135760865348064705860993707 203641298022097058791490561)
        ·
          refine ⟨152730973516572794093617921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203641298022097058791490561 152730973516572794093617921)
          ·
            refine ⟨114548230137429595570213441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152730973516572794093617921 114548230137429595570213441)
            ·
              refine ⟨85911172603072196677660081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114548230137429595570213441 85911172603072196677660081)
              ·
                refine ⟨64433379452304147508245061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85911172603072196677660081 64433379452304147508245061)
                ·
                  refine ⟨12081258647307027657795949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64433379452304147508245061 12081258647307027657795949)
                  ·
                    refine ⟨4530471992740135371673481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12081258647307027657795949 4530471992740135371673481)
                    ·
                      refine ⟨3397853994555101528755111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530471992740135371673481 3397853994555101528755111)
                      ·
                        rfl

theorem cell23_6617297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_6617297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617297 prefixEnd_6617297 := by exact prefixLift 6617297
  have htrace : WordTrace (prefixWord ++ tailWord_6617297) baseStart_6617297 baseEnd_6617297 := by
    simpa [prefixWord, tailWord_6617297, baseEnd_6617297] using wordTrace_append hprefix tailTrace_6617297
  have hstable : (prefixWord ++ tailWord_6617297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617297).length < 2 ^ (prefixWord ++ tailWord_6617297).sum := by decide
  have hdescent : baseEnd_6617297 < baseStart_6617297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617304 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_6617304 : Nat := 118140960795 + 6617304 * 2 ^ 59
def prefixEnd_6617304 : Nat := 4983230072969 + 3 ^ 40 * 6617304 * 2
def baseEnd_6617304 : Nat := 3397857588919683001367579

theorem tailTrace_6617304 : CollatzResearch.WordTrace tailWord_6617304 prefixEnd_6617304 3397857588919683001367579 := by
  unfold tailWord_6617304
  simp only [CollatzResearch.WordTrace]
  refine ⟨120676452409322614196413483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160901936545763485595217977 120676452409322614196413483)
  ·
    refine ⟨181014678613983921294620225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120676452409322614196413483 181014678613983921294620225)
    ·
      refine ⟨135761008960487940970965169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181014678613983921294620225 135761008960487940970965169)
      ·
        refine ⟨101820756720365955728223877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135761008960487940970965169 101820756720365955728223877)
        ·
          refine ⟨19091391885068616699041977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101820756720365955728223877 19091391885068616699041977)
          ·
            refine ⟨14318543913801462524281483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19091391885068616699041977 14318543913801462524281483)
            ·
              refine ⟨21477815870702193786422225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14318543913801462524281483 21477815870702193786422225)
              ·
                refine ⟨16108361903026645339816669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21477815870702193786422225 16108361903026645339816669)
                ·
                  refine ⟨6040635713634992002431251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16108361903026645339816669 6040635713634992002431251)
                  ·
                    refine ⟨9060953570452488003646877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6040635713634992002431251 9060953570452488003646877)
                    ·
                      refine ⟨3397857588919683001367579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9060953570452488003646877 3397857588919683001367579)
                      ·
                        rfl

theorem cell23_6617304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_6617304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617304 prefixEnd_6617304 := by exact prefixLift 6617304
  have htrace : WordTrace (prefixWord ++ tailWord_6617304) baseStart_6617304 baseEnd_6617304 := by
    simpa [prefixWord, tailWord_6617304, baseEnd_6617304] using wordTrace_append hprefix tailTrace_6617304
  have hstable : (prefixWord ++ tailWord_6617304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617304).length < 2 ^ (prefixWord ++ tailWord_6617304).sum := by decide
  have hdescent : baseEnd_6617304 < baseStart_6617304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617308 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6617308 : Nat := 118140960795 + 6617308 * 2 ^ 59
def prefixEnd_6617308 : Nat := 4983230072969 + 3 ^ 40 * 6617308 * 2
def baseEnd_6617308 : Nat := 3397859642842300985717561

theorem tailTrace_6617308 : CollatzResearch.WordTrace tailWord_6617308 prefixEnd_6617308 3397859642842300985717561 := by
  unfold tailWord_6617308
  simp only [CollatzResearch.WordTrace]
  refine ⟨120676525355315368537986289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160902033807087158050648385 120676525355315368537986289)
  ·
    refine ⟨90507394016486526403489717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120676525355315368537986289 90507394016486526403489717)
    ·
      refine ⟨8485068189045611850327161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90507394016486526403489717 8485068189045611850327161)
      ·
        refine ⟨6363801141784208887745371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8485068189045611850327161 6363801141784208887745371)
        ·
          refine ⟨9545701712676313331618057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6363801141784208887745371 9545701712676313331618057)
          ·
            refine ⟨7159276284507234998713543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9545701712676313331618057 7159276284507234998713543)
            ·
              refine ⟨10738914426760852498070315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7159276284507234998713543 10738914426760852498070315)
              ·
                refine ⟨16108371640141278747105473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738914426760852498070315 16108371640141278747105473)
                ·
                  refine ⟨12081278730105959060329105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16108371640141278747105473 12081278730105959060329105)
                  ·
                    refine ⟨9060959047579469295246829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12081278730105959060329105 9060959047579469295246829)
                    ·
                      refine ⟨3397859642842300985717561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9060959047579469295246829 3397859642842300985717561)
                      ·
                        rfl

theorem cell23_6617308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6617308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617308 prefixEnd_6617308 := by exact prefixLift 6617308
  have htrace : WordTrace (prefixWord ++ tailWord_6617308) baseStart_6617308 baseEnd_6617308 := by
    simpa [prefixWord, tailWord_6617308, baseEnd_6617308] using wordTrace_append hprefix tailTrace_6617308
  have hstable : (prefixWord ++ tailWord_6617308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617308).length < 2 ^ (prefixWord ++ tailWord_6617308).sum := by decide
  have hdescent : baseEnd_6617308 < baseStart_6617308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617337 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 2, 4]
def baseStart_6617337 : Nat := 118140960795 + 6617337 * 2 ^ 59
def prefixEnd_6617337 : Nat := 4983230072969 + 3 ^ 40 * 6617337 * 2
def baseEnd_6617337 : Nat := 1132624844593760457418309

theorem tailTrace_6617337 : CollatzResearch.WordTrace tailWord_6617337 prefixEnd_6617337 1132624844593760457418309 := by
  unfold tailWord_6617337
  simp only [CollatzResearch.WordTrace]
  refine ⟨241354108427525675028778265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160902738951683783352518843 241354108427525675028778265)
  ·
    refine ⟨181015581320644256271583699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241354108427525675028778265 181015581320644256271583699)
    ·
      refine ⟨271523371980966384407375549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181015581320644256271583699 271523371980966384407375549)
      ·
        refine ⟨101821264492862394152765831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271523371980966384407375549 101821264492862394152765831)
        ·
          refine ⟨152731896739293591229148747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101821264492862394152765831 152731896739293591229148747)
          ·
            refine ⟨229097845108940386843723121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152731896739293591229148747 229097845108940386843723121)
            ·
              refine ⟨171823383831705290132792341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229097845108940386843723121 171823383831705290132792341)
              ·
                refine ⟨8054221117111185474974641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171823383831705290132792341 8054221117111185474974641)
                ·
                  refine ⟨6040665837833389106230981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8054221117111185474974641 6040665837833389106230981)
                  ·
                    refine ⟨1132624844593760457418309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040665837833389106230981 1132624844593760457418309)
                    ·
                      rfl

theorem cell23_6617337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 4].length) (baseStart_6617337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617337 prefixEnd_6617337 := by exact prefixLift 6617337
  have htrace : WordTrace (prefixWord ++ tailWord_6617337) baseStart_6617337 baseEnd_6617337 := by
    simpa [prefixWord, tailWord_6617337, baseEnd_6617337] using wordTrace_append hprefix tailTrace_6617337
  have hstable : (prefixWord ++ tailWord_6617337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617337).length < 2 ^ (prefixWord ++ tailWord_6617337).sum := by decide
  have hdescent : baseEnd_6617337 < baseStart_6617337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617344 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 3, 2, 2]
def baseStart_6617344 : Nat := 118140960795 + 6617344 * 2 ^ 59
def prefixEnd_6617344 : Nat := 4983230072969 + 3 ^ 40 * 6617344 * 2
def baseEnd_6617344 : Nat := 3397878128145862844867395

theorem tailTrace_6617344 : CollatzResearch.WordTrace tailWord_6617344 prefixEnd_6617344 3397878128145862844867395 := by
  unfold tailWord_6617344
  simp only [CollatzResearch.WordTrace]
  refine ⟨120677181869250157612141543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160902909159000210149522057 120677181869250157612141543)
  ·
    refine ⟨181015772803875236418212315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120677181869250157612141543 181015772803875236418212315)
    ·
      refine ⟨271523659205812854627318473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181015772803875236418212315 271523659205812854627318473)
      ·
        refine ⟨203642744404359640970488855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271523659205812854627318473 203642744404359640970488855)
        ·
          refine ⟨305464116606539461455733283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203642744404359640970488855 305464116606539461455733283)
          ·
            refine ⟨458196174909809192183599925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305464116606539461455733283 458196174909809192183599925)
            ·
              refine ⟨42955891397794611767212493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458196174909809192183599925 42955891397794611767212493)
              ·
                refine ⟨16108459274172979412704685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42955891397794611767212493 16108459274172979412704685)
                ·
                  refine ⟨6040672227814867279764257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16108459274172979412704685 6040672227814867279764257)
                  ·
                    refine ⟨4530504170861150459823193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6040672227814867279764257 4530504170861150459823193)
                    ·
                      refine ⟨3397878128145862844867395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530504170861150459823193 3397878128145862844867395)
                      ·
                        rfl

theorem cell23_6617344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_6617344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617344 prefixEnd_6617344 := by exact prefixLift 6617344
  have htrace : WordTrace (prefixWord ++ tailWord_6617344) baseStart_6617344 baseEnd_6617344 := by
    simpa [prefixWord, tailWord_6617344, baseEnd_6617344] using wordTrace_append hprefix tailTrace_6617344
  have hstable : (prefixWord ++ tailWord_6617344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617344).length < 2 ^ (prefixWord ++ tailWord_6617344).sum := by decide
  have hdescent : baseEnd_6617344 < baseStart_6617344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617367 : List Nat := [1, 1, 3, 4, 1, 2, 4, 7]
def baseStart_6617367 : Nat := 118140960795 + 6617367 * 2 ^ 59
def prefixEnd_6617367 : Nat := 4983230072969 + 3 ^ 40 * 6617367 * 2
def baseEnd_6617367 : Nat := 125847775488922824254807

theorem tailTrace_6617367 : CollatzResearch.WordTrace tailWord_6617367 prefixEnd_6617367 125847775488922824254807 := by
  unfold tailWord_6617367
  simp only [CollatzResearch.WordTrace]
  refine ⟨241355202617416990152370355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160903468411611326768246903 241355202617416990152370355)
  ·
    refine ⟨362032803926125485228555533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241355202617416990152370355 362032803926125485228555533)
    ·
      refine ⟨135762301472297056960708325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362032803926125485228555533 135762301472297056960708325)
      ·
        refine ⟨25455431526055698180132811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135762301472297056960708325 25455431526055698180132811)
        ·
          refine ⟨38183147289083547270199217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25455431526055698180132811 38183147289083547270199217)
          ·
            refine ⟨28637360466812660452649413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38183147289083547270199217 28637360466812660452649413)
            ·
              refine ⟨5369505087527373834871765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28637360466812660452649413 5369505087527373834871765)
              ·
                refine ⟨125847775488922824254807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5369505087527373834871765 125847775488922824254807)
                ·
                  rfl

theorem cell23_6617367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 7].length) (baseStart_6617367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617367 prefixEnd_6617367 := by exact prefixLift 6617367
  have htrace : WordTrace (prefixWord ++ tailWord_6617367) baseStart_6617367 baseEnd_6617367 := by
    simpa [prefixWord, tailWord_6617367, baseEnd_6617367] using wordTrace_append hprefix tailTrace_6617367
  have hstable : (prefixWord ++ tailWord_6617367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617367).length < 2 ^ (prefixWord ++ tailWord_6617367).sum := by decide
  have hdescent : baseEnd_6617367 < baseStart_6617367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617377 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_6617377 : Nat := 118140960795 + 6617377 * 2 ^ 59
def prefixEnd_6617377 : Nat := 4983230072969 + 3 ^ 40 * 6617377 * 2
def baseEnd_6617377 : Nat := 3397895073007461215754743

theorem tailTrace_6617377 : CollatzResearch.WordTrace tailWord_6617377 prefixEnd_6617377 3397895073007461215754743 := by
  unfold tailWord_6617377
  simp only [CollatzResearch.WordTrace]
  refine ⟨241355567347380761860234385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160903711564920507906822923 241355567347380761860234385)
  ·
    refine ⟨181016675510535571395175789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241355567347380761860234385 181016675510535571395175789)
    ·
      refine ⟨67881253316450839273190921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181016675510535571395175789 67881253316450839273190921)
      ·
        refine ⟨50910939987338129454893191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67881253316450839273190921 50910939987338129454893191)
        ·
          refine ⟨76366409981007194182339787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50910939987338129454893191 76366409981007194182339787)
          ·
            refine ⟨114549614971510791273509681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76366409981007194182339787 114549614971510791273509681)
            ·
              refine ⟨85912211228633093455132261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114549614971510791273509681 85912211228633093455132261)
              ·
                refine ⟨16108539605368705022837299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85912211228633093455132261 16108539605368705022837299)
                ·
                  refine ⟨24162809408053057534255949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16108539605368705022837299 24162809408053057534255949)
                  ·
                    refine ⟨9061053528019896575345981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24162809408053057534255949 9061053528019896575345981)
                    ·
                      refine ⟨3397895073007461215754743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9061053528019896575345981 3397895073007461215754743)
                      ·
                        rfl

theorem cell23_6617377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_6617377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617377 prefixEnd_6617377 := by exact prefixLift 6617377
  have htrace : WordTrace (prefixWord ++ tailWord_6617377) baseStart_6617377 baseEnd_6617377 := by
    simpa [prefixWord, tailWord_6617377, baseEnd_6617377] using wordTrace_append hprefix tailTrace_6617377
  have hstable : (prefixWord ++ tailWord_6617377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617377).length < 2 ^ (prefixWord ++ tailWord_6617377).sum := by decide
  have hdescent : baseEnd_6617377 < baseStart_6617377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617384 : List Nat := [2, 1, 5, 1, 4, 1, 9]
def baseStart_6617384 : Nat := 118140960795 + 6617384 * 2 ^ 59
def prefixEnd_6617384 : Nat := 4983230072969 + 3 ^ 40 * 6617384 * 2
def baseEnd_6617384 : Nat := 41949366263852378868731

theorem tailTrace_6617384 : CollatzResearch.WordTrace tailWord_6617384 prefixEnd_6617384 41949366263852378868731 := by
  unfold tailWord_6617384
  simp only [CollatzResearch.WordTrace]
  refine ⟨120677911329177701027869603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160903881772236934703826137 120677911329177701027869603)
  ·
    refine ⟨181016866993766551541804405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120677911329177701027869603 181016866993766551541804405)
    ·
      refine ⟨16970331280665614207044163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181016866993766551541804405 16970331280665614207044163)
      ·
        refine ⟨25455496920998421310566245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16970331280665614207044163 25455496920998421310566245)
        ·
          refine ⟨4772905672687203995731171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25455496920998421310566245 4772905672687203995731171)
          ·
            refine ⟨7159358509030805993596757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772905672687203995731171 7159358509030805993596757)
            ·
              refine ⟨41949366263852378868731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7159358509030805993596757 41949366263852378868731)
              ·
                rfl

theorem cell23_6617384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 9].length) (baseStart_6617384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617384 prefixEnd_6617384 := by exact prefixLift 6617384
  have htrace : WordTrace (prefixWord ++ tailWord_6617384) baseStart_6617384 baseEnd_6617384 := by
    simpa [prefixWord, tailWord_6617384, baseEnd_6617384] using wordTrace_append hprefix tailTrace_6617384
  have hstable : (prefixWord ++ tailWord_6617384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617384).length < 2 ^ (prefixWord ++ tailWord_6617384).sum := by decide
  have hdescent : baseEnd_6617384 < baseStart_6617384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617404 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_6617404 : Nat := 118140960795 + 6617404 * 2 ^ 59
def prefixEnd_6617404 : Nat := 4983230072969 + 3 ^ 40 * 6617404 * 2
def baseEnd_6617404 : Nat := 3397908936985132610117119

theorem tailTrace_6617404 : CollatzResearch.WordTrace tailWord_6617404 prefixEnd_6617404 3397908936985132610117119 := by
  unfold tailWord_6617404
  simp only [CollatzResearch.WordTrace]
  refine ⟨120678276059141472735733633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160904368078855296980978177 120678276059141472735733633)
  ·
    refine ⟨90508707044356104551800225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120678276059141472735733633 90508707044356104551800225)
    ·
      refine ⟨67881530283267078413850169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90508707044356104551800225 67881530283267078413850169)
      ·
        refine ⟨50911147712450308810387627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67881530283267078413850169 50911147712450308810387627)
        ·
          refine ⟨76366721568675463215581441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50911147712450308810387627 76366721568675463215581441)
          ·
            refine ⟨57275041176506597411686081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76366721568675463215581441 57275041176506597411686081)
            ·
              refine ⟨42956280882379948058764561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57275041176506597411686081 42956280882379948058764561)
              ·
                refine ⟨32217210661784961044073421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42956280882379948058764561 32217210661784961044073421)
                ·
                  refine ⟨12081453998169360391527533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32217210661784961044073421 12081453998169360391527533)
                  ·
                    refine ⟨4530545249313510146822825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12081453998169360391527533 4530545249313510146822825)
                    ·
                      refine ⟨3397908936985132610117119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530545249313510146822825 3397908936985132610117119)
                      ·
                        rfl

theorem cell23_6617404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_6617404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617404 prefixEnd_6617404 := by exact prefixLift 6617404
  have htrace : WordTrace (prefixWord ++ tailWord_6617404) baseStart_6617404 baseEnd_6617404 := by
    simpa [prefixWord, tailWord_6617404, baseEnd_6617404] using wordTrace_append hprefix tailTrace_6617404
  have hstable : (prefixWord ++ tailWord_6617404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617404).length < 2 ^ (prefixWord ++ tailWord_6617404).sum := by decide
  have hdescent : baseEnd_6617404 < baseStart_6617404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617411 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 2, 1, 3]
def baseStart_6617411 : Nat := 118140960795 + 6617411 * 2 ^ 59
def prefixEnd_6617411 : Nat := 4983230072969 + 3 ^ 40 * 6617411 * 2
def baseEnd_6617411 : Nat := 3397912531349714082729587

theorem tailTrace_6617411 : CollatzResearch.WordTrace tailWord_6617411 prefixEnd_6617411 3397912531349714082729587 := by
  unfold tailWord_6617411
  simp only [CollatzResearch.WordTrace]
  refine ⟨241356807429257585666972087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160904538286171723777981391 241356807429257585666972087)
  ·
    refine ⟨362035211143886378500458131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241356807429257585666972087 362035211143886378500458131)
    ·
      refine ⟨543052816715829567750687197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362035211143886378500458131 543052816715829567750687197)
      ·
        refine ⟨203644806268436087906507699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 543052816715829567750687197 203644806268436087906507699)
        ·
          refine ⟨305467209402654131859761549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203644806268436087906507699 305467209402654131859761549)
          ·
            refine ⟨114550203525995299447410581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305467209402654131859761549 114550203525995299447410581)
            ·
              refine ⟨5369540790281029661597371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114550203525995299447410581 5369540790281029661597371)
              ·
                refine ⟨8054311185421544492396057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369540790281029661597371 8054311185421544492396057)
                ·
                  refine ⟨6040733389066158369297043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8054311185421544492396057 6040733389066158369297043)
                  ·
                    refine ⟨9061100083599237553945565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6040733389066158369297043 9061100083599237553945565)
                    ·
                      refine ⟨3397912531349714082729587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9061100083599237553945565 3397912531349714082729587)
                      ·
                        rfl

theorem cell23_6617411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_6617411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617411 prefixEnd_6617411 := by exact prefixLift 6617411
  have htrace : WordTrace (prefixWord ++ tailWord_6617411) baseStart_6617411 baseEnd_6617411 := by
    simpa [prefixWord, tailWord_6617411, baseEnd_6617411] using wordTrace_append hprefix tailTrace_6617411
  have hstable : (prefixWord ++ tailWord_6617411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617411).length < 2 ^ (prefixWord ++ tailWord_6617411).sum := by decide
  have hdescent : baseEnd_6617411 < baseStart_6617411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617467 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 3]
def baseStart_6617467 : Nat := 118140960795 + 6617467 * 2 ^ 59
def prefixEnd_6617467 : Nat := 4983230072969 + 3 ^ 40 * 6617467 * 2
def baseEnd_6617467 : Nat := 3397941286266365863629329

theorem tailTrace_6617467 : CollatzResearch.WordTrace tailWord_6617467 prefixEnd_6617467 3397941286266365863629329 := by
  unfold tailWord_6617467
  simp only [CollatzResearch.WordTrace]
  refine ⟨241358849917054707231010655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160905899944703138154007103 241358849917054707231010655)
  ·
    refine ⟨362038274875582060846515983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241358849917054707231010655 362038274875582060846515983)
    ·
      refine ⟨543057412313373091269773975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362038274875582060846515983 543057412313373091269773975)
      ·
        refine ⟨814586118470059636904660963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543057412313373091269773975 814586118470059636904660963)
        ·
          refine ⟨1221879177705089455356991445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814586118470059636904660963 1221879177705089455356991445)
          ·
            refine ⟨28637793227463034109929487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1221879177705089455356991445 28637793227463034109929487)
            ·
              refine ⟨42956689841194551164894231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28637793227463034109929487 42956689841194551164894231)
              ·
                refine ⟨64435034761791826747341347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42956689841194551164894231 64435034761791826747341347)
                ·
                  refine ⟨96652552142687740121012021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64435034761791826747341347 96652552142687740121012021)
                  ·
                    refine ⟨9061176763376975636344877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96652552142687740121012021 9061176763376975636344877)
                    ·
                      refine ⟨3397941286266365863629329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9061176763376975636344877 3397941286266365863629329)
                      ·
                        rfl

theorem cell23_6617467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 3].length) (baseStart_6617467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617467 prefixEnd_6617467 := by exact prefixLift 6617467
  have htrace : WordTrace (prefixWord ++ tailWord_6617467) baseStart_6617467 baseEnd_6617467 := by
    simpa [prefixWord, tailWord_6617467, baseEnd_6617467] using wordTrace_append hprefix tailTrace_6617467
  have hstable : (prefixWord ++ tailWord_6617467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617467).length < 2 ^ (prefixWord ++ tailWord_6617467).sum := by decide
  have hdescent : baseEnd_6617467 < baseStart_6617467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617502 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6617502 : Nat := 118140960795 + 6617502 * 2 ^ 59
def prefixEnd_6617502 : Nat := 4983230072969 + 3 ^ 40 * 6617502 * 2
def baseEnd_6617502 : Nat := 3397959258089273226691669

theorem tailTrace_6617502 : CollatzResearch.WordTrace tailWord_6617502 prefixEnd_6617502 3397959258089273226691669 := by
  unfold tailWord_6617502
  simp only [CollatzResearch.WordTrace]
  refine ⟨30170015808990988526066845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160906750981285272139023173 30170015808990988526066845)
  ·
    refine ⟨11313755928371620697275067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30170015808990988526066845 11313755928371620697275067)
    ·
      refine ⟨16970633892557431045912601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11313755928371620697275067 16970633892557431045912601)
      ·
        refine ⟨12727975419418073284434451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16970633892557431045912601 12727975419418073284434451)
        ·
          refine ⟨19091963129127109926651677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12727975419418073284434451 19091963129127109926651677)
          ·
            refine ⟨7159486173422666222494379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19091963129127109926651677 7159486173422666222494379)
            ·
              refine ⟨10739229260133999333741569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7159486173422666222494379 10739229260133999333741569)
              ·
                refine ⟨8054421945100499500306177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10739229260133999333741569 8054421945100499500306177)
                ·
                  refine ⟨6040816458825374625229633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8054421945100499500306177 6040816458825374625229633)
                  ·
                    refine ⟨4530612344119030968922225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6040816458825374625229633 4530612344119030968922225)
                    ·
                      refine ⟨3397959258089273226691669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530612344119030968922225 3397959258089273226691669)
                      ·
                        rfl

theorem cell23_6617502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6617502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617502 prefixEnd_6617502 := by exact prefixLift 6617502
  have htrace : WordTrace (prefixWord ++ tailWord_6617502) baseStart_6617502 baseEnd_6617502 := by
    simpa [prefixWord, tailWord_6617502, baseEnd_6617502] using wordTrace_append hprefix tailTrace_6617502
  have hstable : (prefixWord ++ tailWord_6617502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617502).length < 2 ^ (prefixWord ++ tailWord_6617502).sum := by decide
  have hdescent : baseEnd_6617502 < baseStart_6617502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617544 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_6617544 : Nat := 118140960795 + 6617544 * 2 ^ 59
def prefixEnd_6617544 : Nat := 4983230072969 + 3 ^ 40 * 6617544 * 2
def baseEnd_6617544 : Nat := 3397980824276762062366475

theorem tailTrace_6617544 : CollatzResearch.WordTrace tailWord_6617544 prefixEnd_6617544 3397980824276762062366475 := by
  unfold tailWord_6617544
  simp only [CollatzResearch.WordTrace]
  refine ⟨120680829168887874690781843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160907772225183832921042457 120680829168887874690781843)
  ·
    refine ⟨181021243753331812036172765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120680829168887874690781843 181021243753331812036172765)
    ·
      refine ⟨67882966407499429513564787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181021243753331812036172765 67882966407499429513564787)
      ·
        refine ⟨101824449611249144270347181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67882966407499429513564787 101824449611249144270347181)
        ·
          refine ⟨38184168604218429101380193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101824449611249144270347181 38184168604218429101380193)
          ·
            refine ⟨28638126453163821826035145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38184168604218429101380193 28638126453163821826035145)
            ·
              refine ⟨21478594839872866369526359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28638126453163821826035145 21478594839872866369526359)
              ·
                refine ⟨32217892259809299554289539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21478594839872866369526359 32217892259809299554289539)
                ·
                  refine ⟨48326838389713949331434309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32217892259809299554289539 48326838389713949331434309)
                  ·
                    refine ⟨9061282198071365499643933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48326838389713949331434309 9061282198071365499643933)
                    ·
                      refine ⟨3397980824276762062366475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9061282198071365499643933 3397980824276762062366475)
                      ·
                        rfl

theorem cell23_6617544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_6617544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617544 prefixEnd_6617544 := by exact prefixLift 6617544
  have htrace : WordTrace (prefixWord ++ tailWord_6617544) baseStart_6617544 baseEnd_6617544 := by
    simpa [prefixWord, tailWord_6617544, baseEnd_6617544] using wordTrace_append hprefix tailTrace_6617544
  have hstable : (prefixWord ++ tailWord_6617544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617544).length < 2 ^ (prefixWord ++ tailWord_6617544).sum := by decide
  have hdescent : baseEnd_6617544 < baseStart_6617544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617568 : List Nat := [2, 1, 1, 3, 1, 1, 7, 2, 1, 4]
def baseStart_6617568 : Nat := 118140960795 + 6617568 * 2 ^ 59
def prefixEnd_6617568 : Nat := 4983230072969 + 3 ^ 40 * 6617568 * 2
def baseEnd_6617568 : Nat := 1132664382604156656155455

theorem tailTrace_6617568 : CollatzResearch.WordTrace tailWord_6617568 prefixEnd_6617568 1132664382604156656155455 := by
  unfold tailWord_6617568
  simp only [CollatzResearch.WordTrace]
  refine ⟨120681266844844400740218679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160908355793125867653624905 120681266844844400740218679)
  ·
    refine ⟨181021900267266601110328019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120681266844844400740218679 181021900267266601110328019)
    ·
      refine ⟨271532850400899901665492029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181021900267266601110328019 271532850400899901665492029)
      ·
        refine ⟨101824818900337463124559511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271532850400899901665492029 101824818900337463124559511)
        ·
          refine ⟨152737228350506194686839267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101824818900337463124559511 152737228350506194686839267)
          ·
            refine ⟨229105842525759292030258901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152737228350506194686839267 229105842525759292030258901)
            ·
              refine ⟨5369668184197483406959193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 229105842525759292030258901 5369668184197483406959193)
              ·
                refine ⟨4027251138148112555219395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5369668184197483406959193 4027251138148112555219395)
                ·
                  refine ⟨6040876707222168832829093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027251138148112555219395 6040876707222168832829093)
                  ·
                    refine ⟨1132664382604156656155455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6040876707222168832829093 1132664382604156656155455)
                    ·
                      rfl

theorem cell23_6617568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 4].length) (baseStart_6617568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617568 prefixEnd_6617568 := by exact prefixLift 6617568
  have htrace : WordTrace (prefixWord ++ tailWord_6617568) baseStart_6617568 baseEnd_6617568 := by
    simpa [prefixWord, tailWord_6617568, baseEnd_6617568] using wordTrace_append hprefix tailTrace_6617568
  have hstable : (prefixWord ++ tailWord_6617568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617568).length < 2 ^ (prefixWord ++ tailWord_6617568).sum := by decide
  have hdescent : baseEnd_6617568 < baseStart_6617568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617581 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 6]
def baseStart_6617581 : Nat := 118140960795 + 6617581 * 2 ^ 59
def prefixEnd_6617581 : Nat := 4983230072969 + 3 ^ 40 * 6617581 * 2
def baseEnd_6617581 : Nat := 377555535895664268622645

theorem tailTrace_6617581 : CollatzResearch.WordTrace tailWord_6617581 prefixEnd_6617581 377555535895664268622645 := by
  unfold tailWord_6617581
  simp only [CollatzResearch.WordTrace]
  refine ⟨241363007838641704700660597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160908671892427803133773731 241363007838641704700660597)
  ·
    refine ⟨22627781984872659815686931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241363007838641704700660597 22627781984872659815686931)
    ·
      refine ⟨33941672977308989723530397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22627781984872659815686931 33941672977308989723530397)
      ·
        refine ⟨12728127366490871146323899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33941672977308989723530397 12728127366490871146323899)
        ·
          refine ⟨19092191049736306719485849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12728127366490871146323899 19092191049736306719485849)
          ·
            refine ⟨14319143287302230039614387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19092191049736306719485849 14319143287302230039614387)
            ·
              refine ⟨21478714930953345059421581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14319143287302230039614387 21478714930953345059421581)
              ·
                refine ⟨8054518099107504397283093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21478714930953345059421581 8054518099107504397283093)
                ·
                  refine ⟨377555535895664268622645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8054518099107504397283093 377555535895664268622645)
                  ·
                    rfl

theorem cell23_6617581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_6617581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617581 prefixEnd_6617581 := by exact prefixLift 6617581
  have htrace : WordTrace (prefixWord ++ tailWord_6617581) baseStart_6617581 baseEnd_6617581 := by
    simpa [prefixWord, tailWord_6617581, baseEnd_6617581] using wordTrace_append hprefix tailTrace_6617581
  have hstable : (prefixWord ++ tailWord_6617581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617581).length < 2 ^ (prefixWord ++ tailWord_6617581).sum := by decide
  have hdescent : baseEnd_6617581 < baseStart_6617581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617594 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_6617594 : Nat := 118140960795 + 6617594 * 2 ^ 59
def prefixEnd_6617594 : Nat := 4983230072969 + 3 ^ 40 * 6617594 * 2
def baseEnd_6617594 : Nat := 1132668832769828955580415

theorem tailTrace_6617594 : CollatzResearch.WordTrace tailWord_6617594 prefixEnd_6617594 1132668832769828955580415 := by
  unfold tailWord_6617594
  simp only [CollatzResearch.WordTrace]
  refine ⟨60340870496898651980220959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160908987991729738613922557 60340870496898651980220959)
  ·
    refine ⟨90511305745347977970331439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60340870496898651980220959 90511305745347977970331439)
    ·
      refine ⟨135766958618021966955497159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90511305745347977970331439 135766958618021966955497159)
      ·
        refine ⟨203650437927032950433245739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135766958618021966955497159 203650437927032950433245739)
        ·
          refine ⟨305475656890549425649868609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203650437927032950433245739 305475656890549425649868609)
          ·
            refine ⟨229106742667912069237401457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305475656890549425649868609 229106742667912069237401457)
            ·
              refine ⟨171830057000934051928051093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229106742667912069237401457 171830057000934051928051093)
              ·
                refine ⟨8054533921918783684127395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171830057000934051928051093 8054533921918783684127395)
                ·
                  refine ⟨12081800882878175526191093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8054533921918783684127395 12081800882878175526191093)
                  ·
                    refine ⟨1132668832769828955580415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12081800882878175526191093 1132668832769828955580415)
                    ·
                      rfl

theorem cell23_6617594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_6617594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617594 prefixEnd_6617594 := by exact prefixLift 6617594
  have htrace : WordTrace (prefixWord ++ tailWord_6617594) baseStart_6617594 baseEnd_6617594 := by
    simpa [prefixWord, tailWord_6617594, baseEnd_6617594] using wordTrace_append hprefix tailTrace_6617594
  have hstable : (prefixWord ++ tailWord_6617594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617594).length < 2 ^ (prefixWord ++ tailWord_6617594).sum := by decide
  have hdescent : baseEnd_6617594 < baseStart_6617594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617608 : List Nat := [2, 1, 3, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_6617608 : Nat := 118140960795 + 6617608 * 2 ^ 59
def prefixEnd_6617608 : Nat := 4983230072969 + 3 ^ 40 * 6617608 * 2
def baseEnd_6617608 : Nat := 3398013687038649811966181

theorem tailTrace_6617608 : CollatzResearch.WordTrace tailWord_6617608 prefixEnd_6617608 3398013687038649811966181 := by
  unfold tailWord_6617608
  simp only [CollatzResearch.WordTrace]
  refine ⟨120681996304771944155946739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160909328406362592207928985 120681996304771944155946739)
  ·
    refine ⟨181022994457157916233920109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120681996304771944155946739 181022994457157916233920109)
    ·
      refine ⟨67883622921434218587720041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181022994457157916233920109 67883622921434218587720041)
      ·
        refine ⟨50912717191075663940790031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67883622921434218587720041 50912717191075663940790031)
        ·
          refine ⟨76369075786613495911185047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50912717191075663940790031 76369075786613495911185047)
          ·
            refine ⟨114553613679920243866777571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76369075786613495911185047 114553613679920243866777571)
            ·
              refine ⟨171830420519880365800166357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114553613679920243866777571 171830420519880365800166357)
              ·
                refine ⟨4027275480934696073441399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 171830420519880365800166357 4027275480934696073441399)
                ·
                  refine ⟨6040913221402044110162099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027275480934696073441399 6040913221402044110162099)
                  ·
                    refine ⟨9061369832103066165243149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6040913221402044110162099 9061369832103066165243149)
                    ·
                      refine ⟨3398013687038649811966181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9061369832103066165243149 3398013687038649811966181)
                      ·
                        rfl

theorem cell23_6617608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_6617608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617608 prefixEnd_6617608 := by exact prefixLift 6617608
  have htrace : WordTrace (prefixWord ++ tailWord_6617608) baseStart_6617608 baseEnd_6617608 := by
    simpa [prefixWord, tailWord_6617608, baseEnd_6617608] using wordTrace_append hprefix tailTrace_6617608
  have hstable : (prefixWord ++ tailWord_6617608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617608).length < 2 ^ (prefixWord ++ tailWord_6617608).sum := by decide
  have hdescent : baseEnd_6617608 < baseStart_6617608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617634 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_6617634 : Nat := 118140960795 + 6617634 * 2 ^ 59
def prefixEnd_6617634 : Nat := 4983230072969 + 3 ^ 40 * 6617634 * 2
def baseEnd_6617634 : Nat := 3398027037535666710241061

theorem tailTrace_6617634 : CollatzResearch.WordTrace tailWord_6617634 prefixEnd_6617634 3398027037535666710241061 := by
  unfold tailWord_6617634
  simp only [CollatzResearch.WordTrace]
  refine ⟨60341235226862423688084989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160909960604966463168226637 60341235226862423688084989)
  ·
    refine ⟨22627963210073408883031871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60341235226862423688084989 22627963210073408883031871)
    ·
      refine ⟨33941944815110113324547807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22627963210073408883031871 33941944815110113324547807)
      ·
        refine ⟨50912917222665169986821711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33941944815110113324547807 50912917222665169986821711)
        ·
          refine ⟨76369375833997754980232567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50912917222665169986821711 76369375833997754980232567)
          ·
            refine ⟨114554063750996632470348851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76369375833997754980232567 114554063750996632470348851)
            ·
              refine ⟨171831095626494948705523277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114554063750996632470348851 171831095626494948705523277)
              ·
                refine ⟨64436660859935605764571229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171831095626494948705523277 64436660859935605764571229)
                ·
                  refine ⟨24163747822475852161714211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64436660859935605764571229 24163747822475852161714211)
                  ·
                    refine ⟨36245621733713778242571317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24163747822475852161714211 36245621733713778242571317)
                    ·
                      refine ⟨3398027037535666710241061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36245621733713778242571317 3398027037535666710241061)
                      ·
                        rfl

theorem cell23_6617634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_6617634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617634 prefixEnd_6617634 := by exact prefixLift 6617634
  have htrace : WordTrace (prefixWord ++ tailWord_6617634) baseStart_6617634 baseEnd_6617634 := by
    simpa [prefixWord, tailWord_6617634, baseEnd_6617634] using wordTrace_append hprefix tailTrace_6617634
  have hstable : (prefixWord ++ tailWord_6617634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617634).length < 2 ^ (prefixWord ++ tailWord_6617634).sum := by decide
  have hdescent : baseEnd_6617634 < baseStart_6617634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617647 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_6617647 : Nat := 118140960795 + 6617647 * 2 ^ 59
def prefixEnd_6617647 : Nat := 4983230072969 + 3 ^ 40 * 6617647 * 2
def baseEnd_6617647 : Nat := 3398033712784175159378501

theorem tailTrace_6617647 : CollatzResearch.WordTrace tailWord_6617647 prefixEnd_6617647 3398033712784175159378501 := by
  unfold tailWord_6617647
  simp only [CollatzResearch.WordTrace]
  refine ⟨241365415056402597972563195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160910276704268398648375463 241365415056402597972563195)
  ·
    refine ⟨362048122584603896958844793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241365415056402597972563195 362048122584603896958844793)
    ·
      refine ⟨271536091938452922719133595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362048122584603896958844793 271536091938452922719133595)
      ·
        refine ⟨407304137907679384078700393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271536091938452922719133595 407304137907679384078700393)
        ·
          refine ⟨305478103430759538059025295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407304137907679384078700393 305478103430759538059025295)
          ·
            refine ⟨458217155146139307088537943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305478103430759538059025295 458217155146139307088537943)
            ·
              refine ⟨687325732719208960632806915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458217155146139307088537943 687325732719208960632806915)
              ·
                refine ⟨1030988599078813440949210373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687325732719208960632806915 1030988599078813440949210373)
                ·
                  refine ⟨193310362327277520177976945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1030988599078813440949210373 193310362327277520177976945)
                  ·
                    refine ⟨144982771745458140133482709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193310362327277520177976945 144982771745458140133482709)
                    ·
                      refine ⟨3398033712784175159378501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144982771745458140133482709 3398033712784175159378501)
                      ·
                        rfl

theorem cell23_6617647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_6617647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617647 prefixEnd_6617647 := by exact prefixLift 6617647
  have htrace : WordTrace (prefixWord ++ tailWord_6617647) baseStart_6617647 baseEnd_6617647 := by
    simpa [prefixWord, tailWord_6617647, baseEnd_6617647] using wordTrace_append hprefix tailTrace_6617647
  have hstable : (prefixWord ++ tailWord_6617647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617647).length < 2 ^ (prefixWord ++ tailWord_6617647).sum := by decide
  have hdescent : baseEnd_6617647 < baseStart_6617647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617651 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 3]
def baseStart_6617651 : Nat := 118140960795 + 6617651 * 2 ^ 59
def prefixEnd_6617651 : Nat := 4983230072969 + 3 ^ 40 * 6617651 * 2
def baseEnd_6617651 : Nat := 3398035766706793143728483

theorem tailTrace_6617651 : CollatzResearch.WordTrace tailWord_6617651 prefixEnd_6617651 3398035766706793143728483 := by
  unfold tailWord_6617651
  simp only [CollatzResearch.WordTrace]
  refine ⟨241365560948388106655708807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160910373965592071103805871 241365560948388106655708807)
  ·
    refine ⟨362048341422582159983563211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241365560948388106655708807 362048341422582159983563211)
    ·
      refine ⟨543072512133873239975344817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362048341422582159983563211 543072512133873239975344817)
      ·
        refine ⟨407304384100404929981508613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543072512133873239975344817 407304384100404929981508613)
        ·
          refine ⟨76369572018825924371532865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407304384100404929981508613 76369572018825924371532865)
          ·
            refine ⟨57277179014119443278649649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76369572018825924371532865 57277179014119443278649649)
            ·
              refine ⟨42957884260589582458987237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57277179014119443278649649 42957884260589582458987237)
              ·
                refine ⟨8054603298860546711060107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42957884260589582458987237 8054603298860546711060107)
                ·
                  refine ⟨12081904948290820066590161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8054603298860546711060107 12081904948290820066590161)
                  ·
                    refine ⟨9061428711218115049942621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12081904948290820066590161 9061428711218115049942621)
                    ·
                      refine ⟨3398035766706793143728483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9061428711218115049942621 3398035766706793143728483)
                      ·
                        rfl

theorem cell23_6617651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 3].length) (baseStart_6617651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617651 prefixEnd_6617651 := by exact prefixLift 6617651
  have htrace : WordTrace (prefixWord ++ tailWord_6617651) baseStart_6617651 baseEnd_6617651 := by
    simpa [prefixWord, tailWord_6617651, baseEnd_6617651] using wordTrace_append hprefix tailTrace_6617651
  have hstable : (prefixWord ++ tailWord_6617651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617651).length < 2 ^ (prefixWord ++ tailWord_6617651).sum := by decide
  have hdescent : baseEnd_6617651 < baseStart_6617651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617661 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6617661 : Nat := 118140960795 + 6617661 * 2 ^ 59
def prefixEnd_6617661 : Nat := 4983230072969 + 3 ^ 40 * 6617661 * 2
def baseEnd_6617661 : Nat := 3398040901513338104603437

theorem tailTrace_6617661 : CollatzResearch.WordTrace tailWord_6617661 prefixEnd_6617661 3398040901513338104603437 := by
  unfold tailWord_6617661
  simp only [CollatzResearch.WordTrace]
  refine ⟨241365925678351878363572837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160910617118901252242381891 241365925678351878363572837)
  ·
    refine ⟨45256111064690977193169907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241365925678351878363572837 45256111064690977193169907)
    ·
      refine ⟨67884166597036465789754861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45256111064690977193169907 67884166597036465789754861)
      ·
        refine ⟨25456562473888674671158073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67884166597036465789754861 25456562473888674671158073)
        ·
          refine ⟨19092421855416506003368555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25456562473888674671158073 19092421855416506003368555)
          ·
            refine ⟨28638632783124759005052833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19092421855416506003368555 28638632783124759005052833)
            ·
              refine ⟨21478974587343569253789625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28638632783124759005052833 21478974587343569253789625)
              ·
                refine ⟨16109230940507676940342219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21478974587343569253789625 16109230940507676940342219)
                ·
                  refine ⟨24163846410761515410513329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16109230940507676940342219 24163846410761515410513329)
                  ·
                    refine ⟨18122884808071136557884997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24163846410761515410513329 18122884808071136557884997)
                    ·
                      refine ⟨3398040901513338104603437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18122884808071136557884997 3398040901513338104603437)
                      ·
                        rfl

theorem cell23_6617661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6617661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617661 prefixEnd_6617661 := by exact prefixLift 6617661
  have htrace : WordTrace (prefixWord ++ tailWord_6617661) baseStart_6617661 baseEnd_6617661 := by
    simpa [prefixWord, tailWord_6617661, baseEnd_6617661] using wordTrace_append hprefix tailTrace_6617661
  have hstable : (prefixWord ++ tailWord_6617661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617661).length < 2 ^ (prefixWord ++ tailWord_6617661).sum := by decide
  have hdescent : baseEnd_6617661 < baseStart_6617661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617662 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_6617662 : Nat := 118140960795 + 6617662 * 2 ^ 59
def prefixEnd_6617662 : Nat := 4983230072969 + 3 ^ 40 * 6617662 * 2
def baseEnd_6617662 : Nat := 1132680471664664200230311

theorem tailTrace_6617662 : CollatzResearch.WordTrace tailWord_6617662 prefixEnd_6617662 1132680471664664200230311 := by
  unfold tailWord_6617662
  simp only [CollatzResearch.WordTrace]
  refine ⟨30170745268918531941794905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160910641434232170356239493 30170745268918531941794905)
  ·
    refine ⟨22628058951688898956346179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30170745268918531941794905 22628058951688898956346179)
    ·
      refine ⟨33942088427533348434519269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22628058951688898956346179 33942088427533348434519269)
      ·
        refine ⟨6364141580162502831472363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33942088427533348434519269 6364141580162502831472363)
        ·
          refine ⟨9546212370243754247208545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364141580162502831472363 9546212370243754247208545)
          ·
            refine ⟨7159659277682815685406409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9546212370243754247208545 7159659277682815685406409)
            ·
              refine ⟨5369744458262111764054807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7159659277682815685406409 5369744458262111764054807)
              ·
                refine ⟨8054616687393167646082211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369744458262111764054807 8054616687393167646082211)
                ·
                  refine ⟨12081925031089751469123317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8054616687393167646082211 12081925031089751469123317)
                  ·
                    refine ⟨1132680471664664200230311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12081925031089751469123317 1132680471664664200230311)
                    ·
                      rfl

theorem cell23_6617662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_6617662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617662 prefixEnd_6617662 := by exact prefixLift 6617662
  have htrace : WordTrace (prefixWord ++ tailWord_6617662) baseStart_6617662 baseEnd_6617662 := by
    simpa [prefixWord, tailWord_6617662, baseEnd_6617662] using wordTrace_append hprefix tailTrace_6617662
  have hstable : (prefixWord ++ tailWord_6617662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617662).length < 2 ^ (prefixWord ++ tailWord_6617662).sum := by decide
  have hdescent : baseEnd_6617662 < baseStart_6617662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617665 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_6617665 : Nat := 118140960795 + 6617665 * 2 ^ 59
def prefixEnd_6617665 : Nat := 4983230072969 + 3 ^ 40 * 6617665 * 2
def baseEnd_6617665 : Nat := 3398042955435956088953419

theorem tailTrace_6617665 : CollatzResearch.WordTrace tailWord_6617665 prefixEnd_6617665 3398042955435956088953419 := by
  unfold tailWord_6617665
  simp only [CollatzResearch.WordTrace]
  refine ⟨241366071570337387046718449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160910714380224924697812299 241366071570337387046718449)
  ·
    refine ⟨181024553677753040285038837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241366071570337387046718449 181024553677753040285038837)
    ·
      refine ⟨16971051907289347526722391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181024553677753040285038837 16971051907289347526722391)
      ·
        refine ⟨25456577860934021290083587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16971051907289347526722391 25456577860934021290083587)
        ·
          refine ⟨38184866791401031935125381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25456577860934021290083587 38184866791401031935125381)
          ·
            refine ⟨7159662523387693487836009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38184866791401031935125381 7159662523387693487836009)
            ·
              refine ⟨5369746892540770115877007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7159662523387693487836009 5369746892540770115877007)
              ·
                refine ⟨8054620338811155173815511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369746892540770115877007 8054620338811155173815511)
                ·
                  refine ⟨12081930508216732760723267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8054620338811155173815511 12081930508216732760723267)
                  ·
                    refine ⟨18122895762325099141084901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12081930508216732760723267 18122895762325099141084901)
                    ·
                      refine ⟨3398042955435956088953419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18122895762325099141084901 3398042955435956088953419)
                      ·
                        rfl

theorem cell23_6617665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_6617665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617665 prefixEnd_6617665 := by exact prefixLift 6617665
  have htrace : WordTrace (prefixWord ++ tailWord_6617665) baseStart_6617665 baseEnd_6617665 := by
    simpa [prefixWord, tailWord_6617665, baseEnd_6617665] using wordTrace_append hprefix tailTrace_6617665
  have hstable : (prefixWord ++ tailWord_6617665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617665).length < 2 ^ (prefixWord ++ tailWord_6617665).sum := by decide
  have hdescent : baseEnd_6617665 < baseStart_6617665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617708 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 1, 3, 2]
def baseStart_6617708 : Nat := 118140960795 + 6617708 * 2 ^ 59
def prefixEnd_6617708 : Nat := 4983230072969 + 3 ^ 40 * 6617708 * 2
def baseEnd_6617708 : Nat := 3398065035104099420715721

theorem tailTrace_6617708 : CollatzResearch.WordTrace tailWord_6617708 prefixEnd_6617708 3398065035104099420715721 := by
  unfold tailWord_6617708
  simp only [CollatzResearch.WordTrace]
  refine ⟨120683819954590802695266889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160911759939454403593689185 120683819954590802695266889)
  ·
    refine ⟨90512864965943102021450167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120683819954590802695266889 90512864965943102021450167)
    ·
      refine ⟨135769297448914653032175251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90512864965943102021450167 135769297448914653032175251)
      ·
        refine ⟨203653946173371979548262877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135769297448914653032175251 203653946173371979548262877)
        ·
          refine ⟨76370229815014492330598579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203653946173371979548262877 76370229815014492330598579)
          ·
            refine ⟨114555344722521738495897869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76370229815014492330598579 114555344722521738495897869)
            ·
              refine ⟨42958254270945651935961701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114555344722521738495897869 42958254270945651935961701)
              ·
                refine ⟨8054672675802309737992819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42958254270945651935961701 8054672675802309737992819)
                ·
                  refine ⟨12082009013703464606989229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8054672675802309737992819 12082009013703464606989229)
                  ·
                    refine ⟨4530753380138799227620961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12082009013703464606989229 4530753380138799227620961)
                    ·
                      refine ⟨3398065035104099420715721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530753380138799227620961 3398065035104099420715721)
                      ·
                        rfl

theorem cell23_6617708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_6617708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617708 prefixEnd_6617708 := by exact prefixLift 6617708
  have htrace : WordTrace (prefixWord ++ tailWord_6617708) baseStart_6617708 baseEnd_6617708 := by
    simpa [prefixWord, tailWord_6617708, baseEnd_6617708] using wordTrace_append hprefix tailTrace_6617708
  have hstable : (prefixWord ++ tailWord_6617708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617708).length < 2 ^ (prefixWord ++ tailWord_6617708).sum := by decide
  have hdescent : baseEnd_6617708 < baseStart_6617708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617724 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_6617724 : Nat := 118140960795 + 6617724 * 2 ^ 59
def prefixEnd_6617724 : Nat := 4983230072969 + 3 ^ 40 * 6617724 * 2
def baseEnd_6617724 : Nat := 3398073250794571358115647

theorem tailTrace_6617724 : CollatzResearch.WordTrace tailWord_6617724 prefixEnd_6617724 3398073250794571358115647 := by
  unfold tailWord_6617724
  simp only [CollatzResearch.WordTrace]
  refine ⟨120684111738561820061558113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160912148984749093415410817 120684111738561820061558113)
  ·
    refine ⟨90513083803921365046168585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120684111738561820061558113 90513083803921365046168585)
    ·
      refine ⟨67884812852941023784626439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90513083803921365046168585 67884812852941023784626439)
      ·
        refine ⟨101827219279411535676939659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67884812852941023784626439 101827219279411535676939659)
        ·
          refine ⟨152740828919117303515409489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101827219279411535676939659 152740828919117303515409489)
          ·
            refine ⟨114555621689337977636557117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152740828919117303515409489 114555621689337977636557117)
            ·
              refine ⟨42958358133501741613708919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114555621689337977636557117 42958358133501741613708919)
              ·
                refine ⟨64437537200252612420563379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42958358133501741613708919 64437537200252612420563379)
                ·
                  refine ⟨96656305800378918630845069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64437537200252612420563379 96656305800378918630845069)
                  ·
                    refine ⟨36246114675142094486566901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96656305800378918630845069 36246114675142094486566901)
                    ·
                      refine ⟨3398073250794571358115647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36246114675142094486566901 3398073250794571358115647)
                      ·
                        rfl

theorem cell23_6617724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_6617724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617724 prefixEnd_6617724 := by exact prefixLift 6617724
  have htrace : WordTrace (prefixWord ++ tailWord_6617724) baseStart_6617724 baseEnd_6617724 := by
    simpa [prefixWord, tailWord_6617724, baseEnd_6617724] using wordTrace_append hprefix tailTrace_6617724
  have hstable : (prefixWord ++ tailWord_6617724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617724).length < 2 ^ (prefixWord ++ tailWord_6617724).sum := by decide
  have hdescent : baseEnd_6617724 < baseStart_6617724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617791 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 2, 5]
def baseStart_6617791 : Nat := 118140960795 + 6617791 * 2 ^ 59
def prefixEnd_6617791 : Nat := 4983230072969 + 3 ^ 40 * 6617791 * 2
def baseEnd_6617791 : Nat := 1132702551332807531992613

theorem tailTrace_6617791 : CollatzResearch.WordTrace tailWord_6617791 prefixEnd_6617791 1132702551332807531992613 := by
  unfold tailWord_6617791
  simp only [CollatzResearch.WordTrace]
  refine ⟨241370667167880910565805227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160913778111920607043870151 241370667167880910565805227)
  ·
    refine ⟨362056000751821365848707841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241370667167880910565805227 362056000751821365848707841)
    ·
      refine ⟨271542000563866024386530881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362056000751821365848707841 271542000563866024386530881)
      ·
        refine ⟨203656500422899518289898161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271542000563866024386530881 203656500422899518289898161)
        ·
          refine ⟨152742375317174638717423621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203656500422899518289898161 152742375317174638717423621)
          ·
            refine ⟨28639195371970244759516929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152742375317174638717423621 28639195371970244759516929)
            ·
              refine ⟨21479396528977683569637697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28639195371970244759516929 21479396528977683569637697)
              ·
                refine ⟨16109547396733262677228273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21479396528977683569637697 16109547396733262677228273)
                ·
                  refine ⟨12082160547549947007921205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16109547396733262677228273 12082160547549947007921205)
                  ·
                    refine ⟨1132702551332807531992613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12082160547549947007921205 1132702551332807531992613)
                    ·
                      rfl

theorem cell23_6617791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_6617791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617791 prefixEnd_6617791 := by exact prefixLift 6617791
  have htrace : WordTrace (prefixWord ++ tailWord_6617791) baseStart_6617791 baseEnd_6617791 := by
    simpa [prefixWord, tailWord_6617791, baseEnd_6617791] using wordTrace_append hprefix tailTrace_6617791
  have hstable : (prefixWord ++ tailWord_6617791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617791).length < 2 ^ (prefixWord ++ tailWord_6617791).sum := by decide
  have hdescent : baseEnd_6617791 < baseStart_6617791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617828 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_6617828 : Nat := 118140960795 + 6617828 * 2 ^ 59
def prefixEnd_6617828 : Nat := 4983230072969 + 3 ^ 40 * 6617828 * 2
def baseEnd_6617828 : Nat := 3398126652782638951215169

theorem tailTrace_6617828 : CollatzResearch.WordTrace tailWord_6617828 prefixEnd_6617828 3398126652782638951215169 := by
  unfold tailWord_6617828
  simp only [CollatzResearch.WordTrace]
  refine ⟨120686008334373432942451069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160914677779164577256601425 120686008334373432942451069)
  ·
    refine ⟨45257253125390037353419151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120686008334373432942451069 45257253125390037353419151)
    ·
      refine ⟨67885879688085056030128727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45257253125390037353419151 67885879688085056030128727)
      ·
        refine ⟨101828819532127584045193091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67885879688085056030128727 101828819532127584045193091)
        ·
          refine ⟨152743229298191376067789637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101828819532127584045193091 152743229298191376067789637)
          ·
            refine ⟨28639355493410883012710557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152743229298191376067789637 28639355493410883012710557)
            ·
              refine ⟨10739758310029081129766459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28639355493410883012710557 10739758310029081129766459)
              ·
                refine ⟨16109637465043621694649689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10739758310029081129766459 16109637465043621694649689)
                ·
                  refine ⟨12082228098782716270987267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16109637465043621694649689 12082228098782716270987267)
                  ·
                    refine ⟨18123342148174074406480901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12082228098782716270987267 18123342148174074406480901)
                    ·
                      refine ⟨3398126652782638951215169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18123342148174074406480901 3398126652782638951215169)
                      ·
                        rfl

theorem cell23_6617828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_6617828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617828 prefixEnd_6617828 := by exact prefixLift 6617828
  have htrace : WordTrace (prefixWord ++ tailWord_6617828) baseStart_6617828 baseEnd_6617828 := by
    simpa [prefixWord, tailWord_6617828, baseEnd_6617828] using wordTrace_append hprefix tailTrace_6617828
  have hstable : (prefixWord ++ tailWord_6617828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617828).length < 2 ^ (prefixWord ++ tailWord_6617828).sum := by decide
  have hdescent : baseEnd_6617828 < baseStart_6617828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617905 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 2, 3, 2]
def baseStart_6617905 : Nat := 118140960795 + 6617905 * 2 ^ 59
def prefixEnd_6617905 : Nat := 4983230072969 + 3 ^ 40 * 6617905 * 2
def baseEnd_6617905 : Nat := 3398166190793035149952315

theorem tailTrace_6617905 : CollatzResearch.WordTrace tailWord_6617905 prefixEnd_6617905 3398166190793035149952315 := by
  unfold tailWord_6617905
  simp only [CollatzResearch.WordTrace]
  refine ⟨241374825089467908035455169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160916550059645272023636779 241374825089467908035455169)
  ·
    refine ⟨181031118817100931026591377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241374825089467908035455169 181031118817100931026591377)
    ·
      refine ⟨135773339112825698269943533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181031118817100931026591377 135773339112825698269943533)
      ·
        refine ⟨50915002167309636851228825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135773339112825698269943533 50915002167309636851228825)
        ·
          refine ⟨38186251625482227638421619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50915002167309636851228825 38186251625482227638421619)
          ·
            refine ⟨57279377438223341457632429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38186251625482227638421619 57279377438223341457632429)
            ·
              refine ⟨21479766539333753046612161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57279377438223341457632429 21479766539333753046612161)
              ·
                refine ⟨16109824904500314784959121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21479766539333753046612161 16109824904500314784959121)
                ·
                  refine ⟨12082368678375236088719341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16109824904500314784959121 12082368678375236088719341)
                  ·
                    refine ⟨4530888254390713533269753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12082368678375236088719341 4530888254390713533269753)
                    ·
                      refine ⟨3398166190793035149952315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530888254390713533269753 3398166190793035149952315)
                      ·
                        rfl

theorem cell23_6617905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_6617905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617905 prefixEnd_6617905 := by exact prefixLift 6617905
  have htrace : WordTrace (prefixWord ++ tailWord_6617905) baseStart_6617905 baseEnd_6617905 := by
    simpa [prefixWord, tailWord_6617905, baseEnd_6617905] using wordTrace_append hprefix tailTrace_6617905
  have hstable : (prefixWord ++ tailWord_6617905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617905).length < 2 ^ (prefixWord ++ tailWord_6617905).sum := by decide
  have hdescent : baseEnd_6617905 < baseStart_6617905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617931 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 4]
def baseStart_6617931 : Nat := 118140960795 + 6617931 * 2 ^ 59
def prefixEnd_6617931 : Nat := 4983230072969 + 3 ^ 40 * 6617931 * 2
def baseEnd_6617931 : Nat := 3398179541290052048227195

theorem tailTrace_6617931 : CollatzResearch.WordTrace tailWord_6617931 prefixEnd_6617931 3398179541290052048227195 := by
  unfold tailWord_6617931
  simp only [CollatzResearch.WordTrace]
  refine ⟨241375773387373714475901647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160917182258249142983934431 241375773387373714475901647)
  ·
    refine ⟨362063660081060571713852471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241375773387373714475901647 362063660081060571713852471)
    ·
      refine ⟨543095490121590857570778707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362063660081060571713852471 543095490121590857570778707)
      ·
        refine ⟨814643235182386286356168061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543095490121590857570778707 814643235182386286356168061)
        ·
          refine ⟨305491213193394857383563023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814643235182386286356168061 305491213193394857383563023)
          ·
            refine ⟨458236819790092286075344535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305491213193394857383563023 458236819790092286075344535)
            ·
              refine ⟨687355229685138429113016803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458236819790092286075344535 687355229685138429113016803)
              ·
                refine ⟨1031032844527707643669525205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687355229685138429113016803 1031032844527707643669525205)
                ·
                  refine ⟨24164832293618147898504497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1031032844527707643669525205 24164832293618147898504497)
                  ·
                    refine ⟨18123624220213610923878373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24164832293618147898504497 18123624220213610923878373)
                    ·
                      refine ⟨3398179541290052048227195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18123624220213610923878373 3398179541290052048227195)
                      ·
                        rfl

theorem cell23_6617931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 4].length) (baseStart_6617931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617931 prefixEnd_6617931 := by exact prefixLift 6617931
  have htrace : WordTrace (prefixWord ++ tailWord_6617931) baseStart_6617931 baseEnd_6617931 := by
    simpa [prefixWord, tailWord_6617931, baseEnd_6617931] using wordTrace_append hprefix tailTrace_6617931
  have hstable : (prefixWord ++ tailWord_6617931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617931).length < 2 ^ (prefixWord ++ tailWord_6617931).sum := by decide
  have hdescent : baseEnd_6617931 < baseStart_6617931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617941 : List Nat := [1, 3, 2, 2, 2, 1, 1, 11]
def baseStart_6617941 : Nat := 118140960795 + 6617941 * 2 ^ 59
def prefixEnd_6617941 : Nat := 4983230072969 + 3 ^ 40 * 6617941 * 2
def baseEnd_6617941 : Nat := 125858691707281370707487

theorem tailTrace_6617941 : CollatzResearch.WordTrace tailWord_6617941 prefixEnd_6617941 125858691707281370707487 := by
  unfold tailWord_6617941
  simp only [CollatzResearch.WordTrace]
  refine ⟨241376138117337486183765677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160917425411558324122510451 241376138117337486183765677)
  ·
    refine ⟨90516051794001557318912129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241376138117337486183765677 90516051794001557318912129)
    ·
      refine ⟨67887038845501167989184097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90516051794001557318912129 67887038845501167989184097)
      ·
        refine ⟨50915279134125875991888073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67887038845501167989184097 50915279134125875991888073)
        ·
          refine ⟨38186459350594406993916055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50915279134125875991888073 38186459350594406993916055)
          ·
            refine ⟨57279689025891610490874083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38186459350594406993916055 57279689025891610490874083)
            ·
              refine ⟨85919533538837415736311125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57279689025891610490874083 85919533538837415736311125)
              ·
                refine ⟨125858691707281370707487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 85919533538837415736311125 125858691707281370707487)
                ·
                  rfl

theorem cell23_6617941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 11].length) (baseStart_6617941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617941 prefixEnd_6617941 := by exact prefixLift 6617941
  have htrace : WordTrace (prefixWord ++ tailWord_6617941) baseStart_6617941 baseEnd_6617941 := by
    simpa [prefixWord, tailWord_6617941, baseEnd_6617941] using wordTrace_append hprefix tailTrace_6617941
  have hstable : (prefixWord ++ tailWord_6617941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617941).length < 2 ^ (prefixWord ++ tailWord_6617941).sum := by decide
  have hdescent : baseEnd_6617941 < baseStart_6617941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617955 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 5]
def baseStart_6617955 : Nat := 118140960795 + 6617955 * 2 ^ 59
def prefixEnd_6617955 : Nat := 4983230072969 + 3 ^ 40 * 6617955 * 2
def baseEnd_6617955 : Nat := 3398191864825759954327085

theorem tailTrace_6617955 : CollatzResearch.WordTrace tailWord_6617955 prefixEnd_6617955 3398191864825759954327085 := by
  unfold tailWord_6617955
  simp only [CollatzResearch.WordTrace]
  refine ⟨241376648739286766574775319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160917765826191177716516879 241376648739286766574775319)
  ·
    refine ⟨362064973108930149862162979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241376648739286766574775319 362064973108930149862162979)
    ·
      refine ⟨543097459663395224793244469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362064973108930149862162979 543097459663395224793244469)
      ·
        refine ⟨50915386843443302324366669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 543097459663395224793244469 50915386843443302324366669)
        ·
          refine ⟨19093270066291238371637501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50915386843443302324366669 19093270066291238371637501)
          ·
            refine ⟨7159976274859214389364063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19093270066291238371637501 7159976274859214389364063)
            ·
              refine ⟨10739964412288821584046095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7159976274859214389364063 10739964412288821584046095)
              ·
                refine ⟨16109946618433232376069143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10739964412288821584046095 16109946618433232376069143)
                ·
                  refine ⟨24164919927649848564103715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16109946618433232376069143 24164919927649848564103715)
                  ·
                    refine ⟨36247379891474772846155573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24164919927649848564103715 36247379891474772846155573)
                    ·
                      refine ⟨3398191864825759954327085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36247379891474772846155573 3398191864825759954327085)
                      ·
                        rfl

theorem cell23_6617955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_6617955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617955 prefixEnd_6617955 := by exact prefixLift 6617955
  have htrace : WordTrace (prefixWord ++ tailWord_6617955) baseStart_6617955 baseEnd_6617955 := by
    simpa [prefixWord, tailWord_6617955, baseEnd_6617955] using wordTrace_append hprefix tailTrace_6617955
  have hstable : (prefixWord ++ tailWord_6617955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617955).length < 2 ^ (prefixWord ++ tailWord_6617955).sum := by decide
  have hdescent : baseEnd_6617955 < baseStart_6617955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617969 : List Nat := [1, 2, 2, 2, 1, 5, 1, 4, 1, 2, 2]
def baseStart_6617969 : Nat := 118140960795 + 6617969 * 2 ^ 59
def prefixEnd_6617969 : Nat := 4983230072969 + 3 ^ 40 * 6617969 * 2
def baseEnd_6617969 : Nat := 3398199053554922899552021

theorem tailTrace_6617969 : CollatzResearch.WordTrace tailWord_6617969 prefixEnd_6617969 3398199053554922899552021 := by
  unfold tailWord_6617969
  simp only [CollatzResearch.WordTrace]
  refine ⟨241377159361236046965784961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160918106240824031310523307 241377159361236046965784961)
  ·
    refine ⟨181032869520927035224338721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241377159361236046965784961 181032869520927035224338721)
    ·
      refine ⟨135774652140695276418254041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181032869520927035224338721 135774652140695276418254041)
      ·
        refine ⟨101830989105521457313690531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135774652140695276418254041 101830989105521457313690531)
        ·
          refine ⟨152746483658282185970535797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101830989105521457313690531 152746483658282185970535797)
          ·
            refine ⟨14319982842963954934737731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152746483658282185970535797 14319982842963954934737731)
            ·
              refine ⟨21479974264445932402106597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14319982842963954934737731 21479974264445932402106597)
              ·
                refine ⟨4027495174583612325394987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21479974264445932402106597 4027495174583612325394987)
                ·
                  refine ⟨6041242761875418488092481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027495174583612325394987 6041242761875418488092481)
                  ·
                    refine ⟨4530932071406563866069361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6041242761875418488092481 4530932071406563866069361)
                    ·
                      refine ⟨3398199053554922899552021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530932071406563866069361 3398199053554922899552021)
                      ·
                        rfl

theorem cell23_6617969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_6617969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617969 prefixEnd_6617969 := by exact prefixLift 6617969
  have htrace : WordTrace (prefixWord ++ tailWord_6617969) baseStart_6617969 baseEnd_6617969 := by
    simpa [prefixWord, tailWord_6617969, baseEnd_6617969] using wordTrace_append hprefix tailTrace_6617969
  have hstable : (prefixWord ++ tailWord_6617969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617969).length < 2 ^ (prefixWord ++ tailWord_6617969).sum := by decide
  have hdescent : baseEnd_6617969 < baseStart_6617969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617971 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 2, 7]
def baseStart_6617971 : Nat := 118140960795 + 6617971 * 2 ^ 59
def prefixEnd_6617971 : Nat := 4983230072969 + 3 ^ 40 * 6617971 * 2
def baseEnd_6617971 : Nat := 1132733360172077297242337

theorem tailTrace_6617971 : CollatzResearch.WordTrace tailWord_6617971 prefixEnd_6617971 1132733360172077297242337 := by
  unfold tailWord_6617971
  simp only [CollatzResearch.WordTrace]
  refine ⟨241377232307228801307357767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160918154871485867538238511 241377232307228801307357767)
  ·
    refine ⟨362065848460843201961036651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241377232307228801307357767 362065848460843201961036651)
    ·
      refine ⟨543098772691264802941554977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362065848460843201961036651 543098772691264802941554977)
      ·
        refine ⟨407324079518448602206166233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543098772691264802941554977 407324079518448602206166233)
        ·
          refine ⟨305493059638836451654624675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407324079518448602206166233 305493059638836451654624675)
          ·
            refine ⟨458239589458254677481937013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305493059638836451654624675 458239589458254677481937013)
            ·
              refine ⟨42959961511711376013931595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458239589458254677481937013 42959961511711376013931595)
              ·
                refine ⟨64439942267567064020897393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42959961511711376013931595 64439942267567064020897393)
                ·
                  refine ⟨48329956700675298015673045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64439942267567064020897393 48329956700675298015673045)
                  ·
                    refine ⟨1132733360172077297242337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48329956700675298015673045 1132733360172077297242337)
                    ·
                      rfl

theorem cell23_6617971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 7].length) (baseStart_6617971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617971 prefixEnd_6617971 := by exact prefixLift 6617971
  have htrace : WordTrace (prefixWord ++ tailWord_6617971) baseStart_6617971 baseEnd_6617971 := by
    simpa [prefixWord, tailWord_6617971, baseEnd_6617971] using wordTrace_append hprefix tailTrace_6617971
  have hstable : (prefixWord ++ tailWord_6617971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617971).length < 2 ^ (prefixWord ++ tailWord_6617971).sum := by decide
  have hdescent : baseEnd_6617971 < baseStart_6617971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6617995 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 3, 3, 2]
def baseStart_6617995 : Nat := 118140960795 + 6617995 * 2 ^ 59
def prefixEnd_6617995 : Nat := 4983230072969 + 3 ^ 40 * 6617995 * 2
def baseEnd_6617995 : Nat := 3398212404051939797826901

theorem tailTrace_6617995 : CollatzResearch.WordTrace tailWord_6617995 prefixEnd_6617995 3398212404051939797826901 := by
  unfold tailWord_6617995
  simp only [CollatzResearch.WordTrace]
  refine ⟨241378107659141853406231439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160918738439427902270820959 241378107659141853406231439)
  ·
    refine ⟨362067161488712780109347159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241378107659141853406231439 362067161488712780109347159)
    ·
      refine ⟨543100742233069170164020739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362067161488712780109347159 543100742233069170164020739)
      ·
        refine ⟨814651113349603755246031109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543100742233069170164020739 814651113349603755246031109)
        ·
          refine ⟨152747083753050704108630833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 814651113349603755246031109 152747083753050704108630833)
          ·
            refine ⟨114560312814788028081473125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152747083753050704108630833 114560312814788028081473125)
            ·
              refine ⟨21480058652772755265276211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114560312814788028081473125 21480058652772755265276211)
              ·
                refine ⟨32220087979159132897914317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21480058652772755265276211 32220087979159132897914317)
                ·
                  refine ⟨12082532992184674836717869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32220087979159132897914317 12082532992184674836717869)
                  ·
                    refine ⟨4530949872069253063769201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12082532992184674836717869 4530949872069253063769201)
                    ·
                      refine ⟨3398212404051939797826901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530949872069253063769201 3398212404051939797826901)
                      ·
                        rfl

theorem cell23_6617995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 3, 2].length) (baseStart_6617995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6617995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6617995 prefixEnd_6617995 := by exact prefixLift 6617995
  have htrace : WordTrace (prefixWord ++ tailWord_6617995) baseStart_6617995 baseEnd_6617995 := by
    simpa [prefixWord, tailWord_6617995, baseEnd_6617995] using wordTrace_append hprefix tailTrace_6617995
  have hstable : (prefixWord ++ tailWord_6617995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6617995).length < 2 ^ (prefixWord ++ tailWord_6617995).sum := by decide
  have hdescent : baseEnd_6617995 < baseStart_6617995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6617995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618001 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 3, 8]
def baseStart_6618001 : Nat := 118140960795 + 6618001 * 2 ^ 59
def prefixEnd_6618001 : Nat := 4983230072969 + 3 ^ 40 * 6618001 * 2
def baseEnd_6618001 : Nat := 1132738494978622258117291

theorem tailTrace_6618001 : CollatzResearch.WordTrace tailWord_6618001 prefixEnd_6618001 1132738494978622258117291 := by
  unfold tailWord_6618001
  simp only [CollatzResearch.WordTrace]
  refine ⟨241378326497120116430949857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160918884331413410953966571 241378326497120116430949857)
  ·
    refine ⟨181033744872840087323212393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241378326497120116430949857 181033744872840087323212393)
    ·
      refine ⟨135775308654630065492409295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181033744872840087323212393 135775308654630065492409295)
      ·
        refine ⟨203662962981945098238613943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135775308654630065492409295 203662962981945098238613943)
        ·
          refine ⟨305494444472917647357920915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203662962981945098238613943 305494444472917647357920915)
          ·
            refine ⟨458241666709376471036881373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305494444472917647357920915 458241666709376471036881373)
            ·
              refine ⟨171840625016016176638830515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458241666709376471036881373 171840625016016176638830515)
              ·
                refine ⟨257760937524024264958245773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171840625016016176638830515 257760937524024264958245773)
                ·
                  refine ⟨96660351571509099359342165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257760937524024264958245773 96660351571509099359342165)
                  ·
                    refine ⟨1132738494978622258117291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96660351571509099359342165 1132738494978622258117291)
                    ·
                      rfl

theorem cell23_6618001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_6618001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618001 prefixEnd_6618001 := by exact prefixLift 6618001
  have htrace : WordTrace (prefixWord ++ tailWord_6618001) baseStart_6618001 baseEnd_6618001 := by
    simpa [prefixWord, tailWord_6618001, baseEnd_6618001] using wordTrace_append hprefix tailTrace_6618001
  have hstable : (prefixWord ++ tailWord_6618001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618001).length < 2 ^ (prefixWord ++ tailWord_6618001).sum := by decide
  have hdescent : baseEnd_6618001 < baseStart_6618001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618006 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6618006 : Nat := 118140960795 + 6618006 * 2 ^ 59
def prefixEnd_6618006 : Nat := 4983230072969 + 3 ^ 40 * 6618006 * 2
def baseEnd_6618006 : Nat := 3398218052339139254789351

theorem tailTrace_6618006 : CollatzResearch.WordTrace tailWord_6618006 prefixEnd_6618006 3398218052339139254789351 := by
  unfold tailWord_6618006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15086156803881375142805117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160919005908068001523254581 15086156803881375142805117)
  ·
    refine ⟨5657308801455515678551919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15086156803881375142805117 5657308801455515678551919)
    ·
      refine ⟨8485963202183273517827879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5657308801455515678551919 8485963202183273517827879)
      ·
        refine ⟨12728944803274910276741819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8485963202183273517827879 12728944803274910276741819)
        ·
          refine ⟨19093417204912365415112729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12728944803274910276741819 19093417204912365415112729)
          ·
            refine ⟨14320062903684274061334547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19093417204912365415112729 14320062903684274061334547)
            ·
              refine ⟨21480094355526411092001821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14320062903684274061334547 21480094355526411092001821)
              ·
                refine ⟨8055035383322404159500683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21480094355526411092001821 8055035383322404159500683)
                ·
                  refine ⟨12082553074983606239251025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8055035383322404159500683 12082553074983606239251025)
                  ·
                    refine ⟨9061914806237704679438269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12082553074983606239251025 9061914806237704679438269)
                    ·
                      refine ⟨3398218052339139254789351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9061914806237704679438269 3398218052339139254789351)
                      ·
                        rfl

theorem cell23_6618006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6618006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618006 prefixEnd_6618006 := by exact prefixLift 6618006
  have htrace : WordTrace (prefixWord ++ tailWord_6618006) baseStart_6618006 baseEnd_6618006 := by
    simpa [prefixWord, tailWord_6618006, baseEnd_6618006] using wordTrace_append hprefix tailTrace_6618006
  have hstable : (prefixWord ++ tailWord_6618006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618006).length < 2 ^ (prefixWord ++ tailWord_6618006).sum := by decide
  have hdescent : baseEnd_6618006 < baseStart_6618006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618048 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 7]
def baseStart_6618048 : Nat := 118140960795 + 6618048 * 2 ^ 59
def prefixEnd_6618048 : Nat := 4983230072969 + 3 ^ 40 * 6618048 * 2
def baseEnd_6618048 : Nat := 377582179836292010051573

theorem tailTrace_6618048 : CollatzResearch.WordTrace tailWord_6618048 prefixEnd_6618048 377582179836292010051573 := by
  unfold tailWord_6618048
  simp only [CollatzResearch.WordTrace]
  refine ⟨120690020363974921728955399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160920027151966562305273865 120690020363974921728955399)
  ·
    refine ⟨181035030545962382593433099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120690020363974921728955399 181035030545962382593433099)
    ·
      refine ⟨271552545818943573890149649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181035030545962382593433099 271552545818943573890149649)
      ·
        refine ⟨203664409364207680417612237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271552545818943573890149649 203664409364207680417612237)
        ·
          refine ⟨76374153511577880156604589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203664409364207680417612237 76374153511577880156604589)
          ·
            refine ⟨28640307566841705058726721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76374153511577880156604589 28640307566841705058726721)
            ·
              refine ⟨21480230675131278794045041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28640307566841705058726721 21480230675131278794045041)
              ·
                refine ⟨16110173006348459095533781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21480230675131278794045041 16110173006348459095533781)
                ·
                  refine ⟨377582179836292010051573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16110173006348459095533781 377582179836292010051573)
                  ·
                    rfl

theorem cell23_6618048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 7].length) (baseStart_6618048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618048 prefixEnd_6618048 := by exact prefixLift 6618048
  have htrace : WordTrace (prefixWord ++ tailWord_6618048) baseStart_6618048 baseEnd_6618048 := by
    simpa [prefixWord, tailWord_6618048, baseEnd_6618048] using wordTrace_append hprefix tailTrace_6618048
  have hstable : (prefixWord ++ tailWord_6618048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618048).length < 2 ^ (prefixWord ++ tailWord_6618048).sum := by decide
  have hdescent : baseEnd_6618048 < baseStart_6618048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618054 : List Nat := [6, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_6618054 : Nat := 118140960795 + 6618054 * 2 ^ 59
def prefixEnd_6618054 : Nat := 4983230072969 + 3 ^ 40 * 6618054 * 2
def baseEnd_6618054 : Nat := 3398242699410555066989131

theorem tailTrace_6618054 : CollatzResearch.WordTrace tailWord_6618054 prefixEnd_6618054 3398242699410555066989131 := by
  unfold tailWord_6618054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543133111435253327582163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160920173043952070988419477 7543133111435253327582163)
  ·
    refine ⟨11314699667152879991373245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7543133111435253327582163 11314699667152879991373245)
    ·
      refine ⟨4243012375182329996764967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11314699667152879991373245 4243012375182329996764967)
      ·
        refine ⟨6364518562773494995147451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243012375182329996764967 6364518562773494995147451)
        ·
          refine ⟨9546777844160242492721177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364518562773494995147451 9546777844160242492721177)
          ·
            refine ⟨7160083383120181869540883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9546777844160242492721177 7160083383120181869540883)
            ·
              refine ⟨10740125074680272804311325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160083383120181869540883 10740125074680272804311325)
              ·
                refine ⟨4027546903005102301616747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10740125074680272804311325 4027546903005102301616747)
                ·
                  refine ⟨6041320354507653452425121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027546903005102301616747 6041320354507653452425121)
                  ·
                    refine ⟨4530990265880740089318841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6041320354507653452425121 4530990265880740089318841)
                    ·
                      refine ⟨3398242699410555066989131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4530990265880740089318841 3398242699410555066989131)
                      ·
                        rfl

theorem cell23_6618054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_6618054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618054 prefixEnd_6618054 := by exact prefixLift 6618054
  have htrace : WordTrace (prefixWord ++ tailWord_6618054) baseStart_6618054 baseEnd_6618054 := by
    simpa [prefixWord, tailWord_6618054, baseEnd_6618054] using wordTrace_append hprefix tailTrace_6618054
  have hstable : (prefixWord ++ tailWord_6618054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618054).length < 2 ^ (prefixWord ++ tailWord_6618054).sum := by decide
  have hdescent : baseEnd_6618054 < baseStart_6618054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618082 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 7]
def baseStart_6618082 : Nat := 118140960795 + 6618082 * 2 ^ 59
def prefixEnd_6618082 : Nat := 4983230072969 + 3 ^ 40 * 6618082 * 2
def baseEnd_6618082 : Nat := 377584119652097884159889

theorem tailTrace_6618082 : CollatzResearch.WordTrace tailWord_6618082 prefixEnd_6618082 377584119652097884159889 := by
  unfold tailWord_6618082
  simp only [CollatzResearch.WordTrace]
  refine ⟨60345320202456666816162125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160920853873217778176432333 60345320202456666816162125)
  ·
    refine ⟨22629495075921250056060797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60345320202456666816162125 22629495075921250056060797)
    ·
      refine ⟨8486060653470468771022799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22629495075921250056060797 8486060653470468771022799)
      ·
        refine ⟨12729090980205703156534199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8486060653470468771022799 12729090980205703156534199)
        ·
          refine ⟨19093636470308554734801299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12729090980205703156534199 19093636470308554734801299)
          ·
            refine ⟨28640454705462832102201949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19093636470308554734801299 28640454705462832102201949)
            ·
              refine ⟨10740170514548562038325731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28640454705462832102201949 10740170514548562038325731)
              ·
                refine ⟨16110255771822843057488597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10740170514548562038325731 16110255771822843057488597)
                ·
                  refine ⟨377584119652097884159889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16110255771822843057488597 377584119652097884159889)
                  ·
                    rfl

theorem cell23_6618082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_6618082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618082 prefixEnd_6618082 := by exact prefixLift 6618082
  have htrace : WordTrace (prefixWord ++ tailWord_6618082) baseStart_6618082 baseEnd_6618082 := by
    simpa [prefixWord, tailWord_6618082, baseEnd_6618082] using wordTrace_append hprefix tailTrace_6618082
  have hstable : (prefixWord ++ tailWord_6618082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618082).length < 2 ^ (prefixWord ++ tailWord_6618082).sum := by decide
  have hdescent : baseEnd_6618082 < baseStart_6618082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618088 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6618088 : Nat := 118140960795 + 6618088 * 2 ^ 59
def prefixEnd_6618088 : Nat := 4983230072969 + 3 ^ 40 * 6618088 * 2
def baseEnd_6618088 : Nat := 3398260157752807933963973

theorem tailTrace_6618088 : CollatzResearch.WordTrace tailWord_6618088 prefixEnd_6618088 3398260157752807933963973 := by
  unfold tailWord_6618088
  simp only [CollatzResearch.WordTrace]
  refine ⟨120690749823902465144683459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160920999765203286859577945 120690749823902465144683459)
  ·
    refine ⟨181036124735853697717025189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120690749823902465144683459 181036124735853697717025189)
    ·
      refine ⟨33944273387972568321942223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181036124735853697717025189 33944273387972568321942223)
      ·
        refine ⟨50916410081958852482913335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33944273387972568321942223 50916410081958852482913335)
        ·
          refine ⟨76374615122938278724370003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50916410081958852482913335 76374615122938278724370003)
          ·
            refine ⟨114561922684407418086555005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76374615122938278724370003 114561922684407418086555005)
            ·
              refine ⟨42960721006652781782458127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114561922684407418086555005 42960721006652781782458127)
              ·
                refine ⟨64441081509979172673687191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42960721006652781782458127 64441081509979172673687191)
                ·
                  refine ⟨96661622264968759010530787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64441081509979172673687191 96661622264968759010530787)
                  ·
                    refine ⟨144992433397453138515796181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96661622264968759010530787 144992433397453138515796181)
                    ·
                      refine ⟨3398260157752807933963973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144992433397453138515796181 3398260157752807933963973)
                      ·
                        rfl

theorem cell23_6618088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6618088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618088 prefixEnd_6618088 := by exact prefixLift 6618088
  have htrace : WordTrace (prefixWord ++ tailWord_6618088) baseStart_6618088 baseEnd_6618088 := by
    simpa [prefixWord, tailWord_6618088, baseEnd_6618088] using wordTrace_append hprefix tailTrace_6618088
  have hstable : (prefixWord ++ tailWord_6618088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618088).length < 2 ^ (prefixWord ++ tailWord_6618088).sum := by decide
  have hdescent : baseEnd_6618088 < baseStart_6618088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618115 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 6, 4, 2]
def baseStart_6618115 : Nat := 118140960795 + 6618115 * 2 ^ 59
def prefixEnd_6618115 : Nat := 4983230072969 + 3 ^ 40 * 6618115 * 2
def baseEnd_6618115 : Nat := 3398274021730479328326349

theorem tailTrace_6618115 : CollatzResearch.WordTrace tailWord_6618115 prefixEnd_6618115 3398274021730479328326349 := by
  unfold tailWord_6618115
  simp only [CollatzResearch.WordTrace]
  refine ⟨241382484418707113900599799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160921656279138075933733199 241382484418707113900599799)
  ·
    refine ⟨362073726628060670850899699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241382484418707113900599799 362073726628060670850899699)
    ·
      refine ⟨543110589942091006276349549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362073726628060670850899699 543110589942091006276349549)
      ·
        refine ⟨203666471228284127353631081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 543110589942091006276349549 203666471228284127353631081)
        ·
          refine ⟨152749853421213095515223311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203666471228284127353631081 152749853421213095515223311)
          ·
            refine ⟨229124780131819643272834967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152749853421213095515223311 229124780131819643272834967)
            ·
              refine ⟨343687170197729464909252451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229124780131819643272834967 343687170197729464909252451)
              ·
                refine ⟨515530755296594197363878677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343687170197729464909252451 515530755296594197363878677)
                ·
                  refine ⟨24165504154527853001431813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 515530755296594197363878677 24165504154527853001431813)
                  ·
                    refine ⟨4531032028973972437768465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24165504154527853001431813 4531032028973972437768465)
                    ·
                      refine ⟨3398274021730479328326349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4531032028973972437768465 3398274021730479328326349)
                      ·
                        rfl

theorem cell23_6618115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_6618115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618115 prefixEnd_6618115 := by exact prefixLift 6618115
  have htrace : WordTrace (prefixWord ++ tailWord_6618115) baseStart_6618115 baseEnd_6618115 := by
    simpa [prefixWord, tailWord_6618115, baseEnd_6618115] using wordTrace_append hprefix tailTrace_6618115
  have hstable : (prefixWord ++ tailWord_6618115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618115).length < 2 ^ (prefixWord ++ tailWord_6618115).sum := by decide
  have hdescent : baseEnd_6618115 < baseStart_6618115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618169 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 3]
def baseStart_6618169 : Nat := 118140960795 + 6618169 * 2 ^ 59
def prefixEnd_6618169 : Nat := 4983230072969 + 3 ^ 40 * 6618169 * 2
def baseEnd_6618169 : Nat := 3398301749685822117051101

theorem tailTrace_6618169 : CollatzResearch.WordTrace tailWord_6618169 prefixEnd_6618169 3398301749685822117051101 := by
  unfold tailWord_6618169
  simp only [CollatzResearch.WordTrace]
  refine ⟨241384453960511481123065561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160922969307007654082043707 241384453960511481123065561)
  ·
    refine ⟨181038340470383610842299171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241384453960511481123065561 181038340470383610842299171)
    ·
      refine ⟨271557510705575416263448757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181038340470383610842299171 271557510705575416263448757)
      ·
        refine ⟨25458516628647695274698321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271557510705575416263448757 25458516628647695274698321)
        ·
          refine ⟨19093887471485771456023741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25458516628647695274698321 19093887471485771456023741)
          ·
            refine ⟨7160207801807164296008903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19093887471485771456023741 7160207801807164296008903)
            ·
              refine ⟨10740311702710746444013355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160207801807164296008903 10740311702710746444013355)
              ·
                refine ⟨16110467554066119666020033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10740311702710746444013355 16110467554066119666020033)
                ·
                  refine ⟨12082850665549589749515025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16110467554066119666020033 12082850665549589749515025)
                  ·
                    refine ⟨9062137999162192312136269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12082850665549589749515025 9062137999162192312136269)
                    ·
                      refine ⟨3398301749685822117051101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9062137999162192312136269 3398301749685822117051101)
                      ·
                        rfl

theorem cell23_6618169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_6618169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618169 prefixEnd_6618169 := by exact prefixLift 6618169
  have htrace : WordTrace (prefixWord ++ tailWord_6618169) baseStart_6618169 baseEnd_6618169 := by
    simpa [prefixWord, tailWord_6618169, baseEnd_6618169] using wordTrace_append hprefix tailTrace_6618169
  have hstable : (prefixWord ++ tailWord_6618169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618169).length < 2 ^ (prefixWord ++ tailWord_6618169).sum := by decide
  have hdescent : baseEnd_6618169 < baseStart_6618169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618189 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 6]
def baseStart_6618189 : Nat := 118140960795 + 6618189 * 2 ^ 59
def prefixEnd_6618189 : Nat := 4983230072969 + 3 ^ 40 * 6618189 * 2
def baseEnd_6618189 : Nat := 377590224366545782089001

theorem tailTrace_6618189 : CollatzResearch.WordTrace tailWord_6618189 prefixEnd_6618189 377590224366545782089001 := by
  unfold tailWord_6618189
  simp only [CollatzResearch.WordTrace]
  refine ⟨241385183420439024538793621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160923455613626016359195747 241385183420439024538793621)
  ·
    refine ⟨11314930472833079275255951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 241385183420439024538793621 11314930472833079275255951)
    ·
      refine ⟨16972395709249618912883927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11314930472833079275255951 16972395709249618912883927)
      ·
        refine ⟨25458593563874428369325891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16972395709249618912883927 25458593563874428369325891)
        ·
          refine ⟨38187890345811642553988837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25458593563874428369325891 38187890345811642553988837)
          ·
            refine ⟨7160229439839682978872907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38187890345811642553988837 7160229439839682978872907)
            ·
              refine ⟨10740344159759524468309361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160229439839682978872907 10740344159759524468309361)
              ·
                refine ⟨8055258119819643351232021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10740344159759524468309361 8055258119819643351232021)
                ·
                  refine ⟨377590224366545782089001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8055258119819643351232021 377590224366545782089001)
                  ·
                    rfl

theorem cell23_6618189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_6618189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618189 prefixEnd_6618189 := by exact prefixLift 6618189
  have htrace : WordTrace (prefixWord ++ tailWord_6618189) baseStart_6618189 baseEnd_6618189 := by
    simpa [prefixWord, tailWord_6618189, baseEnd_6618189] using wordTrace_append hprefix tailTrace_6618189
  have hstable : (prefixWord ++ tailWord_6618189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618189).length < 2 ^ (prefixWord ++ tailWord_6618189).sum := by decide
  have hdescent : baseEnd_6618189 < baseStart_6618189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618192 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 2, 3, 2]
def baseStart_6618192 : Nat := 118140960795 + 6618192 * 2 ^ 59
def prefixEnd_6618192 : Nat := 4983230072969 + 3 ^ 40 * 6618192 * 2
def baseEnd_6618192 : Nat := 3398313559740875527063495

theorem tailTrace_6618192 : CollatzResearch.WordTrace tailWord_6618192 prefixEnd_6618192 3398313559740875527063495 := by
  unfold tailWord_6618192
  simp only [CollatzResearch.WordTrace]
  refine ⟨120692646419714078025576415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160923528559618770700768553 120692646419714078025576415)
  ·
    refine ⟨181038969629571117038364623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120692646419714078025576415 181038969629571117038364623)
    ·
      refine ⟨271558454444356675557546935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181038969629571117038364623 271558454444356675557546935)
      ·
        refine ⟨407337681666535013336320403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271558454444356675557546935 407337681666535013336320403)
        ·
          refine ⟨611006522499802520004480605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407337681666535013336320403 611006522499802520004480605)
          ·
            refine ⟨229127445937425945001680227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611006522499802520004480605 229127445937425945001680227)
            ·
              refine ⟨343691168906138917502520341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229127445937425945001680227 343691168906138917502520341)
              ·
                refine ⟨16110523542475261757930641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343691168906138917502520341 16110523542475261757930641)
                ·
                  refine ⟨12082892656856446318447981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16110523542475261757930641 12082892656856446318447981)
                  ·
                    refine ⟨4531084746321167369417993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12082892656856446318447981 4531084746321167369417993)
                    ·
                      refine ⟨3398313559740875527063495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4531084746321167369417993 3398313559740875527063495)
                      ·
                        rfl

theorem cell23_6618192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 3, 2].length) (baseStart_6618192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618192 prefixEnd_6618192 := by exact prefixLift 6618192
  have htrace : WordTrace (prefixWord ++ tailWord_6618192) baseStart_6618192 baseEnd_6618192 := by
    simpa [prefixWord, tailWord_6618192, baseEnd_6618192] using wordTrace_append hprefix tailTrace_6618192
  have hstable : (prefixWord ++ tailWord_6618192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618192).length < 2 ^ (prefixWord ++ tailWord_6618192).sum := by decide
  have hdescent : baseEnd_6618192 < baseStart_6618192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618233 : List Nat := [1, 2, 1, 3, 5, 2, 1, 3, 1, 1, 3]
def baseStart_6618233 : Nat := 118140960795 + 6618233 * 2 ^ 59
def prefixEnd_6618233 : Nat := 4983230072969 + 3 ^ 40 * 6618233 * 2
def baseEnd_6618233 : Nat := 3398334612447709866650807

theorem tailTrace_6618233 : CollatzResearch.WordTrace tailWord_6618233 prefixEnd_6618233 3398334612447709866650807 := by
  unfold tailWord_6618233
  simp only [CollatzResearch.WordTrace]
  refine ⟨241386788232279620053395353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160924525488186413368930235 241386788232279620053395353)
  ·
    refine ⟨181040091174209715040046515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241386788232279620053395353 181040091174209715040046515)
    ·
      refine ⟨271560136761314572560069773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181040091174209715040046515 271560136761314572560069773)
      ·
        refine ⟨101835051285492964710026165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271560136761314572560069773 101835051285492964710026165)
        ·
          refine ⟨9547036058014965441564953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101835051285492964710026165 9547036058014965441564953)
          ·
            refine ⟨7160277043511224081173715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9547036058014965441564953 7160277043511224081173715)
            ·
              refine ⟨10740415565266836121760573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160277043511224081173715 10740415565266836121760573)
              ·
                refine ⟨4027655836975063545660215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10740415565266836121760573 4027655836975063545660215)
                ·
                  refine ⟨6041483755462595318490323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027655836975063545660215 6041483755462595318490323)
                  ·
                    refine ⟨9062225633193892977735485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6041483755462595318490323 9062225633193892977735485)
                    ·
                      refine ⟨3398334612447709866650807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9062225633193892977735485 3398334612447709866650807)
                      ·
                        rfl

theorem cell23_6618233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_6618233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618233 prefixEnd_6618233 := by exact prefixLift 6618233
  have htrace : WordTrace (prefixWord ++ tailWord_6618233) baseStart_6618233 baseEnd_6618233 := by
    simpa [prefixWord, tailWord_6618233, baseEnd_6618233] using wordTrace_append hprefix tailTrace_6618233
  have hstable : (prefixWord ++ tailWord_6618233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618233).length < 2 ^ (prefixWord ++ tailWord_6618233).sum := by decide
  have hdescent : baseEnd_6618233 < baseStart_6618233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618235 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 4]
def baseStart_6618235 : Nat := 118140960795 + 6618235 * 2 ^ 59
def prefixEnd_6618235 : Nat := 4983230072969 + 3 ^ 40 * 6618235 * 2
def baseEnd_6618235 : Nat := 3398335639409018858825797

theorem tailTrace_6618235 : CollatzResearch.WordTrace tailWord_6618235 prefixEnd_6618235 3398335639409018858825797 := by
  unfold tailWord_6618235
  simp only [CollatzResearch.WordTrace]
  refine ⟨241386861178272374394968159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160924574118848249596645439 241386861178272374394968159)
  ·
    refine ⟨362080291767408561592452239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241386861178272374394968159 362080291767408561592452239)
    ·
      refine ⟨543120437651112842388678359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362080291767408561592452239 543120437651112842388678359)
      ·
        refine ⟨814680656476669263583017539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543120437651112842388678359 814680656476669263583017539)
        ·
          refine ⟨1222020984715003895374526309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814680656476669263583017539 1222020984715003895374526309)
          ·
            refine ⟨229128934634063230382723683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1222020984715003895374526309 229128934634063230382723683)
            ·
              refine ⟨343693401951094845574085525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229128934634063230382723683 343693401951094845574085525)
              ·
                refine ⟨16110628216457570886285259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343693401951094845574085525 16110628216457570886285259)
                ·
                  refine ⟨24165942324686356329427889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16110628216457570886285259 24165942324686356329427889)
                  ·
                    refine ⟨18124456743514767247070917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24165942324686356329427889 18124456743514767247070917)
                    ·
                      refine ⟨3398335639409018858825797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18124456743514767247070917 3398335639409018858825797)
                      ·
                        rfl

theorem cell23_6618235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 4].length) (baseStart_6618235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618235 prefixEnd_6618235 := by exact prefixLift 6618235
  have htrace : WordTrace (prefixWord ++ tailWord_6618235) baseStart_6618235 baseEnd_6618235 := by
    simpa [prefixWord, tailWord_6618235, baseEnd_6618235] using wordTrace_append hprefix tailTrace_6618235
  have hstable : (prefixWord ++ tailWord_6618235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618235).length < 2 ^ (prefixWord ++ tailWord_6618235).sum := by decide
  have hdescent : baseEnd_6618235 < baseStart_6618235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618266 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_6618266 : Nat := 118140960795 + 6618266 * 2 ^ 59
def prefixEnd_6618266 : Nat := 4983230072969 + 3 ^ 40 * 6618266 * 2
def baseEnd_6618266 : Nat := 1132783852436436079179385

theorem tailTrace_6618266 : CollatzResearch.WordTrace tailWord_6618266 prefixEnd_6618266 1132783852436436079179385 := by
  unfold tailWord_6618266
  simp only [CollatzResearch.WordTrace]
  refine ⟨60346997960290016672336663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160925327894106711126231101 60346997960290016672336663)
  ·
    refine ⟨90520496940435025008504995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60346997960290016672336663 90520496940435025008504995)
    ·
      refine ⟨135780745410652537512757493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90520496940435025008504995 135780745410652537512757493)
      ·
        refine ⟨12729444882248675391821015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135780745410652537512757493 12729444882248675391821015)
        ·
          refine ⟨19094167323373013087731523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12729444882248675391821015 19094167323373013087731523)
          ·
            refine ⟨28641250985059519631597285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19094167323373013087731523 28641250985059519631597285)
            ·
              refine ⟨5370234559698659930924491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28641250985059519631597285 5370234559698659930924491)
              ·
                refine ⟨8055351839547989896386737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370234559698659930924491 8055351839547989896386737)
                ·
                  refine ⟨6041513879660992422290053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8055351839547989896386737 6041513879660992422290053)
                  ·
                    refine ⟨1132783852436436079179385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6041513879660992422290053 1132783852436436079179385)
                    ·
                      rfl

theorem cell23_6618266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_6618266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618266 prefixEnd_6618266 := by exact prefixLift 6618266
  have htrace : WordTrace (prefixWord ++ tailWord_6618266) baseStart_6618266 baseEnd_6618266 := by
    simpa [prefixWord, tailWord_6618266, baseEnd_6618266] using wordTrace_append hprefix tailTrace_6618266
  have hstable : (prefixWord ++ tailWord_6618266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618266).length < 2 ^ (prefixWord ++ tailWord_6618266).sum := by decide
  have hdescent : baseEnd_6618266 < baseStart_6618266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618272 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 3]
def baseStart_6618272 : Nat := 118140960795 + 6618272 * 2 ^ 59
def prefixEnd_6618272 : Nat := 4983230072969 + 3 ^ 40 * 6618272 * 2
def baseEnd_6618272 : Nat := 3398354638193235214063127

theorem tailTrace_6618272 : CollatzResearch.WordTrace tailWord_6618272 prefixEnd_6618272 3398354638193235214063127 := by
  unfold tailWord_6618272
  simp only [CollatzResearch.WordTrace]
  refine ⟨120694105339569164857032535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160925473786092219809376713 120694105339569164857032535)
  ·
    refine ⟨181041158009353747285548803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120694105339569164857032535 181041158009353747285548803)
    ·
      refine ⟨271561737014030620928323205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181041158009353747285548803 271561737014030620928323205)
      ·
        refine ⟨50917825690130741424060601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271561737014030620928323205 50917825690130741424060601)
        ·
          refine ⟨38188369267598056068045451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50917825690130741424060601 38188369267598056068045451)
          ·
            refine ⟨57282553901397084102068177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38188369267598056068045451 57282553901397084102068177)
            ·
              refine ⟨42961915426047813076551133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57282553901397084102068177 42961915426047813076551133)
              ·
                refine ⟨16110718284767929903706675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42961915426047813076551133 16110718284767929903706675)
                ·
                  refine ⟨24166077427151894855560013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16110718284767929903706675 24166077427151894855560013)
                  ·
                    refine ⟨9062279035181960570835005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24166077427151894855560013 9062279035181960570835005)
                    ·
                      refine ⟨3398354638193235214063127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9062279035181960570835005 3398354638193235214063127)
                      ·
                        rfl

theorem cell23_6618272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_6618272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618272 prefixEnd_6618272 := by exact prefixLift 6618272
  have htrace : WordTrace (prefixWord ++ tailWord_6618272) baseStart_6618272 baseEnd_6618272 := by
    simpa [prefixWord, tailWord_6618272, baseEnd_6618272] using wordTrace_append hprefix tailTrace_6618272
  have hstable : (prefixWord ++ tailWord_6618272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618272).length < 2 ^ (prefixWord ++ tailWord_6618272).sum := by decide
  have hdescent : baseEnd_6618272 < baseStart_6618272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618276 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_6618276 : Nat := 118140960795 + 6618276 * 2 ^ 59
def prefixEnd_6618276 : Nat := 4983230072969 + 3 ^ 40 * 6618276 * 2
def baseEnd_6618276 : Nat := 3398356692115853198413109

theorem tailTrace_6618276 : CollatzResearch.WordTrace tailWord_6618276 prefixEnd_6618276 3398356692115853198413109 := by
  unfold tailWord_6618276
  simp only [CollatzResearch.WordTrace]
  refine ⟨120694178285561919198605341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160925571047415892264807121 120694178285561919198605341)
  ·
    refine ⟨45260316857085719699477003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120694178285561919198605341 45260316857085719699477003)
    ·
      refine ⟨67890475285628579549215505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45260316857085719699477003 67890475285628579549215505)
      ·
        refine ⟨50917856464221434661911629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67890475285628579549215505 50917856464221434661911629)
        ·
          refine ⟨19094196174083037998216861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50917856464221434661911629 19094196174083037998216861)
          ·
            refine ⟨7160323565281139249331323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19094196174083037998216861 7160323565281139249331323)
            ·
              refine ⟨10740485347921708873996985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160323565281139249331323 10740485347921708873996985)
              ·
                refine ⟨8055364010941281655497739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10740485347921708873996985 8055364010941281655497739)
                ·
                  refine ⟨12083046016411922483246609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8055364010941281655497739 12083046016411922483246609)
                  ·
                    refine ⟨9062284512308941862434957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12083046016411922483246609 9062284512308941862434957)
                    ·
                      refine ⟨3398356692115853198413109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9062284512308941862434957 3398356692115853198413109)
                      ·
                        rfl

theorem cell23_6618276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_6618276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618276 prefixEnd_6618276 := by exact prefixLift 6618276
  have htrace : WordTrace (prefixWord ++ tailWord_6618276) baseStart_6618276 baseEnd_6618276 := by
    simpa [prefixWord, tailWord_6618276, baseEnd_6618276] using wordTrace_append hprefix tailTrace_6618276
  have hstable : (prefixWord ++ tailWord_6618276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618276).length < 2 ^ (prefixWord ++ tailWord_6618276).sum := by decide
  have hdescent : baseEnd_6618276 < baseStart_6618276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618289 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6618289 : Nat := 118140960795 + 6618289 * 2 ^ 59
def prefixEnd_6618289 : Nat := 4983230072969 + 3 ^ 40 * 6618289 * 2
def baseEnd_6618289 : Nat := 3398363367364361647550549

theorem tailTrace_6618289 : CollatzResearch.WordTrace tailWord_6618289 prefixEnd_6618289 3398363367364361647550549 := by
  unfold tailWord_6618289
  simp only [CollatzResearch.WordTrace]
  refine ⟨241388830720076741617433921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160925887146717827744955947 241388830720076741617433921)
  ·
    refine ⟨181041623040057556213075441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241388830720076741617433921 181041623040057556213075441)
    ·
      refine ⟨135781217280043167159806581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181041623040057556213075441 135781217280043167159806581)
      ·
        refine ⟨12729489120004046921231867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135781217280043167159806581 12729489120004046921231867)
        ·
          refine ⟨19094233680006070381847801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12729489120004046921231867 19094233680006070381847801)
          ·
            refine ⟨14320675260004552786385851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19094233680006070381847801 14320675260004552786385851)
            ·
              refine ⟨21481012890006829179578777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14320675260004552786385851 21481012890006829179578777)
              ·
                refine ⟨16110759667505121884684083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21481012890006829179578777 16110759667505121884684083)
                ·
                  refine ⟨24166139501257682827026125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16110759667505121884684083 24166139501257682827026125)
                  ·
                    refine ⟨9062302312971631060134797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24166139501257682827026125 9062302312971631060134797)
                    ·
                      refine ⟨3398363367364361647550549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9062302312971631060134797 3398363367364361647550549)
                      ·
                        rfl

theorem cell23_6618289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6618289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618289 prefixEnd_6618289 := by exact prefixLift 6618289
  have htrace : WordTrace (prefixWord ++ tailWord_6618289) baseStart_6618289 baseEnd_6618289 := by
    simpa [prefixWord, tailWord_6618289, baseEnd_6618289] using wordTrace_append hprefix tailTrace_6618289
  have hstable : (prefixWord ++ tailWord_6618289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618289).length < 2 ^ (prefixWord ++ tailWord_6618289).sum := by decide
  have hdescent : baseEnd_6618289 < baseStart_6618289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618315 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 5]
def baseStart_6618315 : Nat := 118140960795 + 6618315 * 2 ^ 59
def prefixEnd_6618315 : Nat := 4983230072969 + 3 ^ 40 * 6618315 * 2
def baseEnd_6618315 : Nat := 3398376717861378545825429

theorem tailTrace_6618315 : CollatzResearch.WordTrace tailWord_6618315 prefixEnd_6618315 3398376717861378545825429 := by
  unfold tailWord_6618315
  simp only [CollatzResearch.WordTrace]
  refine ⟨241389779017982548057880399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160926519345321698705253599 241389779017982548057880399)
  ·
    refine ⟨362084668526973822086820599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241389779017982548057880399 362084668526973822086820599)
    ·
      refine ⟨543127002790460733130230899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362084668526973822086820599 543127002790460733130230899)
      ·
        refine ⟨814690504185691099695346349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543127002790460733130230899 814690504185691099695346349)
        ·
          refine ⟨305508939069634162385754881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814690504185691099695346349 305508939069634162385754881)
          ·
            refine ⟨229131704302225621789316161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305508939069634162385754881 229131704302225621789316161)
            ·
              refine ⟨171848778226669216341987121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229131704302225621789316161 171848778226669216341987121)
              ·
                refine ⟨128886583670001912256490341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171848778226669216341987121 128886583670001912256490341)
                ·
                  refine ⟨24166234438125358548091939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128886583670001912256490341 24166234438125358548091939)
                  ·
                    refine ⟨36249351657188037822137909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24166234438125358548091939 36249351657188037822137909)
                    ·
                      refine ⟨3398376717861378545825429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36249351657188037822137909 3398376717861378545825429)
                      ·
                        rfl

theorem cell23_6618315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_6618315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618315 prefixEnd_6618315 := by exact prefixLift 6618315
  have htrace : WordTrace (prefixWord ++ tailWord_6618315) baseStart_6618315 baseEnd_6618315 := by
    simpa [prefixWord, tailWord_6618315, baseEnd_6618315] using wordTrace_append hprefix tailTrace_6618315
  have hstable : (prefixWord ++ tailWord_6618315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618315).length < 2 ^ (prefixWord ++ tailWord_6618315).sum := by decide
  have hdescent : baseEnd_6618315 < baseStart_6618315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618322 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_6618322 : Nat := 118140960795 + 6618322 * 2 ^ 59
def prefixEnd_6618322 : Nat := 4983230072969 + 3 ^ 40 * 6618322 * 2
def baseEnd_6618322 : Nat := 1132793437408653339479299

theorem tailTrace_6618322 : CollatzResearch.WordTrace tailWord_6618322 prefixEnd_6618322 1132793437408653339479299 := by
  unfold tailWord_6618322
  simp only [CollatzResearch.WordTrace]
  refine ⟨60347508582239297063346305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160926689552638125502256813 60347508582239297063346305)
  ·
    refine ⟨45260631436679472797509729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60347508582239297063346305 45260631436679472797509729)
    ·
      refine ⟨33945473577509604598132297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45260631436679472797509729 33945473577509604598132297)
      ·
        refine ⟨25459105183132203448599223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33945473577509604598132297 25459105183132203448599223)
        ·
          refine ⟨38188657774698305172898835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25459105183132203448599223 38188657774698305172898835)
          ·
            refine ⟨57282986662047457759348253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38188657774698305172898835 57282986662047457759348253)
            ·
              refine ⟨21481119998267796659755595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57282986662047457759348253 21481119998267796659755595)
              ·
                refine ⟨32221679997401694989633393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21481119998267796659755595 32221679997401694989633393)
                ·
                  refine ⟨24166259998051271242225045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32221679997401694989633393 24166259998051271242225045)
                  ·
                    refine ⟨1132793437408653339479299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24166259998051271242225045 1132793437408653339479299)
                    ·
                      rfl

theorem cell23_6618322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_6618322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618322 prefixEnd_6618322 := by exact prefixLift 6618322
  have htrace : WordTrace (prefixWord ++ tailWord_6618322) baseStart_6618322 baseEnd_6618322 := by
    simpa [prefixWord, tailWord_6618322, baseEnd_6618322] using wordTrace_append hprefix tailTrace_6618322
  have hstable : (prefixWord ++ tailWord_6618322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618322).length < 2 ^ (prefixWord ++ tailWord_6618322).sum := by decide
  have hdescent : baseEnd_6618322 < baseStart_6618322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618329 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 6, 2, 2]
def baseStart_6618329 : Nat := 118140960795 + 6618329 * 2 ^ 59
def prefixEnd_6618329 : Nat := 4983230072969 + 3 ^ 40 * 6618329 * 2
def baseEnd_6618329 : Nat := 3398383906590541491050365

theorem tailTrace_6618329 : CollatzResearch.WordTrace tailWord_6618329 prefixEnd_6618329 3398383906590541491050365 := by
  unfold tailWord_6618329
  simp only [CollatzResearch.WordTrace]
  refine ⟨241390289639931828448890041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160926859759954552299260027 241390289639931828448890041)
  ·
    refine ⟨181042717229948871336667531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241390289639931828448890041 181042717229948871336667531)
    ·
      refine ⟨271564075844923307005001297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181042717229948871336667531 271564075844923307005001297)
      ·
        refine ⟨203673056883692480253750973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271564075844923307005001297 203673056883692480253750973)
        ·
          refine ⟨76377396331384680095156615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203673056883692480253750973 76377396331384680095156615)
          ·
            refine ⟨114566094497077020142734923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76377396331384680095156615 114566094497077020142734923)
            ·
              refine ⟨171849141745615530214102385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114566094497077020142734923 171849141745615530214102385)
              ·
                refine ⟨128886856309211647660576789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171849141745615530214102385 128886856309211647660576789)
                ·
                  refine ⟨6041571389494295984089537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128886856309211647660576789 6041571389494295984089537)
                  ·
                    refine ⟨4531178542120721988067153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6041571389494295984089537 4531178542120721988067153)
                    ·
                      refine ⟨3398383906590541491050365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4531178542120721988067153 3398383906590541491050365)
                      ·
                        rfl

theorem cell23_6618329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 2, 2].length) (baseStart_6618329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618329 prefixEnd_6618329 := by exact prefixLift 6618329
  have htrace : WordTrace (prefixWord ++ tailWord_6618329) baseStart_6618329 baseEnd_6618329 := by
    simpa [prefixWord, tailWord_6618329, baseEnd_6618329] using wordTrace_append hprefix tailTrace_6618329
  have hstable : (prefixWord ++ tailWord_6618329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618329).length < 2 ^ (prefixWord ++ tailWord_6618329).sum := by decide
  have hdescent : baseEnd_6618329 < baseStart_6618329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618335 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 9]
def baseStart_6618335 : Nat := 118140960795 + 6618335 * 2 ^ 59
def prefixEnd_6618335 : Nat := 4983230072969 + 3 ^ 40 * 6618335 * 2
def baseEnd_6618335 : Nat := 377598554163829829730593

theorem tailTrace_6618335 : CollatzResearch.WordTrace tailWord_6618335 prefixEnd_6618335 377598554163829829730593 := by
  unfold tailWord_6618335
  simp only [CollatzResearch.WordTrace]
  refine ⟨241390508477910091473608459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160927005651940060982405639 241390508477910091473608459)
  ·
    refine ⟨362085762716865137210412689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241390508477910091473608459 362085762716865137210412689)
    ·
      refine ⟨271564322037648852907809517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362085762716865137210412689 271564322037648852907809517)
      ·
        refine ⟨101836620764118319840428569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271564322037648852907809517 101836620764118319840428569)
        ·
          refine ⟨76377465573088739880321427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101836620764118319840428569 76377465573088739880321427)
          ·
            refine ⟨114566198359633109820482141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76377465573088739880321427 114566198359633109820482141)
            ·
              refine ⟨42962324384862416182680803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114566198359633109820482141 42962324384862416182680803)
              ·
                refine ⟨64443486577293624274021205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42962324384862416182680803 64443486577293624274021205)
                ·
                  refine ⟨377598554163829829730593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64443486577293624274021205 377598554163829829730593)
                  ·
                    rfl

theorem cell23_6618335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 9].length) (baseStart_6618335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618335 prefixEnd_6618335 := by exact prefixLift 6618335
  have htrace : WordTrace (prefixWord ++ tailWord_6618335) baseStart_6618335 baseEnd_6618335 := by
    simpa [prefixWord, tailWord_6618335, baseEnd_6618335] using wordTrace_append hprefix tailTrace_6618335
  have hstable : (prefixWord ++ tailWord_6618335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618335).length < 2 ^ (prefixWord ++ tailWord_6618335).sum := by decide
  have hdescent : baseEnd_6618335 < baseStart_6618335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618362 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_6618362 : Nat := 118140960795 + 6618362 * 2 ^ 59
def prefixEnd_6618362 : Nat := 4983230072969 + 3 ^ 40 * 6618362 * 2
def baseEnd_6618362 : Nat := 3398400851452139861937713

theorem tailTrace_6618362 : CollatzResearch.WordTrace tailWord_6618362 prefixEnd_6618362 3398400851452139861937713 := by
  unfold tailWord_6618362
  simp only [CollatzResearch.WordTrace]
  refine ⟨60347873312203068771210335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160927662165874850056560893 60347873312203068771210335)
  ·
    refine ⟨90521809968304603156815503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60347873312203068771210335 90521809968304603156815503)
    ·
      refine ⟨135782714952456904735223255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90521809968304603156815503 135782714952456904735223255)
      ·
        refine ⟨203674072428685357102834883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135782714952456904735223255 203674072428685357102834883)
        ·
          refine ⟨305511108643028035654252325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203674072428685357102834883 305511108643028035654252325)
          ·
            refine ⟨57283332870567756685172311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305511108643028035654252325 57283332870567756685172311)
            ·
              refine ⟨85924999305851635027758467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57283332870567756685172311 85924999305851635027758467)
              ·
                refine ⟨128887498958777452541637701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85924999305851635027758467 128887498958777452541637701)
                ·
                  refine ⟨24166406054770772351557069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128887498958777452541637701 24166406054770772351557069)
                  ·
                    refine ⟨9062402270539039631833901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24166406054770772351557069 9062402270539039631833901)
                    ·
                      refine ⟨3398400851452139861937713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9062402270539039631833901 3398400851452139861937713)
                      ·
                        rfl

theorem cell23_6618362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_6618362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618362 prefixEnd_6618362 := by exact prefixLift 6618362
  have htrace : WordTrace (prefixWord ++ tailWord_6618362) baseStart_6618362 baseEnd_6618362 := by
    simpa [prefixWord, tailWord_6618362, baseEnd_6618362] using wordTrace_append hprefix tailTrace_6618362
  have hstable : (prefixWord ++ tailWord_6618362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618362).length < 2 ^ (prefixWord ++ tailWord_6618362).sum := by decide
  have hdescent : baseEnd_6618362 < baseStart_6618362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618369 : List Nat := [1, 2, 4, 1, 1, 3, 2, 4, 5]
def baseStart_6618369 : Nat := 118140960795 + 6618369 * 2 ^ 59
def prefixEnd_6618369 : Nat := 4983230072969 + 3 ^ 40 * 6618369 * 2
def baseEnd_6618369 : Nat := 377600493979635703838909

theorem tailTrace_6618369 : CollatzResearch.WordTrace tailWord_6618369 prefixEnd_6618369 377600493979635703838909 := by
  unfold tailWord_6618369
  simp only [CollatzResearch.WordTrace]
  refine ⟨241391748559786915280346161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160927832373191276853564107 241391748559786915280346161)
  ·
    refine ⟨181043811419840186460259621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241391748559786915280346161 181043811419840186460259621)
    ·
      refine ⟨33945714641220034961298679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181043811419840186460259621 33945714641220034961298679)
      ·
        refine ⟨50918571961830052441948019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33945714641220034961298679 50918571961830052441948019)
        ·
          refine ⟨76377857942745078662922029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50918571961830052441948019 76377857942745078662922029)
          ·
            refine ⟨28641696728529404498595761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76377857942745078662922029 28641696728529404498595761)
            ·
              refine ⟨21481272546397053373946821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28641696728529404498595761 21481272546397053373946821)
              ·
                refine ⟨4027738602449447507615029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21481272546397053373946821 4027738602449447507615029)
                ·
                  refine ⟨377600493979635703838909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4027738602449447507615029 377600493979635703838909)
                  ·
                    rfl

theorem cell23_6618369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 5].length) (baseStart_6618369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618369 prefixEnd_6618369 := by exact prefixLift 6618369
  have htrace : WordTrace (prefixWord ++ tailWord_6618369) baseStart_6618369 baseEnd_6618369 := by
    simpa [prefixWord, tailWord_6618369, baseEnd_6618369] using wordTrace_append hprefix tailTrace_6618369
  have hstable : (prefixWord ++ tailWord_6618369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618369).length < 2 ^ (prefixWord ++ tailWord_6618369).sum := by decide
  have hdescent : baseEnd_6618369 < baseStart_6618369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618382 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_6618382 : Nat := 118140960795 + 6618382 * 2 ^ 59
def prefixEnd_6618382 : Nat := 4983230072969 + 3 ^ 40 * 6618382 * 2
def baseEnd_6618382 : Nat := 1132803707021743261229207

theorem tailTrace_6618382 : CollatzResearch.WordTrace tailWord_6618382 prefixEnd_6618382 1132803707021743261229207 := by
  unfold tailWord_6618382
  simp only [CollatzResearch.WordTrace]
  refine ⟨30174027838592477312571175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160928148472493212333712933 30174027838592477312571175)
  ·
    refine ⟨45261041757888715968856763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30174027838592477312571175 45261041757888715968856763)
    ·
      refine ⟨67891562636833073953285145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45261041757888715968856763 67891562636833073953285145)
      ·
        refine ⟨50918671977624805464963859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67891562636833073953285145 50918671977624805464963859)
        ·
          refine ⟨76378007966437208197445789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50918671977624805464963859 76378007966437208197445789)
          ·
            refine ⟨28641752987413953074042171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76378007966437208197445789 28641752987413953074042171)
            ·
              refine ⟨42962629481120929611063257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28641752987413953074042171 42962629481120929611063257)
              ·
                refine ⟨32221972110840697208297443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42962629481120929611063257 32221972110840697208297443)
                ·
                  refine ⟨48332958166261045812446165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32221972110840697208297443 48332958166261045812446165)
                  ·
                    refine ⟨1132803707021743261229207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48332958166261045812446165 1132803707021743261229207)
                    ·
                      rfl

theorem cell23_6618382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_6618382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618382 prefixEnd_6618382 := by exact prefixLift 6618382
  have htrace : WordTrace (prefixWord ++ tailWord_6618382) baseStart_6618382 baseEnd_6618382 := by
    simpa [prefixWord, tailWord_6618382, baseEnd_6618382] using wordTrace_append hprefix tailTrace_6618382
  have hstable : (prefixWord ++ tailWord_6618382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618382).length < 2 ^ (prefixWord ++ tailWord_6618382).sum := by decide
  have hdescent : baseEnd_6618382 < baseStart_6618382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618395 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 10]
def baseStart_6618395 : Nat := 118140960795 + 6618395 * 2 ^ 59
def prefixEnd_6618395 : Nat := 4983230072969 + 3 ^ 40 * 6618395 * 2
def baseEnd_6618395 : Nat := 1132805932104579410941687

theorem tailTrace_6618395 : CollatzResearch.WordTrace tailWord_6618395 prefixEnd_6618395 1132805932104579410941687 := by
  unfold tailWord_6618395
  simp only [CollatzResearch.WordTrace]
  refine ⟨241392696857692721720792639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160928464571795147813861759 241392696857692721720792639)
  ·
    refine ⟨362089045286539082581188959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241392696857692721720792639 362089045286539082581188959)
    ·
      refine ⟨543133567929808623871783439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362089045286539082581188959 543133567929808623871783439)
      ·
        refine ⟨814700351894712935807675159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543133567929808623871783439 814700351894712935807675159)
        ·
          refine ⟨1222050527842069403711512739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814700351894712935807675159 1222050527842069403711512739)
          ·
            refine ⟨1833075791763104105567269109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222050527842069403711512739 1833075791763104105567269109)
            ·
              refine ⟨171850855477791009896931479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1833075791763104105567269109 171850855477791009896931479)
              ·
                refine ⟨257776283216686514845397219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171850855477791009896931479 257776283216686514845397219)
                ·
                  refine ⟨386664424825029772268095829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257776283216686514845397219 386664424825029772268095829)
                  ·
                    refine ⟨1132805932104579410941687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 386664424825029772268095829 1132805932104579410941687)
                    ·
                      rfl

theorem cell23_6618395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 10].length) (baseStart_6618395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618395 prefixEnd_6618395 := by exact prefixLift 6618395
  have htrace : WordTrace (prefixWord ++ tailWord_6618395) baseStart_6618395 baseEnd_6618395 := by
    simpa [prefixWord, tailWord_6618395, baseEnd_6618395] using wordTrace_append hprefix tailTrace_6618395
  have hstable : (prefixWord ++ tailWord_6618395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618395).length < 2 ^ (prefixWord ++ tailWord_6618395).sum := by decide
  have hdescent : baseEnd_6618395 < baseStart_6618395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618419 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 4]
def baseStart_6618419 : Nat := 118140960795 + 6618419 * 2 ^ 59
def prefixEnd_6618419 : Nat := 4983230072969 + 3 ^ 40 * 6618419 * 2
def baseEnd_6618419 : Nat := 3398430119849446138924951

theorem tailTrace_6618419 : CollatzResearch.WordTrace tailWord_6618419 prefixEnd_6618419 3398430119849446138924951 := by
  unfold tailWord_6618419
  simp only [CollatzResearch.WordTrace]
  refine ⟨241393572209605773819666311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160929048139737182546444207 241393572209605773819666311)
  ·
    refine ⟨362090358314408660729499467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241393572209605773819666311 362090358314408660729499467)
    ·
      refine ⟨543135537471612991094249201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362090358314408660729499467 543135537471612991094249201)
      ·
        refine ⟨407351653103709743320686901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543135537471612991094249201 407351653103709743320686901)
        ·
          refine ⟨38189217478472788436314397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 407351653103709743320686901 38189217478472788436314397)
          ·
            refine ⟨14320956554427295663617899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38189217478472788436314397 14320956554427295663617899)
            ·
              refine ⟨21481434831640943495426849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14320956554427295663617899 21481434831640943495426849)
              ·
                refine ⟨16111076123730707621570137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21481434831640943495426849 16111076123730707621570137)
                ·
                  refine ⟨12083307092798030716177603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16111076123730707621570137 12083307092798030716177603)
                  ·
                    refine ⟨18124960639197046074266405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12083307092798030716177603 18124960639197046074266405)
                    ·
                      refine ⟨3398430119849446138924951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18124960639197046074266405 3398430119849446138924951)
                      ·
                        rfl

theorem cell23_6618419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_6618419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618419 prefixEnd_6618419 := by exact prefixLift 6618419
  have htrace : WordTrace (prefixWord ++ tailWord_6618419) baseStart_6618419 baseEnd_6618419 := by
    simpa [prefixWord, tailWord_6618419, baseEnd_6618419] using wordTrace_append hprefix tailTrace_6618419
  have hstable : (prefixWord ++ tailWord_6618419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618419).length < 2 ^ (prefixWord ++ tailWord_6618419).sum := by decide
  have hdescent : baseEnd_6618419 < baseStart_6618419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618519 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 4, 4]
def baseStart_6618519 : Nat := 118140960795 + 6618519 * 2 ^ 59
def prefixEnd_6618519 : Nat := 4983230072969 + 3 ^ 40 * 6618519 * 2
def baseEnd_6618519 : Nat := 1132827155971631915891497

theorem tailTrace_6618519 : CollatzResearch.WordTrace tailWord_6618519 prefixEnd_6618519 1132827155971631915891497 := by
  unfold tailWord_6618519
  simp only [CollatzResearch.WordTrace]
  refine ⟨241397219509243490898306611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160931479672828993932204407 241397219509243490898306611)
  ·
    refine ⟨362095829263865236347459917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241397219509243490898306611 362095829263865236347459917)
    ·
      refine ⟨135785935973949463630297469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362095829263865236347459917 135785935973949463630297469)
      ·
        refine ⟨50919725990231048861361551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135785935973949463630297469 50919725990231048861361551)
        ·
          refine ⟨76379588985346573292042327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50919725990231048861361551 76379588985346573292042327)
          ·
            refine ⟨114569383478019859938063491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76379588985346573292042327 114569383478019859938063491)
            ·
              refine ⟨171854075217029789907095237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114569383478019859938063491 171854075217029789907095237)
              ·
                refine ⟨32222639103193085607580357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171854075217029789907095237 32222639103193085607580357)
                ·
                  refine ⟨6041744831848703551421317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32222639103193085607580357 6041744831848703551421317)
                  ·
                    refine ⟨1132827155971631915891497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6041744831848703551421317 1132827155971631915891497)
                    ·
                      rfl

theorem cell23_6618519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_6618519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618519 prefixEnd_6618519 := by exact prefixLift 6618519
  have htrace : WordTrace (prefixWord ++ tailWord_6618519) baseStart_6618519 baseEnd_6618519 := by
    simpa [prefixWord, tailWord_6618519, baseEnd_6618519] using wordTrace_append hprefix tailTrace_6618519
  have hstable : (prefixWord ++ tailWord_6618519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618519).length < 2 ^ (prefixWord ++ tailWord_6618519).sum := by decide
  have hdescent : baseEnd_6618519 < baseStart_6618519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618553 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 1, 6]
def baseStart_6618553 : Nat := 118140960795 + 6618553 * 2 ^ 59
def prefixEnd_6618553 : Nat := 4983230072969 + 3 ^ 40 * 6618553 * 2
def baseEnd_6618553 : Nat := 1132832975419049538216445

theorem tailTrace_6618553 : CollatzResearch.WordTrace tailWord_6618553 prefixEnd_6618553 1132832975419049538216445 := by
  unfold tailWord_6618553
  simp only [CollatzResearch.WordTrace]
  refine ⟨241398459591120314705044313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160932306394080209803362875 241398459591120314705044313)
  ·
    refine ⟨181048844693340236028783235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241398459591120314705044313 181048844693340236028783235)
    ·
      refine ⟨271573267040010354043174853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181048844693340236028783235 271573267040010354043174853)
      ·
        refine ⟨50919987570001941383095285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271573267040010354043174853 50919987570001941383095285)
        ·
          refine ⟨4773748834687682004665183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50919987570001941383095285 4773748834687682004665183)
          ·
            refine ⟨7160623252031523006997775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773748834687682004665183 7160623252031523006997775)
            ·
              refine ⟨10740934878047284510496663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160623252031523006997775 10740934878047284510496663)
              ·
                refine ⟨16111402317070926765744995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10740934878047284510496663 16111402317070926765744995)
                ·
                  refine ⟨24167103475606390148617493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16111402317070926765744995 24167103475606390148617493)
                  ·
                    refine ⟨1132832975419049538216445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24167103475606390148617493 1132832975419049538216445)
                    ·
                      rfl

theorem cell23_6618553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 6].length) (baseStart_6618553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618553 prefixEnd_6618553 := by exact prefixLift 6618553
  have htrace : WordTrace (prefixWord ++ tailWord_6618553) baseStart_6618553 baseEnd_6618553 := by
    simpa [prefixWord, tailWord_6618553, baseEnd_6618553] using wordTrace_append hprefix tailTrace_6618553
  have hstable : (prefixWord ++ tailWord_6618553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618553).length < 2 ^ (prefixWord ++ tailWord_6618553).sum := by decide
  have hdescent : baseEnd_6618553 < baseStart_6618553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618556 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6618556 : Nat := 118140960795 + 6618556 * 2 ^ 59
def prefixEnd_6618556 : Nat := 4983230072969 + 3 ^ 40 * 6618556 * 2
def baseEnd_6618556 : Nat := 3398500466699112102911821

theorem tailTrace_6618556 : CollatzResearch.WordTrace tailWord_6618556 prefixEnd_6618556 3398500466699112102911821 := by
  unfold tailWord_6618556
  simp only [CollatzResearch.WordTrace]
  refine ⟨120699284505054723108701761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160932379340072964144935681 120699284505054723108701761)
  ·
    refine ⟨90524463378791042331526321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120699284505054723108701761 90524463378791042331526321)
    ·
      refine ⟨67893347534093281748644741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90524463378791042331526321 67893347534093281748644741)
      ·
        refine ⟨12730002662642490327870889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67893347534093281748644741 12730002662642490327870889)
        ·
          refine ⟨9547501996981867745903167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12730002662642490327870889 9547501996981867745903167)
          ·
            refine ⟨14321252995472801618854751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9547501996981867745903167 14321252995472801618854751)
            ·
              refine ⟨21481879493209202428282127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14321252995472801618854751 21481879493209202428282127)
              ·
                refine ⟨32222819239813803642423191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21481879493209202428282127 32222819239813803642423191)
                ·
                  refine ⟨48334228859720705463634787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32222819239813803642423191 48334228859720705463634787)
                  ·
                    refine ⟨72501343289581058195452181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48334228859720705463634787 72501343289581058195452181)
                    ·
                      refine ⟨3398500466699112102911821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72501343289581058195452181 3398500466699112102911821)
                      ·
                        rfl

theorem cell23_6618556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6618556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618556 prefixEnd_6618556 := by exact prefixLift 6618556
  have htrace : WordTrace (prefixWord ++ tailWord_6618556) baseStart_6618556 baseEnd_6618556 := by
    simpa [prefixWord, tailWord_6618556, baseEnd_6618556] using wordTrace_append hprefix tailTrace_6618556
  have hstable : (prefixWord ++ tailWord_6618556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618556).length < 2 ^ (prefixWord ++ tailWord_6618556).sum := by decide
  have hdescent : baseEnd_6618556 < baseStart_6618556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618610 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_6618610 : Nat := 118140960795 + 6618610 * 2 ^ 59
def prefixEnd_6618610 : Nat := 4983230072969 + 3 ^ 40 * 6618610 * 2
def baseEnd_6618610 : Nat := 3398528194654454891636573

theorem tailTrace_6618610 : CollatzResearch.WordTrace tailWord_6618610 prefixEnd_6618610 3398528194654454891636573 := by
  unfold tailWord_6618610
  simp only [CollatzResearch.WordTrace]
  refine ⟨60350134637978453359967321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160933692367942542293246189 60350134637978453359967321)
  ·
    refine ⟨45262600978483840019975491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60350134637978453359967321 45262600978483840019975491)
    ·
      refine ⟨67893901467725760029963237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45262600978483840019975491 67893901467725760029963237)
      ·
        refine ⟨12730106525198580005618107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67893901467725760029963237 12730106525198580005618107)
        ·
          refine ⟨19095159787797870008427161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12730106525198580005618107 19095159787797870008427161)
          ·
            refine ⟨14321369840848402506320371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19095159787797870008427161 14321369840848402506320371)
            ·
              refine ⟨21482054761272603759480557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14321369840848402506320371 21482054761272603759480557)
              ·
                refine ⟨8055770535477226409805209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21482054761272603759480557 8055770535477226409805209)
                ·
                  refine ⟨6041827901607919807353907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8055770535477226409805209 6041827901607919807353907)
                  ·
                    refine ⟨9062741852411879711030861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6041827901607919807353907 9062741852411879711030861)
                    ·
                      refine ⟨3398528194654454891636573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9062741852411879711030861 3398528194654454891636573)
                      ·
                        rfl

theorem cell23_6618610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_6618610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618610 prefixEnd_6618610 := by exact prefixLift 6618610
  have htrace : WordTrace (prefixWord ++ tailWord_6618610) baseStart_6618610 baseEnd_6618610 := by
    simpa [prefixWord, tailWord_6618610, baseEnd_6618610] using wordTrace_append hprefix tailTrace_6618610
  have hstable : (prefixWord ++ tailWord_6618610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618610).length < 2 ^ (prefixWord ++ tailWord_6618610).sum := by decide
  have hdescent : baseEnd_6618610 < baseStart_6618610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618619 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 3]
def baseStart_6618619 : Nat := 118140960795 + 6618619 * 2 ^ 59
def prefixEnd_6618619 : Nat := 4983230072969 + 3 ^ 40 * 6618619 * 2
def baseEnd_6618619 : Nat := 3398532815980345356424031

theorem tailTrace_6618619 : CollatzResearch.WordTrace tailWord_6618619 prefixEnd_6618619 3398532815980345356424031 := by
  unfold tailWord_6618619
  simp only [CollatzResearch.WordTrace]
  refine ⟨241400866808881207976946911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160933911205920805317964607 241400866808881207976946911)
  ·
    refine ⟨362101300213321811965420367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241400866808881207976946911 362101300213321811965420367)
    ·
      refine ⟨543151950319982717948130551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362101300213321811965420367 543151950319982717948130551)
      ·
        refine ⟨814727925479974076922195827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543151950319982717948130551 814727925479974076922195827)
        ·
          refine ⟨1222091888219961115383293741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814727925479974076922195827 1222091888219961115383293741)
          ·
            refine ⟨458284458082485418268735153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1222091888219961115383293741 458284458082485418268735153)
            ·
              refine ⟨343713343561864063701551365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458284458082485418268735153 343713343561864063701551365)
              ·
                refine ⟨64446251917849511944040881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343713343561864063701551365 64446251917849511944040881)
                ·
                  refine ⟨48334688938387133958030661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64446251917849511944040881 48334688938387133958030661)
                  ·
                    refine ⟨9062754175947587617130749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48334688938387133958030661 9062754175947587617130749)
                    ·
                      refine ⟨3398532815980345356424031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9062754175947587617130749 3398532815980345356424031)
                      ·
                        rfl

theorem cell23_6618619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 3].length) (baseStart_6618619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618619 prefixEnd_6618619 := by exact prefixLift 6618619
  have htrace : WordTrace (prefixWord ++ tailWord_6618619) baseStart_6618619 baseEnd_6618619 := by
    simpa [prefixWord, tailWord_6618619, baseEnd_6618619] using wordTrace_append hprefix tailTrace_6618619
  have hstable : (prefixWord ++ tailWord_6618619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618619).length < 2 ^ (prefixWord ++ tailWord_6618619).sum := by decide
  have hdescent : baseEnd_6618619 < baseStart_6618619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618629 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_6618629 : Nat := 118140960795 + 6618629 * 2 ^ 59
def prefixEnd_6618629 : Nat := 4983230072969 + 3 ^ 40 * 6618629 * 2
def baseEnd_6618629 : Nat := 3398537950786890317298985

theorem tailTrace_6618629 : CollatzResearch.WordTrace tailWord_6618629 prefixEnd_6618629 3398537950786890317298985 := by
  unfold tailWord_6618629
  simp only [CollatzResearch.WordTrace]
  refine ⟨241401231538844979684810941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160934154359229986456540627 241401231538844979684810941)
  ·
    refine ⟨90525461827066867381804103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241401231538844979684810941 90525461827066867381804103)
    ·
      refine ⟨135788192740600301072706155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90525461827066867381804103 135788192740600301072706155)
      ·
        refine ⟨203682289110900451609059233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135788192740600301072706155 203682289110900451609059233)
        ·
          refine ⟨152761716833175338706794425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203682289110900451609059233 152761716833175338706794425)
          ·
            refine ⟨114571287624881504030095819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152761716833175338706794425 114571287624881504030095819)
            ·
              refine ⟨171856931437322256045143729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114571287624881504030095819 171856931437322256045143729)
              ·
                refine ⟨128892698577991692033857797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171856931437322256045143729 128892698577991692033857797)
                ·
                  refine ⟨24167380983373442256348337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128892698577991692033857797 24167380983373442256348337)
                  ·
                    refine ⟨18125535737530081692261253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24167380983373442256348337 18125535737530081692261253)
                    ·
                      refine ⟨3398537950786890317298985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18125535737530081692261253 3398537950786890317298985)
                      ·
                        rfl

theorem cell23_6618629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_6618629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618629 prefixEnd_6618629 := by exact prefixLift 6618629
  have htrace : WordTrace (prefixWord ++ tailWord_6618629) baseStart_6618629 baseEnd_6618629 := by
    simpa [prefixWord, tailWord_6618629, baseEnd_6618629] using wordTrace_append hprefix tailTrace_6618629
  have hstable : (prefixWord ++ tailWord_6618629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618629).length < 2 ^ (prefixWord ++ tailWord_6618629).sum := by decide
  have hdescent : baseEnd_6618629 < baseStart_6618629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618701 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_6618701 : Nat := 118140960795 + 6618701 * 2 ^ 59
def prefixEnd_6618701 : Nat := 4983230072969 + 3 ^ 40 * 6618701 * 2
def baseEnd_6618701 : Nat := 3398574921394014035598655

theorem tailTrace_6618701 : CollatzResearch.WordTrace tailWord_6618701 prefixEnd_6618701 3398574921394014035598655 := by
  unfold tailWord_6618701
  simp only [CollatzResearch.WordTrace]
  refine ⟨241403857594584135981431957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160935905063056090654287971 241403857594584135981431957)
  ·
    refine ⟨11315805824746131374129623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 241403857594584135981431957 11315805824746131374129623)
    ·
      refine ⟨16973708737119197061194435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315805824746131374129623 16973708737119197061194435)
      ·
        refine ⟨25460563105678795591791653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16973708737119197061194435 25460563105678795591791653)
        ·
          refine ⟨4773855582314774173460935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25460563105678795591791653 4773855582314774173460935)
          ·
            refine ⟨7160783373472161260191403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773855582314774173460935 7160783373472161260191403)
            ·
              refine ⟨10741175060208241890287105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160783373472161260191403 10741175060208241890287105)
              ·
                refine ⟨8055881295156181417715329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10741175060208241890287105 8055881295156181417715329)
                ·
                  refine ⟨6041910971367136063286497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8055881295156181417715329 6041910971367136063286497)
                  ·
                    refine ⟨4531433228525352047464873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6041910971367136063286497 4531433228525352047464873)
                    ·
                      refine ⟨3398574921394014035598655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4531433228525352047464873 3398574921394014035598655)
                      ·
                        rfl

theorem cell23_6618701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_6618701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618701 prefixEnd_6618701 := by exact prefixLift 6618701
  have htrace : WordTrace (prefixWord ++ tailWord_6618701) baseStart_6618701 baseEnd_6618701 := by
    simpa [prefixWord, tailWord_6618701, baseEnd_6618701] using wordTrace_append hprefix tailTrace_6618701
  have hstable : (prefixWord ++ tailWord_6618701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618701).length < 2 ^ (prefixWord ++ tailWord_6618701).sum := by decide
  have hdescent : baseEnd_6618701 < baseStart_6618701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618723 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 2, 4, 2]
def baseStart_6618723 : Nat := 118140960795 + 6618723 * 2 ^ 59
def prefixEnd_6618723 : Nat := 4983230072969 + 3 ^ 40 * 6618723 * 2
def baseEnd_6618723 : Nat := 3398586217968412949523553

theorem tailTrace_6618723 : CollatzResearch.WordTrace tailWord_6618723 prefixEnd_6618723 3398586217968412949523553 := by
  unfold tailWord_6618723
  simp only [CollatzResearch.WordTrace]
  refine ⟨241404660000504433738732823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160936440000336289159155215 241404660000504433738732823)
  ·
    refine ⟨362106990000756650608099235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241404660000504433738732823 362106990000756650608099235)
    ·
      refine ⟨543160485001134975912148853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362106990000756650608099235 543160485001134975912148853)
      ·
        refine ⟨50921295468856403991763955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 543160485001134975912148853 50921295468856403991763955)
        ·
          refine ⟨76381943203284605987645933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50921295468856403991763955 76381943203284605987645933)
          ·
            refine ⟨28643228701231727245367225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76381943203284605987645933 28643228701231727245367225)
            ·
              refine ⟨21482421525923795434025419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28643228701231727245367225 21482421525923795434025419)
              ·
                refine ⟨32223632288885693151038129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21482421525923795434025419 32223632288885693151038129)
                ·
                  refine ⟨24167724216664269863278597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32223632288885693151038129 24167724216664269863278597)
                  ·
                    refine ⟨4531448290624550599364737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24167724216664269863278597 4531448290624550599364737)
                    ·
                      refine ⟨3398586217968412949523553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4531448290624550599364737 3398586217968412949523553)
                      ·
                        rfl

theorem cell23_6618723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_6618723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618723 prefixEnd_6618723 := by exact prefixLift 6618723
  have htrace : WordTrace (prefixWord ++ tailWord_6618723) baseStart_6618723 baseEnd_6618723 := by
    simpa [prefixWord, tailWord_6618723, baseEnd_6618723] using wordTrace_append hprefix tailTrace_6618723
  have hstable : (prefixWord ++ tailWord_6618723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618723).length < 2 ^ (prefixWord ++ tailWord_6618723).sum := by decide
  have hdescent : baseEnd_6618723 < baseStart_6618723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618810 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_6618810 : Nat := 118140960795 + 6618810 * 2 ^ 59
def prefixEnd_6618810 : Nat := 4983230072969 + 3 ^ 40 * 6618810 * 2
def baseEnd_6618810 : Nat := 1132876963595118036378551

theorem tailTrace_6618810 : CollatzResearch.WordTrace tailWord_6618810 prefixEnd_6618810 1132876963595118036378551 := by
  unfold tailWord_6618810
  simp only [CollatzResearch.WordTrace]
  refine ⟨60351958287797311899287471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160938555434126165064766589 60351958287797311899287471)
  ·
    refine ⟨90527937431695967848931207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60351958287797311899287471 90527937431695967848931207)
    ·
      refine ⟨135791906147543951773396811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90527937431695967848931207 135791906147543951773396811)
      ·
        refine ⟨203687859221315927660095217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135791906147543951773396811 203687859221315927660095217)
        ·
          refine ⟨152765894415986945745071413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203687859221315927660095217 152765894415986945745071413)
          ·
            refine ⟨14321802601498776163600445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152765894415986945745071413 14321802601498776163600445)
            ·
              refine ⟨5370675975562041061350167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14321802601498776163600445 5370675975562041061350167)
              ·
                refine ⟨8056013963343061592025251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370675975562041061350167 8056013963343061592025251)
                ·
                  refine ⟨12084020945014592388037877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8056013963343061592025251 12084020945014592388037877)
                  ·
                    refine ⟨1132876963595118036378551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12084020945014592388037877 1132876963595118036378551)
                    ·
                      rfl

theorem cell23_6618810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_6618810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618810 prefixEnd_6618810 := by exact prefixLift 6618810
  have htrace : WordTrace (prefixWord ++ tailWord_6618810) baseStart_6618810 baseEnd_6618810 := by
    simpa [prefixWord, tailWord_6618810, baseEnd_6618810] using wordTrace_append hprefix tailTrace_6618810
  have hstable : (prefixWord ++ tailWord_6618810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618810).length < 2 ^ (prefixWord ++ tailWord_6618810).sum := by decide
  have hdescent : baseEnd_6618810 < baseStart_6618810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618833 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_6618833 : Nat := 118140960795 + 6618833 * 2 ^ 59
def prefixEnd_6618833 : Nat := 4983230072969 + 3 ^ 40 * 6618833 * 2
def baseEnd_6618833 : Nat := 3398642700840407519148047

theorem tailTrace_6618833 : CollatzResearch.WordTrace tailWord_6618833 prefixEnd_6618833 3398642700840407519148047 := by
  unfold tailWord_6618833
  simp only [CollatzResearch.WordTrace]
  refine ⟨241408672030105922525237153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160939114686737281683491435 241408672030105922525237153)
  ·
    refine ⟨181056504022579441893927865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241408672030105922525237153 181056504022579441893927865)
    ·
      refine ⟨135792378016934581420445899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181056504022579441893927865 135792378016934581420445899)
      ·
        refine ⟨203688567025401872130668849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135792378016934581420445899 203688567025401872130668849)
        ·
          refine ⟨152766425269051404098001637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203688567025401872130668849 152766425269051404098001637)
          ·
            refine ⟨28643704737947138268375307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152766425269051404098001637 28643704737947138268375307)
            ·
              refine ⟨42965557106920707402562961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28643704737947138268375307 42965557106920707402562961)
              ·
                refine ⟨32224167830190530551922221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42965557106920707402562961 32224167830190530551922221)
                ·
                  refine ⟨12084062936321448956970833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32224167830190530551922221 12084062936321448956970833)
                  ·
                    refine ⟨9063047202241086717728125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12084062936321448956970833 9063047202241086717728125)
                    ·
                      refine ⟨3398642700840407519148047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9063047202241086717728125 3398642700840407519148047)
                      ·
                        rfl

theorem cell23_6618833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_6618833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618833 prefixEnd_6618833 := by exact prefixLift 6618833
  have htrace : WordTrace (prefixWord ++ tailWord_6618833) baseStart_6618833 baseEnd_6618833 := by
    simpa [prefixWord, tailWord_6618833, baseEnd_6618833] using wordTrace_append hprefix tailTrace_6618833
  have hstable : (prefixWord ++ tailWord_6618833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618833).length < 2 ^ (prefixWord ++ tailWord_6618833).sum := by decide
  have hdescent : baseEnd_6618833 < baseStart_6618833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618853 : List Nat := [1, 3, 1, 4, 1, 1, 5, 7]
def baseStart_6618853 : Nat := 118140960795 + 6618853 * 2 ^ 59
def prefixEnd_6618853 : Nat := 4983230072969 + 3 ^ 40 * 6618853 * 2
def baseEnd_6618853 : Nat := 125876035942722127440665

theorem tailTrace_6618853 : CollatzResearch.WordTrace tailWord_6618853 prefixEnd_6618853 125876035942722127440665 := by
  unfold tailWord_6618853
  simp only [CollatzResearch.WordTrace]
  refine ⟨241409401490033465940965213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160939600993355643960643475 241409401490033465940965213)
  ·
    refine ⟨90528525558762549727861955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241409401490033465940965213 90528525558762549727861955)
    ·
      refine ⟨135792788338143824591792933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90528525558762549727861955 135792788338143824591792933)
      ·
        refine ⟨25461147813401967110961175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135792788338143824591792933 25461147813401967110961175)
        ·
          refine ⟨38191721720102950666441763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25461147813401967110961175 38191721720102950666441763)
          ·
            refine ⟨57287582580154425999662645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38191721720102950666441763 57287582580154425999662645)
            ·
              refine ⟨5370710866889477437468373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57287582580154425999662645 5370710866889477437468373)
              ·
                refine ⟨125876035942722127440665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5370710866889477437468373 125876035942722127440665)
                ·
                  rfl

theorem cell23_6618853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 7].length) (baseStart_6618853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618853 prefixEnd_6618853 := by exact prefixLift 6618853
  have htrace : WordTrace (prefixWord ++ tailWord_6618853) baseStart_6618853 baseEnd_6618853 := by
    simpa [prefixWord, tailWord_6618853, baseEnd_6618853] using wordTrace_append hprefix tailTrace_6618853
  have hstable : (prefixWord ++ tailWord_6618853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618853).length < 2 ^ (prefixWord ++ tailWord_6618853).sum := by decide
  have hdescent : baseEnd_6618853 < baseStart_6618853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618863 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 3]
def baseStart_6618863 : Nat := 118140960795 + 6618863 * 2 ^ 59
def prefixEnd_6618863 : Nat := 4983230072969 + 3 ^ 40 * 6618863 * 2
def baseEnd_6618863 : Nat := 3398658105260042401772909

theorem tailTrace_6618863 : CollatzResearch.WordTrace tailWord_6618863 prefixEnd_6618863 3398658105260042401772909 := by
  unfold tailWord_6618863
  simp only [CollatzResearch.WordTrace]
  refine ⟨241409766219997237648829243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160939844146664825099219495 241409766219997237648829243)
  ·
    refine ⟨362114649329995856473243865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241409766219997237648829243 362114649329995856473243865)
    ·
      refine ⟨271585986997496892354932899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362114649329995856473243865 271585986997496892354932899)
      ·
        refine ⟨407378980496245338532399349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271585986997496892354932899 407378980496245338532399349)
        ·
          refine ⟨38191779421523000487412439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 407378980496245338532399349 38191779421523000487412439)
          ·
            refine ⟨57287669132284500731118659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38191779421523000487412439 57287669132284500731118659)
            ·
              refine ⟨85931503698426751096677989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57287669132284500731118659 85931503698426751096677989)
              ·
                refine ⟨16112156943455015830627123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85931503698426751096677989 16112156943455015830627123)
                ·
                  refine ⟨24168235415182523745940685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16112156943455015830627123 24168235415182523745940685)
                  ·
                    refine ⟨9063088280693446404727757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24168235415182523745940685 9063088280693446404727757)
                    ·
                      refine ⟨3398658105260042401772909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9063088280693446404727757 3398658105260042401772909)
                      ·
                        rfl

theorem cell23_6618863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_6618863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618863 prefixEnd_6618863 := by exact prefixLift 6618863
  have htrace : WordTrace (prefixWord ++ tailWord_6618863) baseStart_6618863 baseEnd_6618863 := by
    simpa [prefixWord, tailWord_6618863, baseEnd_6618863] using wordTrace_append hprefix tailTrace_6618863
  have hstable : (prefixWord ++ tailWord_6618863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618863).length < 2 ^ (prefixWord ++ tailWord_6618863).sum := by decide
  have hdescent : baseEnd_6618863 < baseStart_6618863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618953 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 3]
def baseStart_6618953 : Nat := 118140960795 + 6618953 * 2 ^ 59
def prefixEnd_6618953 : Nat := 4983230072969 + 3 ^ 40 * 6618953 * 2
def baseEnd_6618953 : Nat := 3398704318518947049647495

theorem tailTrace_6618953 : CollatzResearch.WordTrace tailWord_6618953 prefixEnd_6618953 3398704318518947049647495 := by
  unfold tailWord_6618953
  simp only [CollatzResearch.WordTrace]
  refine ⟨241413048789671183019605513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160942032526447455346403675 241413048789671183019605513)
  ·
    refine ⟨181059786592253387264704135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241413048789671183019605513 181059786592253387264704135)
    ·
      refine ⟨271589679888380080897056203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181059786592253387264704135 271589679888380080897056203)
      ·
        refine ⟨407384519832570121345584305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271589679888380080897056203 407384519832570121345584305)
        ·
          refine ⟨305538389874427591009188229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407384519832570121345584305 305538389874427591009188229)
          ·
            refine ⟨57288448101455173314222793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305538389874427591009188229 57288448101455173314222793)
            ·
              refine ⟨42966336076091379985667095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57288448101455173314222793 42966336076091379985667095)
              ·
                refine ⟨64449504114137069978500643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42966336076091379985667095 64449504114137069978500643)
                ·
                  refine ⟨96674256171205604967750965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64449504114137069978500643 96674256171205604967750965)
                  ·
                    refine ⟨9063211516050525465726653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96674256171205604967750965 9063211516050525465726653)
                    ·
                      refine ⟨3398704318518947049647495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9063211516050525465726653 3398704318518947049647495)
                      ·
                        rfl

theorem cell23_6618953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_6618953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618953 prefixEnd_6618953 := by exact prefixLift 6618953
  have htrace : WordTrace (prefixWord ++ tailWord_6618953) baseStart_6618953 baseEnd_6618953 := by
    simpa [prefixWord, tailWord_6618953, baseEnd_6618953] using wordTrace_append hprefix tailTrace_6618953
  have hstable : (prefixWord ++ tailWord_6618953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618953).length < 2 ^ (prefixWord ++ tailWord_6618953).sum := by decide
  have hdescent : baseEnd_6618953 < baseStart_6618953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6618983 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_6618983 : Nat := 118140960795 + 6618983 * 2 ^ 59
def prefixEnd_6618983 : Nat := 4983230072969 + 3 ^ 40 * 6618983 * 2
def baseEnd_6618983 : Nat := 3398719722938581932272357

theorem tailTrace_6618983 : CollatzResearch.WordTrace tailWord_6618983 prefixEnd_6618983 3398719722938581932272357 := by
  unfold tailWord_6618983
  simp only [CollatzResearch.WordTrace]
  refine ⟨241414142979562498143197603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160942761986374998762131735 241414142979562498143197603)
  ·
    refine ⟨362121214469343747214796405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241414142979562498143197603 362121214469343747214796405)
    ·
      refine ⟨33948863856500976301387163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 362121214469343747214796405 33948863856500976301387163)
      ·
        refine ⟨50923295784751464452080745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33948863856500976301387163 50923295784751464452080745)
        ·
          refine ⟨38192471838563598339060559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50923295784751464452080745 38192471838563598339060559)
          ·
            refine ⟨57288707757845397508590839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38192471838563598339060559 57288707757845397508590839)
            ·
              refine ⟨85933061636768096262886259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57288707757845397508590839 85933061636768096262886259)
              ·
                refine ⟨128899592455152144394329389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85933061636768096262886259 128899592455152144394329389)
                ·
                  refine ⟨48337347170682054147873521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128899592455152144394329389 48337347170682054147873521)
                  ·
                    refine ⟨36253010378011540610905141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48337347170682054147873521 36253010378011540610905141)
                    ·
                      refine ⟨3398719722938581932272357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36253010378011540610905141 3398719722938581932272357)
                      ·
                        rfl

theorem cell23_6618983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_6618983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6618983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6618983 prefixEnd_6618983 := by exact prefixLift 6618983
  have htrace : WordTrace (prefixWord ++ tailWord_6618983) baseStart_6618983 baseEnd_6618983 := by
    simpa [prefixWord, tailWord_6618983, baseEnd_6618983] using wordTrace_append hprefix tailTrace_6618983
  have hstable : (prefixWord ++ tailWord_6618983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6618983).length < 2 ^ (prefixWord ++ tailWord_6618983).sum := by decide
  have hdescent : baseEnd_6618983 < baseStart_6618983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6618983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619087 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 2, 3, 2]
def baseStart_6619087 : Nat := 118140960795 + 6619087 * 2 ^ 59
def prefixEnd_6619087 : Nat := 4983230072969 + 3 ^ 40 * 6619087 * 2
def baseEnd_6619087 : Nat := 3398773124926649525371879

theorem tailTrace_6619087 : CollatzResearch.WordTrace tailWord_6619087 prefixEnd_6619087 3398773124926649525371879 := by
  unfold tailWord_6619087
  simp only [CollatzResearch.WordTrace]
  refine ⟨241417936171185723904983515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160945290780790482603322343 241417936171185723904983515)
  ·
    refine ⟨362126904256778585857475273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241417936171185723904983515 362126904256778585857475273)
    ·
      refine ⟨271595178192583939393106455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362126904256778585857475273 271595178192583939393106455)
      ·
        refine ⟨407392767288875909089659683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271595178192583939393106455 407392767288875909089659683)
        ·
          refine ⟨611089150933313863634489525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407392767288875909089659683 611089150933313863634489525)
          ·
            refine ⟨57289607899998174715733393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 611089150933313863634489525 57289607899998174715733393)
            ·
              refine ⟨42967205924998631036800045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57289607899998174715733393 42967205924998631036800045)
              ·
                refine ⟨16112702221874486638800017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42967205924998631036800045 16112702221874486638800017)
                ·
                  refine ⟨12084526666405864979100013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16112702221874486638800017 12084526666405864979100013)
                  ·
                    refine ⟨4531697499902199367162505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12084526666405864979100013 4531697499902199367162505)
                    ·
                      refine ⟨3398773124926649525371879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4531697499902199367162505 3398773124926649525371879)
                      ·
                        rfl

theorem cell23_6619087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 3, 2].length) (baseStart_6619087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619087 prefixEnd_6619087 := by exact prefixLift 6619087
  have htrace : WordTrace (prefixWord ++ tailWord_6619087) baseStart_6619087 baseEnd_6619087 := by
    simpa [prefixWord, tailWord_6619087, baseEnd_6619087] using wordTrace_append hprefix tailTrace_6619087
  have hstable : (prefixWord ++ tailWord_6619087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619087).length < 2 ^ (prefixWord ++ tailWord_6619087).sum := by decide
  have hdescent : baseEnd_6619087 < baseStart_6619087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619111 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_6619111 : Nat := 118140960795 + 6619111 * 2 ^ 59
def prefixEnd_6619111 : Nat := 4983230072969 + 3 ^ 40 * 6619111 * 2
def baseEnd_6619111 : Nat := 3398785448462357431471769

theorem tailTrace_6619111 : CollatzResearch.WordTrace tailWord_6619111 prefixEnd_6619111 3398785448462357431471769 := by
  unfold tailWord_6619111
  simp only [CollatzResearch.WordTrace]
  refine ⟨241418811523098776003857187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160945874348732517335904791 241418811523098776003857187)
  ·
    refine ⟨362128217284648164005785781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241418811523098776003857187 362128217284648164005785781)
    ·
      refine ⟨33949520370435765375542417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 362128217284648164005785781 33949520370435765375542417)
      ·
        refine ⟨25462140277826824031656813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33949520370435765375542417 25462140277826824031656813)
        ·
          refine ⟨9548302604185059011871305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25462140277826824031656813 9548302604185059011871305)
          ·
            refine ⟨7161226953138794258903479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9548302604185059011871305 7161226953138794258903479)
            ·
              refine ⟨10741840429708191388355219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161226953138794258903479 10741840429708191388355219)
              ·
                refine ⟨16112760644562287082532829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10741840429708191388355219 16112760644562287082532829)
                ·
                  refine ⟨6042285241710857655949811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16112760644562287082532829 6042285241710857655949811)
                  ·
                    refine ⟨9063427862566286483924717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6042285241710857655949811 9063427862566286483924717)
                    ·
                      refine ⟨3398785448462357431471769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9063427862566286483924717 3398785448462357431471769)
                      ·
                        rfl

theorem cell23_6619111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_6619111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619111 prefixEnd_6619111 := by exact prefixLift 6619111
  have htrace : WordTrace (prefixWord ++ tailWord_6619111) baseStart_6619111 baseEnd_6619111 := by
    simpa [prefixWord, tailWord_6619111, baseEnd_6619111] using wordTrace_append hprefix tailTrace_6619111
  have hstable : (prefixWord ++ tailWord_6619111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619111).length < 2 ^ (prefixWord ++ tailWord_6619111).sum := by decide
  have hdescent : baseEnd_6619111 < baseStart_6619111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619120 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_6619120 : Nat := 118140960795 + 6619120 * 2 ^ 59
def prefixEnd_6619120 : Nat := 4983230072969 + 3 ^ 40 * 6619120 * 2
def baseEnd_6619120 : Nat := 3398790069788247896259227

theorem tailTrace_6619120 : CollatzResearch.WordTrace tailWord_6619120 prefixEnd_6619120 3398790069788247896259227 := by
  unfold tailWord_6619120
  simp only [CollatzResearch.WordTrace]
  refine ⟨120709569890033085270467407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160946093186710780360623209 120709569890033085270467407)
  ·
    refine ⟨181064354835049627905701111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120709569890033085270467407 181064354835049627905701111)
    ·
      refine ⟨271596532252574441858551667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181064354835049627905701111 271596532252574441858551667)
      ·
        refine ⟨407394798378861662787827501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271596532252574441858551667 407394798378861662787827501)
        ·
          refine ⟨152773049392073123545435313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407394798378861662787827501 152773049392073123545435313)
          ·
            refine ⟨114579787044054842659076485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152773049392073123545435313 114579787044054842659076485)
            ·
              refine ⟨21483710070760282998576841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114579787044054842659076485 21483710070760282998576841)
              ·
                refine ⟨16112782553070212248932631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21483710070760282998576841 16112782553070212248932631)
                ·
                  refine ⟨24169173829605318373398947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16112782553070212248932631 24169173829605318373398947)
                  ·
                    refine ⟨36253760744407977560098421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24169173829605318373398947 36253760744407977560098421)
                    ·
                      refine ⟨3398790069788247896259227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36253760744407977560098421 3398790069788247896259227)
                      ·
                        rfl

theorem cell23_6619120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_6619120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619120 prefixEnd_6619120 := by exact prefixLift 6619120
  have htrace : WordTrace (prefixWord ++ tailWord_6619120) baseStart_6619120 baseEnd_6619120 := by
    simpa [prefixWord, tailWord_6619120, baseEnd_6619120] using wordTrace_append hprefix tailTrace_6619120
  have hstable : (prefixWord ++ tailWord_6619120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619120).length < 2 ^ (prefixWord ++ tailWord_6619120).sum := by decide
  have hdescent : baseEnd_6619120 < baseStart_6619120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619134 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6619134 : Nat := 118140960795 + 6619134 * 2 ^ 59
def prefixEnd_6619134 : Nat := 4983230072969 + 3 ^ 40 * 6619134 * 2
def baseEnd_6619134 : Nat := 3398797258517410841484163

theorem tailTrace_6619134 : CollatzResearch.WordTrace tailWord_6619134 prefixEnd_6619134 3398797258517410841484163 := by
  unfold tailWord_6619134
  simp only [CollatzResearch.WordTrace]
  refine ⟨30177456300251931366493057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160946433601343633954629637 30177456300251931366493057)
  ·
    refine ⟨22633092225188948524869793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30177456300251931366493057 22633092225188948524869793)
    ·
      refine ⟨16974819168891711393652345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22633092225188948524869793 16974819168891711393652345)
      ·
        refine ⟨12731114376668783545239259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16974819168891711393652345 12731114376668783545239259)
        ·
          refine ⟨19096671565003175317858889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12731114376668783545239259 19096671565003175317858889)
          ·
            refine ⟨14322503673752381488394167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19096671565003175317858889 14322503673752381488394167)
            ·
              refine ⟨21483755510628572232591251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14322503673752381488394167 21483755510628572232591251)
              ·
                refine ⟨32225633265942858348886877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21483755510628572232591251 32225633265942858348886877)
                ·
                  refine ⟨12084612474728571880832579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32225633265942858348886877 12084612474728571880832579)
                  ·
                    refine ⟨18126918712092857821248869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12084612474728571880832579 18126918712092857821248869)
                    ·
                      refine ⟨3398797258517410841484163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18126918712092857821248869 3398797258517410841484163)
                      ·
                        rfl

theorem cell23_6619134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6619134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619134 prefixEnd_6619134 := by exact prefixLift 6619134
  have htrace : WordTrace (prefixWord ++ tailWord_6619134) baseStart_6619134 baseEnd_6619134 := by
    simpa [prefixWord, tailWord_6619134, baseEnd_6619134] using wordTrace_append hprefix tailTrace_6619134
  have hstable : (prefixWord ++ tailWord_6619134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619134).length < 2 ^ (prefixWord ++ tailWord_6619134).sum := by decide
  have hdescent : baseEnd_6619134 < baseStart_6619134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619137 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_6619137 : Nat := 118140960795 + 6619137 * 2 ^ 59
def prefixEnd_6619137 : Nat := 4983230072969 + 3 ^ 40 * 6619137 * 2
def baseEnd_6619137 : Nat := 3398798798959374329746649

theorem tailTrace_6619137 : CollatzResearch.WordTrace tailWord_6619137 prefixEnd_6619137 3398798798959374329746649 := by
  unfold tailWord_6619137
  simp only [CollatzResearch.WordTrace]
  refine ⟨241419759821004582444303665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160946506547336388296202443 241419759821004582444303665)
  ·
    refine ⟨181064819865753436833227749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241419759821004582444303665 181064819865753436833227749)
    ·
      refine ⟨33949653724828769406230203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181064819865753436833227749 33949653724828769406230203)
      ·
        refine ⟨50924480587243154109345305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33949653724828769406230203 50924480587243154109345305)
        ·
          refine ⟨38193360440432365582008979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50924480587243154109345305 38193360440432365582008979)
          ·
            refine ⟨57290040660648548373013469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38193360440432365582008979 57290040660648548373013469)
            ·
              refine ⟨21483765247743205639880051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57290040660648548373013469 21483765247743205639880051)
              ·
                refine ⟨32225647871614808459820077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21483765247743205639880051 32225647871614808459820077)
                ·
                  refine ⟨12084617951855553172432529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32225647871614808459820077 12084617951855553172432529)
                  ·
                    refine ⟨9063463463891664879324397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12084617951855553172432529 9063463463891664879324397)
                    ·
                      refine ⟨3398798798959374329746649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9063463463891664879324397 3398798798959374329746649)
                      ·
                        rfl

theorem cell23_6619137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_6619137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619137 prefixEnd_6619137 := by exact prefixLift 6619137
  have htrace : WordTrace (prefixWord ++ tailWord_6619137) baseStart_6619137 baseEnd_6619137 := by
    simpa [prefixWord, tailWord_6619137, baseEnd_6619137] using wordTrace_append hprefix tailTrace_6619137
  have hstable : (prefixWord ++ tailWord_6619137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619137).length < 2 ^ (prefixWord ++ tailWord_6619137).sum := by decide
  have hdescent : baseEnd_6619137 < baseStart_6619137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619170 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_6619170 : Nat := 118140960795 + 6619170 * 2 ^ 59
def prefixEnd_6619170 : Nat := 4983230072969 + 3 ^ 40 * 6619170 * 2
def baseEnd_6619170 : Nat := 1132938581273657566877999

theorem tailTrace_6619170 : CollatzResearch.WordTrace tailWord_6619170 prefixEnd_6619170 1132938581273657566877999 := by
  unfold tailWord_6619170
  simp only [CollatzResearch.WordTrace]
  refine ⟨60355240857471257270063741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160947308953256686053503309 60355240857471257270063741)
  ·
    refine ⟨22633215321551721476273903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60355240857471257270063741 22633215321551721476273903)
    ·
      refine ⟨33949822982327582214410855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22633215321551721476273903 33949822982327582214410855)
      ·
        refine ⟨50924734473491373321616283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33949822982327582214410855 50924734473491373321616283)
        ·
          refine ⟨76387101710237059982424425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50924734473491373321616283 76387101710237059982424425)
          ·
            refine ⟨57290326282677794986818319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76387101710237059982424425 57290326282677794986818319)
            ·
              refine ⟨85935489424016692480227479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57290326282677794986818319 85935489424016692480227479)
              ·
                refine ⟨128903234136025038720341219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85935489424016692480227479 128903234136025038720341219)
                ·
                  refine ⟨193354851204037558080511829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128903234136025038720341219 193354851204037558080511829)
                  ·
                    refine ⟨1132938581273657566877999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 193354851204037558080511829 1132938581273657566877999)
                    ·
                      rfl

theorem cell23_6619170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_6619170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619170 prefixEnd_6619170 := by exact prefixLift 6619170
  have htrace : WordTrace (prefixWord ++ tailWord_6619170) baseStart_6619170 baseEnd_6619170 := by
    simpa [prefixWord, tailWord_6619170, baseEnd_6619170] using wordTrace_append hprefix tailTrace_6619170
  have hstable : (prefixWord ++ tailWord_6619170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619170).length < 2 ^ (prefixWord ++ tailWord_6619170).sum := by decide
  have hdescent : baseEnd_6619170 < baseStart_6619170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619184 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 2, 1, 3]
def baseStart_6619184 : Nat := 118140960795 + 6619184 * 2 ^ 59
def prefixEnd_6619184 : Nat := 4983230072969 + 3 ^ 40 * 6619184 * 2
def baseEnd_6619184 : Nat := 3398822932550135645858933

theorem tailTrace_6619184 : CollatzResearch.WordTrace tailWord_6619184 prefixEnd_6619184 3398822932550135645858933 := by
  unfold tailWord_6619184
  simp only [CollatzResearch.WordTrace]
  refine ⟨120710737025917154735632303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160947649367889539647509737 120710737025917154735632303)
  ·
    refine ⟨181066105538875732103448455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120710737025917154735632303 181066105538875732103448455)
    ·
      refine ⟨271599158308313598155172683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181066105538875732103448455 271599158308313598155172683)
      ·
        refine ⟨407398737462470397232759025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271599158308313598155172683 407398737462470397232759025)
        ·
          refine ⟨305549053096852797924569269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407398737462470397232759025 305549053096852797924569269)
          ·
            refine ⟨28645223727829949805428369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 305549053096852797924569269 28645223727829949805428369)
            ·
              refine ⟨21483917795872462354071277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28645223727829949805428369 21483917795872462354071277)
              ·
                refine ⟨8056469173452173382776729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21483917795872462354071277 8056469173452173382776729)
                ·
                  refine ⟨6042351880089130037082547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8056469173452173382776729 6042351880089130037082547)
                  ·
                    refine ⟨9063527820133695055623821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6042351880089130037082547 9063527820133695055623821)
                    ·
                      refine ⟨3398822932550135645858933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9063527820133695055623821 3398822932550135645858933)
                      ·
                        rfl

theorem cell23_6619184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 1, 3].length) (baseStart_6619184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619184 prefixEnd_6619184 := by exact prefixLift 6619184
  have htrace : WordTrace (prefixWord ++ tailWord_6619184) baseStart_6619184 baseEnd_6619184 := by
    simpa [prefixWord, tailWord_6619184, baseEnd_6619184] using wordTrace_append hprefix tailTrace_6619184
  have hstable : (prefixWord ++ tailWord_6619184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619184).length < 2 ^ (prefixWord ++ tailWord_6619184).sum := by decide
  have hdescent : baseEnd_6619184 < baseStart_6619184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619194 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2]
def baseStart_6619194 : Nat := 118140960795 + 6619194 * 2 ^ 59
def prefixEnd_6619194 : Nat := 4983230072969 + 3 ^ 40 * 6619194 * 2
def baseEnd_6619194 : Nat := 3398828067356680606733887

theorem tailTrace_6619194 : CollatzResearch.WordTrace tailWord_6619194 prefixEnd_6619194 3398828067356680606733887 := by
  unfold tailWord_6619194
  simp only [CollatzResearch.WordTrace]
  refine ⟨60355459695449520294782159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160947892521198720786085757 60355459695449520294782159)
  ·
    refine ⟨90533189543174280442173239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60355459695449520294782159 90533189543174280442173239)
    ·
      refine ⟨135799784314761420663259859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90533189543174280442173239 135799784314761420663259859)
      ·
        refine ⟨203699676472142130994889789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135799784314761420663259859 203699676472142130994889789)
        ·
          refine ⟨76387378677053299123083671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203699676472142130994889789 76387378677053299123083671)
          ·
            refine ⟨114581068015579948684625507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76387378677053299123083671 114581068015579948684625507)
            ·
              refine ⟨171871602023369923026938261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114581068015579948684625507 171871602023369923026938261)
              ·
                refine ⟨8056481344845465141887731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171871602023369923026938261 8056481344845465141887731)
                ·
                  refine ⟨12084722017268197712831597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8056481344845465141887731 12084722017268197712831597)
                  ·
                    refine ⟨4531770756475574142311849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12084722017268197712831597 4531770756475574142311849)
                    ·
                      refine ⟨3398828067356680606733887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4531770756475574142311849 3398828067356680606733887)
                      ·
                        rfl

theorem cell23_6619194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_6619194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619194 prefixEnd_6619194 := by exact prefixLift 6619194
  have htrace : WordTrace (prefixWord ++ tailWord_6619194) baseStart_6619194 baseEnd_6619194 := by
    simpa [prefixWord, tailWord_6619194, baseEnd_6619194] using wordTrace_append hprefix tailTrace_6619194
  have hstable : (prefixWord ++ tailWord_6619194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619194).length < 2 ^ (prefixWord ++ tailWord_6619194).sum := by decide
  have hdescent : baseEnd_6619194 < baseStart_6619194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619210 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_6619210 : Nat := 118140960795 + 6619210 * 2 ^ 59
def prefixEnd_6619210 : Nat := 4983230072969 + 3 ^ 40 * 6619210 * 2
def baseEnd_6619210 : Nat := 3398836283047152544133813

theorem tailTrace_6619210 : CollatzResearch.WordTrace tailWord_6619210 prefixEnd_6619210 3398836283047152544133813 := by
  unfold tailWord_6619210
  simp only [CollatzResearch.WordTrace]
  refine ⟨60355605587435028977927771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160948281566493410607807389 60355605587435028977927771)
  ·
    refine ⟨90533408381152543466891657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60355605587435028977927771 90533408381152543466891657)
    ·
      refine ⟨67900056285864407600168743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90533408381152543466891657 67900056285864407600168743)
      ·
        refine ⟨101850084428796611400253115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67900056285864407600168743 101850084428796611400253115)
        ·
          refine ⟨152775126643194917100379673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101850084428796611400253115 152775126643194917100379673)
          ·
            refine ⟨114581344982396187825284755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152775126643194917100379673 114581344982396187825284755)
            ·
              refine ⟨171872017473594281737927133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114581344982396187825284755 171872017473594281737927133)
              ·
                refine ⟨64452006552597855651722675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171872017473594281737927133 64452006552597855651722675)
                ·
                  refine ⟨96678009828896783477584013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64452006552597855651722675 96678009828896783477584013)
                  ·
                    refine ⟨36254253685836293804094005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96678009828896783477584013 36254253685836293804094005)
                    ·
                      refine ⟨3398836283047152544133813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36254253685836293804094005 3398836283047152544133813)
                      ·
                        rfl

theorem cell23_6619210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_6619210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619210 prefixEnd_6619210 := by exact prefixLift 6619210
  have htrace : WordTrace (prefixWord ++ tailWord_6619210) baseStart_6619210 baseEnd_6619210 := by
    simpa [prefixWord, tailWord_6619210, baseEnd_6619210] using wordTrace_append hprefix tailTrace_6619210
  have hstable : (prefixWord ++ tailWord_6619210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619210).length < 2 ^ (prefixWord ++ tailWord_6619210).sum := by decide
  have hdescent : baseEnd_6619210 < baseStart_6619210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619218 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_6619218 : Nat := 118140960795 + 6619218 * 2 ^ 59
def prefixEnd_6619218 : Nat := 4983230072969 + 3 ^ 40 * 6619218 * 2
def baseEnd_6619218 : Nat := 3398840390892388512833777

theorem tailTrace_6619218 : CollatzResearch.WordTrace tailWord_6619218 prefixEnd_6619218 3398840390892388512833777 := by
  unfold tailWord_6619218
  simp only [CollatzResearch.WordTrace]
  refine ⟨60355678533427783319500577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160948476089140755518668205 60355678533427783319500577)
  ·
    refine ⟨45266758900070837489625433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60355678533427783319500577 45266758900070837489625433)
    ·
      refine ⟨33950069175053128117219075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45266758900070837489625433 33950069175053128117219075)
      ·
        refine ⟨50925103762579692175828613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33950069175053128117219075 50925103762579692175828613)
        ·
          refine ⟨9548456955483692282967865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50925103762579692175828613 9548456955483692282967865)
          ·
            refine ⟨7161342716612769212225899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9548456955483692282967865 7161342716612769212225899)
            ·
              refine ⟨10742014074919153818338849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161342716612769212225899 10742014074919153818338849)
              ·
                refine ⟨8056510556189365363754137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10742014074919153818338849 8056510556189365363754137)
                ·
                  refine ⟨6042382917142024022815603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8056510556189365363754137 6042382917142024022815603)
                  ·
                    refine ⟨9063574375713036034223405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6042382917142024022815603 9063574375713036034223405)
                    ·
                      refine ⟨3398840390892388512833777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9063574375713036034223405 3398840390892388512833777)
                      ·
                        rfl

theorem cell23_6619218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_6619218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619218 prefixEnd_6619218 := by exact prefixLift 6619218
  have htrace : WordTrace (prefixWord ++ tailWord_6619218) baseStart_6619218 baseEnd_6619218 := by
    simpa [prefixWord, tailWord_6619218, baseEnd_6619218] using wordTrace_append hprefix tailTrace_6619218
  have hstable : (prefixWord ++ tailWord_6619218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619218).length < 2 ^ (prefixWord ++ tailWord_6619218).sum := by decide
  have hdescent : baseEnd_6619218 < baseStart_6619218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619237 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_6619237 : Nat := 118140960795 + 6619237 * 2 ^ 59
def prefixEnd_6619237 : Nat := 4983230072969 + 3 ^ 40 * 6619237 * 2
def baseEnd_6619237 : Nat := 3398850147024823938496189

theorem tailTrace_6619237 : CollatzResearch.WordTrace tailWord_6619237 prefixEnd_6619237 3398850147024823938496189 := by
  unfold tailWord_6619237
  simp only [CollatzResearch.WordTrace]
  refine ⟨241423407120642299522943965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160948938080428199681962643 241423407120642299522943965)
  ·
    refine ⟨90533777670240862321103987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241423407120642299522943965 90533777670240862321103987)
    ·
      refine ⟨135800666505361293481655981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90533777670240862321103987 135800666505361293481655981)
      ·
        refine ⟨50925249939510485055620993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135800666505361293481655981 50925249939510485055620993)
        ·
          refine ⟨38193937454632863791715745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50925249939510485055620993 38193937454632863791715745)
          ·
            refine ⟨28645453090974647843786809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38193937454632863791715745 28645453090974647843786809)
            ·
              refine ⟨21484089818230985882840107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28645453090974647843786809 21484089818230985882840107)
              ·
                refine ⟨32226134727346478824260161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21484089818230985882840107 32226134727346478824260161)
                ·
                  refine ⟨24169601045509859118195121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32226134727346478824260161 24169601045509859118195121)
                  ·
                    refine ⟨18127200784132394338646341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24169601045509859118195121 18127200784132394338646341)
                    ·
                      refine ⟨3398850147024823938496189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18127200784132394338646341 3398850147024823938496189)
                      ·
                        rfl

theorem cell23_6619237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_6619237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619237 prefixEnd_6619237 := by exact prefixLift 6619237
  have htrace : WordTrace (prefixWord ++ tailWord_6619237) baseStart_6619237 baseEnd_6619237 := by
    simpa [prefixWord, tailWord_6619237, baseEnd_6619237] using wordTrace_append hprefix tailTrace_6619237
  have hstable : (prefixWord ++ tailWord_6619237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619237).length < 2 ^ (prefixWord ++ tailWord_6619237).sum := by decide
  have hdescent : baseEnd_6619237 < baseStart_6619237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619286 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6619286 : Nat := 118140960795 + 6619286 * 2 ^ 59
def prefixEnd_6619286 : Nat := 4983230072969 + 3 ^ 40 * 6619286 * 2
def baseEnd_6619286 : Nat := 3398875307576894246783465

theorem tailTrace_6619286 : CollatzResearch.WordTrace tailWord_6619286 prefixEnd_6619286 3398875307576894246783465 := by
  unfold tailWord_6619286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089074643591548805717357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160950129531643187260985141 15089074643591548805717357)
  ·
    refine ⟨5658402991346830802144009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15089074643591548805717357 5658402991346830802144009)
    ·
      refine ⟨4243802243510123101608007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5658402991346830802144009 4243802243510123101608007)
      ·
        refine ⟨6365703365265184652412011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243802243510123101608007 6365703365265184652412011)
        ·
          refine ⟨9548555047897776978618017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365703365265184652412011 9548555047897776978618017)
          ·
            refine ⟨7161416285923332733963513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9548555047897776978618017 7161416285923332733963513)
            ·
              refine ⟨5371062214442499550472635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7161416285923332733963513 5371062214442499550472635)
              ·
                refine ⟨8056593321663749325708953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371062214442499550472635 8056593321663749325708953)
                ·
                  refine ⟨6042444991247811994281715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8056593321663749325708953 6042444991247811994281715)
                  ·
                    refine ⟨9063667486871717991422573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6042444991247811994281715 9063667486871717991422573)
                    ·
                      refine ⟨3398875307576894246783465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9063667486871717991422573 3398875307576894246783465)
                      ·
                        rfl

theorem cell23_6619286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6619286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619286 prefixEnd_6619286 := by exact prefixLift 6619286
  have htrace : WordTrace (prefixWord ++ tailWord_6619286) baseStart_6619286 baseEnd_6619286 := by
    simpa [prefixWord, tailWord_6619286, baseEnd_6619286] using wordTrace_append hprefix tailTrace_6619286
  have hstable : (prefixWord ++ tailWord_6619286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619286).length < 2 ^ (prefixWord ++ tailWord_6619286).sum := by decide
  have hdescent : baseEnd_6619286 < baseStart_6619286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619314 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_6619314 : Nat := 118140960795 + 6619314 * 2 ^ 59
def prefixEnd_6619314 : Nat := 4983230072969 + 3 ^ 40 * 6619314 * 2
def baseEnd_6619314 : Nat := 3398889685035220137233335

theorem tailTrace_6619314 : CollatzResearch.WordTrace tailWord_6619314 prefixEnd_6619314 3398889685035220137233335 := by
  unfold tailWord_6619314
  simp only [CollatzResearch.WordTrace]
  refine ⟨60356553885340835418374249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160950810360908894448997997 60356553885340835418374249)
  ·
    refine ⟨45267415414005626563780687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60356553885340835418374249 45267415414005626563780687)
    ·
      refine ⟨67901123121008439845671031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45267415414005626563780687 67901123121008439845671031)
      ·
        refine ⟨101851684681512659768506547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67901123121008439845671031 101851684681512659768506547)
        ·
          refine ⟨152777527022268989652759821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101851684681512659768506547 152777527022268989652759821)
          ·
            refine ⟨57291572633350871119784933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152777527022268989652759821 57291572633350871119784933)
            ·
              refine ⟨10742169868753288334959675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57291572633350871119784933 10742169868753288334959675)
              ·
                refine ⟨16113254803129932502439513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10742169868753288334959675 16113254803129932502439513)
                ·
                  refine ⟨12084941102347449376829635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16113254803129932502439513 12084941102347449376829635)
                  ·
                    refine ⟨18127411653521174065244453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12084941102347449376829635 18127411653521174065244453)
                    ·
                      refine ⟨3398889685035220137233335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18127411653521174065244453 3398889685035220137233335)
                      ·
                        rfl

theorem cell23_6619314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_6619314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619314 prefixEnd_6619314 := by exact prefixLift 6619314
  have htrace : WordTrace (prefixWord ++ tailWord_6619314) baseStart_6619314 baseEnd_6619314 := by
    simpa [prefixWord, tailWord_6619314, baseEnd_6619314] using wordTrace_append hprefix tailTrace_6619314
  have hstable : (prefixWord ++ tailWord_6619314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619314).length < 2 ^ (prefixWord ++ tailWord_6619314).sum := by decide
  have hdescent : baseEnd_6619314 < baseStart_6619314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619362 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6619362 : Nat := 118140960795 + 6619362 * 2 ^ 59
def prefixEnd_6619362 : Nat := 4983230072969 + 3 ^ 40 * 6619362 * 2
def baseEnd_6619362 : Nat := 1132971444035545316477705

theorem tailTrace_6619362 : CollatzResearch.WordTrace tailWord_6619362 prefixEnd_6619362 1132971444035545316477705 := by
  unfold tailWord_6619362
  simp only [CollatzResearch.WordTrace]
  refine ⟨60356991561297361467811085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160951977496792963914162893 60356991561297361467811085)
  ·
    refine ⟨22633871835486510550429157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60356991561297361467811085 22633871835486510550429157)
    ·
      refine ⟨4243850969153720728205467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22633871835486510550429157 4243850969153720728205467)
      ·
        refine ⟨6365776453730581092308201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243850969153720728205467 6365776453730581092308201)
        ·
          refine ⟨4774332340297935819231151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6365776453730581092308201 4774332340297935819231151)
          ·
            refine ⟨7161498510446903728846727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774332340297935819231151 7161498510446903728846727)
            ·
              refine ⟨10742247765670355593270091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161498510446903728846727 10742247765670355593270091)
              ·
                refine ⟨16113371648505533389905137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10742247765670355593270091 16113371648505533389905137)
                ·
                  refine ⟨12085028736379150042428853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16113371648505533389905137 12085028736379150042428853)
                  ·
                    refine ⟨1132971444035545316477705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12085028736379150042428853 1132971444035545316477705)
                    ·
                      rfl

theorem cell23_6619362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6619362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619362 prefixEnd_6619362 := by exact prefixLift 6619362
  have htrace : WordTrace (prefixWord ++ tailWord_6619362) baseStart_6619362 baseEnd_6619362 := by
    simpa [prefixWord, tailWord_6619362, baseEnd_6619362] using wordTrace_append hprefix tailTrace_6619362
  have hstable : (prefixWord ++ tailWord_6619362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619362).length < 2 ^ (prefixWord ++ tailWord_6619362).sum := by decide
  have hdescent : baseEnd_6619362 < baseStart_6619362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619427 : List Nat := [1, 1, 1, 4, 2, 2, 3, 9]
def baseStart_6619427 : Nat := 118140960795 + 6619427 * 2 ^ 59
def prefixEnd_6619427 : Nat := 4983230072969 + 3 ^ 40 * 6619427 * 2
def baseEnd_6619427 : Nat := 125886952161080673893345

theorem tailTrace_6619427 : CollatzResearch.WordTrace tailWord_6619427 prefixEnd_6619427 125886952161080673893345 := by
  unfold tailWord_6619427
  simp only [CollatzResearch.WordTrace]
  refine ⟨241430336989953961972360535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160953557993302641314907023 241430336989953961972360535)
  ·
    refine ⟨362145505484930942958540803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241430336989953961972360535 362145505484930942958540803)
    ·
      refine ⟨543218258227396414437811205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362145505484930942958540803 543218258227396414437811205)
      ·
        refine ⟨101853423417636827707089601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 543218258227396414437811205 101853423417636827707089601)
        ·
          refine ⟨76390067563227620780317201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101853423417636827707089601 76390067563227620780317201)
          ·
            refine ⟨57292550672420715585237901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76390067563227620780317201 57292550672420715585237901)
            ·
              refine ⟨21484706502157768344464213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57292550672420715585237901 21484706502157768344464213)
              ·
                refine ⟨125886952161080673893345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21484706502157768344464213 125886952161080673893345)
                ·
                  rfl

theorem cell23_6619427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 9].length) (baseStart_6619427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619427 prefixEnd_6619427 := by exact prefixLift 6619427
  have htrace : WordTrace (prefixWord ++ tailWord_6619427) baseStart_6619427 baseEnd_6619427 := by
    simpa [prefixWord, tailWord_6619427, baseEnd_6619427] using wordTrace_append hprefix tailTrace_6619427
  have hstable : (prefixWord ++ tailWord_6619427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619427).length < 2 ^ (prefixWord ++ tailWord_6619427).sum := by decide
  have hdescent : baseEnd_6619427 < baseStart_6619427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619432 : List Nat := [2, 1, 5, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_6619432 : Nat := 118140960795 + 6619432 * 2 ^ 59
def prefixEnd_6619432 : Nat := 4983230072969 + 3 ^ 40 * 6619432 * 2
def baseEnd_6619432 : Nat := 3398950275752450675557793

theorem tailTrace_6619432 : CollatzResearch.WordTrace tailWord_6619432 prefixEnd_6619432 3398950275752450675557793 := by
  unfold tailWord_6619432
  simp only [CollatzResearch.WordTrace]
  refine ⟨120715259677467923913146275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160953679569957231884195033 120715259677467923913146275)
  ·
    refine ⟨181072889516201885869719413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120715259677467923913146275 181072889516201885869719413)
    ·
      refine ⟨16975583392143926800286195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181072889516201885869719413 16975583392143926800286195)
      ·
        refine ⟨25463375088215890200429293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16975583392143926800286195 25463375088215890200429293)
        ·
          refine ⟨9548765658080958825160985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25463375088215890200429293 9548765658080958825160985)
          ·
            refine ⟨7161574243560719118870739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9548765658080958825160985 7161574243560719118870739)
            ·
              refine ⟨10742361365341078678306109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161574243560719118870739 10742361365341078678306109)
              ·
                refine ⟨4028385512002904504364791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10742361365341078678306109 4028385512002904504364791)
                ·
                  refine ⟨6042578268004356756547187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4028385512002904504364791 6042578268004356756547187)
                  ·
                    refine ⟨9063867402006535134820781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6042578268004356756547187 9063867402006535134820781)
                    ·
                      refine ⟨3398950275752450675557793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9063867402006535134820781 3398950275752450675557793)
                      ·
                        rfl

theorem cell23_6619432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_6619432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619432 prefixEnd_6619432 := by exact prefixLift 6619432
  have htrace : WordTrace (prefixWord ++ tailWord_6619432) baseStart_6619432 baseEnd_6619432 := by
    simpa [prefixWord, tailWord_6619432, baseEnd_6619432] using wordTrace_append hprefix tailTrace_6619432
  have hstable : (prefixWord ++ tailWord_6619432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619432).length < 2 ^ (prefixWord ++ tailWord_6619432).sum := by decide
  have hdescent : baseEnd_6619432 < baseStart_6619432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619441 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_6619441 : Nat := 118140960795 + 6619441 * 2 ^ 59
def prefixEnd_6619441 : Nat := 4983230072969 + 3 ^ 40 * 6619441 * 2
def baseEnd_6619441 : Nat := 3398954897078341140345251

theorem tailTrace_6619441 : CollatzResearch.WordTrace tailWord_6619441 prefixEnd_6619441 3398954897078341140345251 := by
  unfold tailWord_6619441
  simp only [CollatzResearch.WordTrace]
  refine ⟨241430847611903242363370177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160953898407935494908913451 241430847611903242363370177)
  ·
    refine ⟨181073135708927431772527633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241430847611903242363370177 181073135708927431772527633)
    ·
      refine ⟨135804851781695573829395725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181073135708927431772527633 135804851781695573829395725)
      ·
        refine ⟨50926819418135840186023397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135804851781695573829395725 50926819418135840186023397)
        ·
          refine ⟨9548778640900470034879387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50926819418135840186023397 9548778640900470034879387)
          ·
            refine ⟨14323167961350705052319081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9548778640900470034879387 14323167961350705052319081)
            ·
              refine ⟨10742375971013028789239311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14323167961350705052319081 10742375971013028789239311)
              ·
                refine ⟨16113563956519543183858967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10742375971013028789239311 16113563956519543183858967)
                ·
                  refine ⟨24170345934779314775788451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16113563956519543183858967 24170345934779314775788451)
                  ·
                    refine ⟨36255518902168972163682677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24170345934779314775788451 36255518902168972163682677)
                    ·
                      refine ⟨3398954897078341140345251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36255518902168972163682677 3398954897078341140345251)
                      ·
                        rfl

theorem cell23_6619441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_6619441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619441 prefixEnd_6619441 := by exact prefixLift 6619441
  have htrace : WordTrace (prefixWord ++ tailWord_6619441) baseStart_6619441 baseEnd_6619441 := by
    simpa [prefixWord, tailWord_6619441, baseEnd_6619441] using wordTrace_append hprefix tailTrace_6619441
  have hstable : (prefixWord ++ tailWord_6619441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619441).length < 2 ^ (prefixWord ++ tailWord_6619441).sum := by decide
  have hdescent : baseEnd_6619441 < baseStart_6619441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619444 : List Nat := [2, 5, 1, 1, 1, 2, 11]
def baseStart_6619444 : Nat := 118140960795 + 6619444 * 2 ^ 59
def prefixEnd_6619444 : Nat := 4983230072969 + 3 ^ 40 * 6619444 * 2
def baseEnd_6619444 : Nat := 41962425154571662081577

theorem tailTrace_6619444 : CollatzResearch.WordTrace tailWord_6619444 prefixEnd_6619444 41962425154571662081577 := by
  unfold tailWord_6619444
  simp only [CollatzResearch.WordTrace]
  refine ⟨120715478515446186937864693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160953971353928249250486257 120715478515446186937864693)
  ·
    refine ⟨11317076110823080025424815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120715478515446186937864693 11317076110823080025424815)
    ·
      refine ⟨16975614166234620038137223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11317076110823080025424815 16975614166234620038137223)
      ·
        refine ⟨25463421249351930057205835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16975614166234620038137223 25463421249351930057205835)
        ·
          refine ⟨38195131874027895085808753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25463421249351930057205835 38195131874027895085808753)
          ·
            refine ⟨28646348905520921314356565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38195131874027895085808753 28646348905520921314356565)
            ·
              refine ⟨41962425154571662081577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28646348905520921314356565 41962425154571662081577)
              ·
                rfl

theorem cell23_6619444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 11].length) (baseStart_6619444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619444 prefixEnd_6619444 := by exact prefixLift 6619444
  have htrace : WordTrace (prefixWord ++ tailWord_6619444) baseStart_6619444 baseEnd_6619444 := by
    simpa [prefixWord, tailWord_6619444, baseEnd_6619444] using wordTrace_append hprefix tailTrace_6619444
  have hstable : (prefixWord ++ tailWord_6619444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619444).length < 2 ^ (prefixWord ++ tailWord_6619444).sum := by decide
  have hdescent : baseEnd_6619444 < baseStart_6619444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619467 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 5]
def baseStart_6619467 : Nat := 118140960795 + 6619467 * 2 ^ 59
def prefixEnd_6619467 : Nat := 4983230072969 + 3 ^ 40 * 6619467 * 2
def baseEnd_6619467 : Nat := 3398968247575358038620131

theorem tailTrace_6619467 : CollatzResearch.WordTrace tailWord_6619467 prefixEnd_6619467 3398968247575358038620131 := by
  unfold tailWord_6619467
  simp only [CollatzResearch.WordTrace]
  refine ⟨241431795909809048803816655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160954530606539365869211103 241431795909809048803816655)
  ·
    refine ⟨362147693864713573205724983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241431795909809048803816655 362147693864713573205724983)
    ·
      refine ⟨543221540797070359808587475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362147693864713573205724983 543221540797070359808587475)
      ·
        refine ⟨814832311195605539712881213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543221540797070359808587475 814832311195605539712881213)
        ·
          refine ⟨305562116698352077392330455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814832311195605539712881213 305562116698352077392330455)
          ·
            refine ⟨458343175047528116088495683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305562116698352077392330455 458343175047528116088495683)
            ·
              refine ⟨687514762571292174132743525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458343175047528116088495683 687514762571292174132743525)
              ·
                refine ⟨128909017982117282649889411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687514762571292174132743525 128909017982117282649889411)
                ·
                  refine ⟨193363526973175923974834117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128909017982117282649889411 193363526973175923974834117)
                  ·
                    refine ⟨36255661307470485745281397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193363526973175923974834117 36255661307470485745281397)
                    ·
                      refine ⟨3398968247575358038620131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36255661307470485745281397 3398968247575358038620131)
                      ·
                        rfl

theorem cell23_6619467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_6619467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619467 prefixEnd_6619467 := by exact prefixLift 6619467
  have htrace : WordTrace (prefixWord ++ tailWord_6619467) baseStart_6619467 baseEnd_6619467 := by
    simpa [prefixWord, tailWord_6619467, baseEnd_6619467] using wordTrace_append hprefix tailTrace_6619467
  have hstable : (prefixWord ++ tailWord_6619467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619467).length < 2 ^ (prefixWord ++ tailWord_6619467).sum := by decide
  have hdescent : baseEnd_6619467 < baseStart_6619467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619521 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 2, 6]
def baseStart_6619521 : Nat := 118140960795 + 6619521 * 2 ^ 59
def prefixEnd_6619521 : Nat := 4983230072969 + 3 ^ 40 * 6619521 * 2
def baseEnd_6619521 : Nat := 1132998658510233609114961

theorem tailTrace_6619521 : CollatzResearch.WordTrace tailWord_6619521 prefixEnd_6619521 1132998658510233609114961 := by
  unfold tailWord_6619521
  simp only [CollatzResearch.WordTrace]
  refine ⟨241433765451613416026282417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160955843634408944017521611 241433765451613416026282417)
  ·
    refine ⟨181075324088710062019711813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241433765451613416026282417 181075324088710062019711813)
    ·
      refine ⟨33951623266633136628695965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181075324088710062019711813 33951623266633136628695965)
      ·
        refine ⟨12731858724987426235760987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33951623266633136628695965 12731858724987426235760987)
        ·
          refine ⟨19097788087481139353641481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12731858724987426235760987 19097788087481139353641481)
          ·
            refine ⟨14323341065610854515231111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19097788087481139353641481 14323341065610854515231111)
            ·
              refine ⟨21485011598416281772846667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14323341065610854515231111 21485011598416281772846667)
              ·
                refine ⟨32227517397624422659270001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21485011598416281772846667 32227517397624422659270001)
                ·
                  refine ⟨24170638048218316994452501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32227517397624422659270001 24170638048218316994452501)
                  ·
                    refine ⟨1132998658510233609114961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24170638048218316994452501 1132998658510233609114961)
                    ·
                      rfl

theorem cell23_6619521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_6619521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619521 prefixEnd_6619521 := by exact prefixLift 6619521
  have htrace : WordTrace (prefixWord ++ tailWord_6619521) baseStart_6619521 baseEnd_6619521 := by
    simpa [prefixWord, tailWord_6619521, baseEnd_6619521] using wordTrace_append hprefix tailTrace_6619521
  have hstable : (prefixWord ++ tailWord_6619521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619521).length < 2 ^ (prefixWord ++ tailWord_6619521).sum := by decide
  have hdescent : baseEnd_6619521 < baseStart_6619521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619528 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_6619528 : Nat := 118140960795 + 6619528 * 2 ^ 59
def prefixEnd_6619528 : Nat := 4983230072969 + 3 ^ 40 * 6619528 * 2
def baseEnd_6619528 : Nat := 3398999569895282299957351

theorem tailTrace_6619528 : CollatzResearch.WordTrace tailWord_6619528 prefixEnd_6619528 3398999569895282299957351 := by
  unfold tailWord_6619528
  simp only [CollatzResearch.WordTrace]
  refine ⟨120717010381294028110893619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160956013841725370814524825 120717010381294028110893619)
  ·
    refine ⟨181075515571941042166340429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120717010381294028110893619 181075515571941042166340429)
    ·
      refine ⟨67903318339477890812377661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181075515571941042166340429 67903318339477890812377661)
      ·
        refine ⟨25463744377304209054641623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67903318339477890812377661 25463744377304209054641623)
        ·
          refine ⟨38195616565956313581962435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25463744377304209054641623 38195616565956313581962435)
          ·
            refine ⟨57293424848934470372943653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38195616565956313581962435 57293424848934470372943653)
            ·
              refine ⟨10742517159175213194926935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57293424848934470372943653 10742517159175213194926935)
              ·
                refine ⟨16113775738762819792390403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10742517159175213194926935 16113775738762819792390403)
                ·
                  refine ⟨24170663608144229688585605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16113775738762819792390403 24170663608144229688585605)
                  ·
                    refine ⟨4531999426527043066609801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24170663608144229688585605 4531999426527043066609801)
                    ·
                      refine ⟨3398999569895282299957351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4531999426527043066609801 3398999569895282299957351)
                      ·
                        rfl

theorem cell23_6619528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_6619528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619528 prefixEnd_6619528 := by exact prefixLift 6619528
  have htrace : WordTrace (prefixWord ++ tailWord_6619528) baseStart_6619528 baseEnd_6619528 := by
    simpa [prefixWord, tailWord_6619528, baseEnd_6619528] using wordTrace_append hprefix tailTrace_6619528
  have hstable : (prefixWord ++ tailWord_6619528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619528).length < 2 ^ (prefixWord ++ tailWord_6619528).sum := by decide
  have hdescent : baseEnd_6619528 < baseStart_6619528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619549 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_6619549 : Nat := 118140960795 + 6619549 * 2 ^ 59
def prefixEnd_6619549 : Nat := 4983230072969 + 3 ^ 40 * 6619549 * 2
def baseEnd_6619549 : Nat := 3399010352989026717794755

theorem tailTrace_6619549 : CollatzResearch.WordTrace tailWord_6619549 prefixEnd_6619549 3399010352989026717794755 := by
  unfold tailWord_6619549
  simp only [CollatzResearch.WordTrace]
  refine ⟨241434786695511976808301701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160956524463674651205534467 241434786695511976808301701)
  ·
    refine ⟨45269022505408495651556569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241434786695511976808301701 45269022505408495651556569)
    ·
      refine ⟨33951766879056371738667427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45269022505408495651556569 33951766879056371738667427)
      ·
        refine ⟨50927650318584557608001141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33951766879056371738667427 50927650318584557608001141)
        ·
          refine ⟨4774467217367302275750107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50927650318584557608001141 4774467217367302275750107)
          ·
            refine ⟨7161700826050953413625161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774467217367302275750107 7161700826050953413625161)
            ·
              refine ⟨5371275619538215060218871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7161700826050953413625161 5371275619538215060218871)
              ·
                refine ⟨8056913429307322590328307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371275619538215060218871 8056913429307322590328307)
                ·
                  refine ⟨12085370143960983885492461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8056913429307322590328307 12085370143960983885492461)
                  ·
                    refine ⟨4532013803985368957059673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12085370143960983885492461 4532013803985368957059673)
                    ·
                      refine ⟨3399010352989026717794755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4532013803985368957059673 3399010352989026717794755)
                      ·
                        rfl

theorem cell23_6619549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_6619549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619549 prefixEnd_6619549 := by exact prefixLift 6619549
  have htrace : WordTrace (prefixWord ++ tailWord_6619549) baseStart_6619549 baseEnd_6619549 := by
    simpa [prefixWord, tailWord_6619549, baseEnd_6619549] using wordTrace_append hprefix tailTrace_6619549
  have hstable : (prefixWord ++ tailWord_6619549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619549).length < 2 ^ (prefixWord ++ tailWord_6619549).sum := by decide
  have hdescent : baseEnd_6619549 < baseStart_6619549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619564 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_6619564 : Nat := 118140960795 + 6619564 * 2 ^ 59
def prefixEnd_6619564 : Nat := 4983230072969 + 3 ^ 40 * 6619564 * 2
def baseEnd_6619564 : Nat := 1133006018399614719702395

theorem tailTrace_6619564 : CollatzResearch.WordTrace tailWord_6619564 prefixEnd_6619564 1133006018399614719702395 := by
  unfold tailWord_6619564
  simp only [CollatzResearch.WordTrace]
  refine ⟨120717666895228817185048873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160956889193638422913398497 120717666895228817185048873)
  ·
    refine ⟨90538250171421612888786655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120717666895228817185048873 90538250171421612888786655)
    ·
      refine ⟨135807375257132419333179983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90538250171421612888786655 135807375257132419333179983)
      ·
        refine ⟨203711062885698628999769975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135807375257132419333179983 203711062885698628999769975)
        ·
          refine ⟨305566594328547943499654963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203711062885698628999769975 305566594328547943499654963)
          ·
            refine ⟨458349891492821915249482445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305566594328547943499654963 458349891492821915249482445)
            ·
              refine ⟨171881209309808218218555917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458349891492821915249482445 171881209309808218218555917)
              ·
                refine ⟨64455453491178081831958469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171881209309808218218555917 64455453491178081831958469)
                ·
                  refine ⟨12085397529595890343492213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64455453491178081831958469 12085397529595890343492213)
                  ·
                    refine ⟨1133006018399614719702395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12085397529595890343492213 1133006018399614719702395)
                    ·
                      rfl

theorem cell23_6619564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_6619564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619564 prefixEnd_6619564 := by exact prefixLift 6619564
  have htrace : WordTrace (prefixWord ++ tailWord_6619564) baseStart_6619564 baseEnd_6619564 := by
    simpa [prefixWord, tailWord_6619564, baseEnd_6619564] using wordTrace_append hprefix tailTrace_6619564
  have hstable : (prefixWord ++ tailWord_6619564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619564).length < 2 ^ (prefixWord ++ tailWord_6619564).sum := by decide
  have hdescent : baseEnd_6619564 < baseStart_6619564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619594 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_6619594 : Nat := 118140960795 + 6619594 * 2 ^ 59
def prefixEnd_6619594 : Nat := 4983230072969 + 3 ^ 40 * 6619594 * 2
def baseEnd_6619594 : Nat := 1133011153206159680577349

theorem tailTrace_6619594 : CollatzResearch.WordTrace tailWord_6619594 prefixEnd_6619594 1133011153206159680577349 := by
  unfold tailWord_6619594
  simp only [CollatzResearch.WordTrace]
  refine ⟨60359106995087237373422459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160957618653565966329126557 60359106995087237373422459)
  ·
    refine ⟨90538660492630856060133689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60359106995087237373422459 90538660492630856060133689)
    ·
      refine ⟨67903995369473142045100267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90538660492630856060133689 67903995369473142045100267)
      ·
        refine ⟨101855993054209713067650401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67903995369473142045100267 101855993054209713067650401)
        ·
          refine ⟨76391994790657284800737801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101855993054209713067650401 76391994790657284800737801)
          ·
            refine ⟨57293996092992963600553351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76391994790657284800737801 57293996092992963600553351)
            ·
              refine ⟨85940994139489445400830027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57293996092992963600553351 85940994139489445400830027)
              ·
                refine ⟨128911491209234168101245041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85940994139489445400830027 128911491209234168101245041)
                ·
                  refine ⟨96683618406925626075933781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128911491209234168101245041 96683618406925626075933781)
                  ·
                    refine ⟨1133011153206159680577349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96683618406925626075933781 1133011153206159680577349)
                    ·
                      rfl

theorem cell23_6619594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_6619594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619594 prefixEnd_6619594 := by exact prefixLift 6619594
  have htrace : WordTrace (prefixWord ++ tailWord_6619594) baseStart_6619594 baseEnd_6619594 := by
    simpa [prefixWord, tailWord_6619594, baseEnd_6619594] using wordTrace_append hprefix tailTrace_6619594
  have hstable : (prefixWord ++ tailWord_6619594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619594).length < 2 ^ (prefixWord ++ tailWord_6619594).sum := by decide
  have hdescent : baseEnd_6619594 < baseStart_6619594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619601 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 1, 6, 2]
def baseStart_6619601 : Nat := 118140960795 + 6619601 * 2 ^ 59
def prefixEnd_6619601 : Nat := 4983230072969 + 3 ^ 40 * 6619601 * 2
def baseEnd_6619601 : Nat := 3399037053983060514344515

theorem tailTrace_6619601 : CollatzResearch.WordTrace tailWord_6619601 prefixEnd_6619601 3399037053983060514344515 := by
  unfold tailWord_6619601
  simp only [CollatzResearch.WordTrace]
  refine ⟨241436683291323589689194657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160957788860882393126129771 241436683291323589689194657)
  ·
    refine ⟨181077512468492692266895993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241436683291323589689194657 181077512468492692266895993)
    ·
      refine ⟨135808134351369519200171995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181077512468492692266895993 135808134351369519200171995)
      ·
        refine ⟨203712201527054278800257993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135808134351369519200171995 203712201527054278800257993)
        ·
          refine ⟨152784151145290709100193495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203712201527054278800257993 152784151145290709100193495)
          ·
            refine ⟨229176226717936063650290243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152784151145290709100193495 229176226717936063650290243)
            ·
              refine ⟨343764340076904095475435365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229176226717936063650290243 343764340076904095475435365)
              ·
                refine ⟨64455813764419517901644131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343764340076904095475435365 64455813764419517901644131)
                ·
                  refine ⟨96683720646629276852466197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64455813764419517901644131 96683720646629276852466197)
                  ·
                    refine ⟨4532049405310747352459353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96683720646629276852466197 4532049405310747352459353)
                    ·
                      refine ⟨3399037053983060514344515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4532049405310747352459353 3399037053983060514344515)
                      ·
                        rfl

theorem cell23_6619601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_6619601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619601 prefixEnd_6619601 := by exact prefixLift 6619601
  have htrace : WordTrace (prefixWord ++ tailWord_6619601) baseStart_6619601 baseEnd_6619601 := by
    simpa [prefixWord, tailWord_6619601, baseEnd_6619601] using wordTrace_append hprefix tailTrace_6619601
  have hstable : (prefixWord ++ tailWord_6619601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619601).length < 2 ^ (prefixWord ++ tailWord_6619601).sum := by decide
  have hdescent : baseEnd_6619601 < baseStart_6619601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619602 : List Nat := [3, 2, 2, 4, 1, 2, 1, 3, 5]
def baseStart_6619602 : Nat := 118140960795 + 6619602 * 2 ^ 59
def prefixEnd_6619602 : Nat := 4983230072969 + 3 ^ 40 * 6619602 * 2
def baseEnd_6619602 : Nat := 377670840829301667825779

theorem tailTrace_6619602 : CollatzResearch.WordTrace tailWord_6619602 prefixEnd_6619602 377670840829301667825779 := by
  unfold tailWord_6619602
  simp only [CollatzResearch.WordTrace]
  refine ⟨60359179941079991714995265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160957813176213311239987373 60359179941079991714995265)
  ·
    refine ⟨45269384955809993786246449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60359179941079991714995265 45269384955809993786246449)
    ·
      refine ⟨33952038716857495339684837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45269384955809993786246449 33952038716857495339684837)
      ·
        refine ⟨6366007259410780376190907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33952038716857495339684837 6366007259410780376190907)
        ·
          refine ⟨9549010889116170564286361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6366007259410780376190907 9549010889116170564286361)
          ·
            refine ⟨7161758166837127923214771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9549010889116170564286361 7161758166837127923214771)
            ·
              refine ⟨10742637250255691884822157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161758166837127923214771 10742637250255691884822157)
              ·
                refine ⟨4028488968845884456808309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10742637250255691884822157 4028488968845884456808309)
                ·
                  refine ⟨377670840829301667825779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4028488968845884456808309 377670840829301667825779)
                  ·
                    rfl

theorem cell23_6619602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_6619602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619602 prefixEnd_6619602 := by exact prefixLift 6619602
  have htrace : WordTrace (prefixWord ++ tailWord_6619602) baseStart_6619602 baseEnd_6619602 := by
    simpa [prefixWord, tailWord_6619602, baseEnd_6619602] using wordTrace_append hprefix tailTrace_6619602
  have hstable : (prefixWord ++ tailWord_6619602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619602).length < 2 ^ (prefixWord ++ tailWord_6619602).sum := by decide
  have hdescent : baseEnd_6619602 < baseStart_6619602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619638 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_6619638 : Nat := 118140960795 + 6619638 * 2 ^ 59
def prefixEnd_6619638 : Nat := 4983230072969 + 3 ^ 40 * 6619638 * 2
def baseEnd_6619638 : Nat := 3399056052767276869581845

theorem tailTrace_6619638 : CollatzResearch.WordTrace tailWord_6619638 prefixEnd_6619638 3399056052767276869581845 := by
  unfold tailWord_6619638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089877049511846563018223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160958688528126363338861045 15089877049511846563018223)
  ·
    refine ⟨22634815574267769844527335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15089877049511846563018223 22634815574267769844527335)
    ·
      refine ⟨33952223361401654766791003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22634815574267769844527335 33952223361401654766791003)
      ·
        refine ⟨50928335042102482150186505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33952223361401654766791003 50928335042102482150186505)
        ·
          refine ⟨38196251281576861612639879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50928335042102482150186505 38196251281576861612639879)
          ·
            refine ⟨57294376922365292418959819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38196251281576861612639879 57294376922365292418959819)
            ·
              refine ⟨85941565383547938628439729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57294376922365292418959819 85941565383547938628439729)
              ·
                refine ⟨64456174037660953971329797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85941565383547938628439729 64456174037660953971329797)
                ·
                  refine ⟨12085532632061428869624337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64456174037660953971329797 12085532632061428869624337)
                  ·
                    refine ⟨9064149474046071652218253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12085532632061428869624337 9064149474046071652218253)
                    ·
                      refine ⟨3399056052767276869581845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9064149474046071652218253 3399056052767276869581845)
                      ·
                        rfl

theorem cell23_6619638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_6619638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619638 prefixEnd_6619638 := by exact prefixLift 6619638
  have htrace : WordTrace (prefixWord ++ tailWord_6619638) baseStart_6619638 baseEnd_6619638 := by
    simpa [prefixWord, tailWord_6619638, baseEnd_6619638] using wordTrace_append hprefix tailTrace_6619638
  have hstable : (prefixWord ++ tailWord_6619638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619638).length < 2 ^ (prefixWord ++ tailWord_6619638).sum := by decide
  have hdescent : baseEnd_6619638 < baseStart_6619638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619655 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_6619655 : Nat := 118140960795 + 6619655 * 2 ^ 59
def prefixEnd_6619655 : Nat := 4983230072969 + 3 ^ 40 * 6619655 * 2
def baseEnd_6619655 : Nat := 3399064781938403303069267

theorem tailTrace_6619655 : CollatzResearch.WordTrace tailWord_6619655 prefixEnd_6619655 3399064781938403303069267 := by
  unfold tailWord_6619655
  simp only [CollatzResearch.WordTrace]
  refine ⟨241438652833127956911660419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160959101888751971274440279 241438652833127956911660419)
  ·
    refine ⟨362157979249691935367490629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241438652833127956911660419 362157979249691935367490629)
    ·
      refine ⟨67904621109317237881404493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362157979249691935367490629 67904621109317237881404493)
      ·
        refine ⟨25464232915993964205526685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67904621109317237881404493 25464232915993964205526685)
        ·
          refine ⟨9549087343497736577072507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25464232915993964205526685 9549087343497736577072507)
          ·
            refine ⟨14323631015246604865608761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9549087343497736577072507 14323631015246604865608761)
            ·
              refine ⟨10742723261434953649206571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14323631015246604865608761 10742723261434953649206571)
              ·
                refine ⟨16114084892152430473809857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10742723261434953649206571 16114084892152430473809857)
                ·
                  refine ⟨12085563669114322855357393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16114084892152430473809857 12085563669114322855357393)
                  ·
                    refine ⟨9064172751835742141518045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12085563669114322855357393 9064172751835742141518045)
                    ·
                      refine ⟨3399064781938403303069267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9064172751835742141518045 3399064781938403303069267)
                      ·
                        rfl

theorem cell23_6619655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_6619655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619655 prefixEnd_6619655 := by exact prefixLift 6619655
  have htrace : WordTrace (prefixWord ++ tailWord_6619655) baseStart_6619655 baseEnd_6619655 := by
    simpa [prefixWord, tailWord_6619655, baseEnd_6619655] using wordTrace_append hprefix tailTrace_6619655
  have hstable : (prefixWord ++ tailWord_6619655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619655).length < 2 ^ (prefixWord ++ tailWord_6619655).sum := by decide
  have hdescent : baseEnd_6619655 < baseStart_6619655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619688 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6619688 : Nat := 118140960795 + 6619688 * 2 ^ 59
def prefixEnd_6619688 : Nat := 4983230072969 + 3 ^ 40 * 6619688 * 2
def baseEnd_6619688 : Nat := 1133027242266667224652205

theorem tailTrace_6619688 : CollatzResearch.WordTrace tailWord_6619688 prefixEnd_6619688 1133027242266667224652205 := by
  unfold tailWord_6619688
  simp only [CollatzResearch.WordTrace]
  refine ⟨120719928221004201773805859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160959904294672269031741145 120719928221004201773805859)
  ·
    refine ⟨181079892331506302660708789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120719928221004201773805859 181079892331506302660708789)
    ·
      refine ⟨16976239906078715874441449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181079892331506302660708789 16976239906078715874441449)
      ·
        refine ⟨12732179929559036905831087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16976239906078715874441449 12732179929559036905831087)
        ·
          refine ⟨19098269894338555358746631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12732179929559036905831087 19098269894338555358746631)
          ·
            refine ⟨28647404841507833038119947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19098269894338555358746631 28647404841507833038119947)
            ·
              refine ⟨42971107262261749557179921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28647404841507833038119947 42971107262261749557179921)
              ·
                refine ⟨32228330446696312167884941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42971107262261749557179921 32228330446696312167884941)
                ·
                  refine ⟨12085623917511117062956853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32228330446696312167884941 12085623917511117062956853)
                  ·
                    refine ⟨1133027242266667224652205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12085623917511117062956853 1133027242266667224652205)
                    ·
                      rfl

theorem cell23_6619688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6619688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619688 prefixEnd_6619688 := by exact prefixLift 6619688
  have htrace : WordTrace (prefixWord ++ tailWord_6619688) baseStart_6619688 baseEnd_6619688 := by
    simpa [prefixWord, tailWord_6619688, baseEnd_6619688] using wordTrace_append hprefix tailTrace_6619688
  have hstable : (prefixWord ++ tailWord_6619688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619688).length < 2 ^ (prefixWord ++ tailWord_6619688).sum := by decide
  have hdescent : baseEnd_6619688 < baseStart_6619688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619702 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_6619702 : Nat := 118140960795 + 6619702 * 2 ^ 59
def prefixEnd_6619702 : Nat := 4983230072969 + 3 ^ 40 * 6619702 * 2
def baseEnd_6619702 : Nat := 3399088915529164619181551

theorem tailTrace_6619702 : CollatzResearch.WordTrace tailWord_6619702 prefixEnd_6619702 3399088915529164619181551 := by
  unfold tailWord_6619702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090022941497355246163835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160960244709305122625747573 15090022941497355246163835)
  ·
    refine ⟨22635034412246032869245753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15090022941497355246163835 22635034412246032869245753)
    ·
      refine ⟨16976275809184524651934315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22635034412246032869245753 16976275809184524651934315)
      ·
        refine ⟨25464413713776786977901473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16976275809184524651934315 25464413713776786977901473)
        ·
          refine ⟨19098310285332590233426105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25464413713776786977901473 19098310285332590233426105)
          ·
            refine ⟨14323732713999442675069579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19098310285332590233426105 14323732713999442675069579)
            ·
              refine ⟨21485599070999164012604369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14323732713999442675069579 21485599070999164012604369)
              ·
                refine ⟨16114199303249373009453277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21485599070999164012604369 16114199303249373009453277)
                ·
                  refine ⟨6042824738718514878544979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16114199303249373009453277 6042824738718514878544979)
                  ·
                    refine ⟨9064237108077772317817469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6042824738718514878544979 9064237108077772317817469)
                    ·
                      refine ⟨3399088915529164619181551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9064237108077772317817469 3399088915529164619181551)
                      ·
                        rfl

theorem cell23_6619702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_6619702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619702 prefixEnd_6619702 := by exact prefixLift 6619702
  have htrace : WordTrace (prefixWord ++ tailWord_6619702) baseStart_6619702 baseEnd_6619702 := by
    simpa [prefixWord, tailWord_6619702, baseEnd_6619702] using wordTrace_append hprefix tailTrace_6619702
  have hstable : (prefixWord ++ tailWord_6619702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619702).length < 2 ^ (prefixWord ++ tailWord_6619702).sum := by decide
  have hdescent : baseEnd_6619702 < baseStart_6619702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619708 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_6619708 : Nat := 118140960795 + 6619708 * 2 ^ 59
def prefixEnd_6619708 : Nat := 4983230072969 + 3 ^ 40 * 6619708 * 2
def baseEnd_6619708 : Nat := 3399091996413091595706523

theorem tailTrace_6619708 : CollatzResearch.WordTrace tailWord_6619708 prefixEnd_6619708 3399091996413091595706523 := by
  unfold tailWord_6619708
  simp only [CollatzResearch.WordTrace]
  refine ⟨120720292950967973481669889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160960390601290631308893185 120720292950967973481669889)
  ·
    refine ⟨90540219713225980111252417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120720292950967973481669889 90540219713225980111252417)
    ·
      refine ⟨67905164784919485083439313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90540219713225980111252417 67905164784919485083439313)
      ·
        refine ⟨50928873588689613812579485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67905164784919485083439313 50928873588689613812579485)
        ·
          refine ⟨19098327595758605179717307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50928873588689613812579485 19098327595758605179717307)
          ·
            refine ⟨28647491393637907769575961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19098327595758605179717307 28647491393637907769575961)
            ·
              refine ⟨21485618545228430827181971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28647491393637907769575961 21485618545228430827181971)
              ·
                refine ⟨32228427817842646240772957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21485618545228430827181971 32228427817842646240772957)
                ·
                  refine ⟨12085660431690992340289859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32228427817842646240772957 12085660431690992340289859)
                  ·
                    refine ⟨18128490647536488510434789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12085660431690992340289859 18128490647536488510434789)
                    ·
                      refine ⟨3399091996413091595706523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18128490647536488510434789 3399091996413091595706523)
                      ·
                        rfl

theorem cell23_6619708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_6619708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619708 prefixEnd_6619708 := by exact prefixLift 6619708
  have htrace : WordTrace (prefixWord ++ tailWord_6619708) baseStart_6619708 baseEnd_6619708 := by
    simpa [prefixWord, tailWord_6619708, baseEnd_6619708] using wordTrace_append hprefix tailTrace_6619708
  have hstable : (prefixWord ++ tailWord_6619708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619708).length < 2 ^ (prefixWord ++ tailWord_6619708).sum := by decide
  have hdescent : baseEnd_6619708 < baseStart_6619708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619752 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 1, 6]
def baseStart_6619752 : Nat := 118140960795 + 6619752 * 2 ^ 59
def prefixEnd_6619752 : Nat := 4983230072969 + 3 ^ 40 * 6619752 * 2
def baseEnd_6619752 : Nat := 1133038196520629807852107

theorem tailTrace_6619752 : CollatzResearch.WordTrace tailWord_6619752 prefixEnd_6619752 1133038196520629807852107 := by
  unfold tailWord_6619752
  simp only [CollatzResearch.WordTrace]
  refine ⟨120721095356888271238970755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160961460475851028318627673 120721095356888271238970755)
  ·
    refine ⟨181081643035332406858456133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120721095356888271238970755 181081643035332406858456133)
    ·
      refine ⟨33952808069124826285960525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181081643035332406858456133 33952808069124826285960525)
      ·
        refine ⟨12732303025921809857235197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33952808069124826285960525 12732303025921809857235197)
        ·
          refine ⟨4774613634720678696463199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12732303025921809857235197 4774613634720678696463199)
          ·
            refine ⟨7161920452081018044694799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774613634720678696463199 7161920452081018044694799)
            ·
              refine ⟨10742880678121527067042199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161920452081018044694799 10742880678121527067042199)
              ·
                refine ⟨16114321017182290600563299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10742880678121527067042199 16114321017182290600563299)
                ·
                  refine ⟨24171481525773435900844949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16114321017182290600563299 24171481525773435900844949)
                  ·
                    refine ⟨1133038196520629807852107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24171481525773435900844949 1133038196520629807852107)
                    ·
                      rfl

theorem cell23_6619752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_6619752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619752 prefixEnd_6619752 := by exact prefixLift 6619752
  have htrace : WordTrace (prefixWord ++ tailWord_6619752) baseStart_6619752 baseEnd_6619752 := by
    simpa [prefixWord, tailWord_6619752, baseEnd_6619752] using wordTrace_append hprefix tailTrace_6619752
  have hstable : (prefixWord ++ tailWord_6619752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619752).length < 2 ^ (prefixWord ++ tailWord_6619752).sum := by decide
  have hdescent : baseEnd_6619752 < baseStart_6619752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619762 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_6619762 : Nat := 118140960795 + 6619762 * 2 ^ 59
def prefixEnd_6619762 : Nat := 4983230072969 + 3 ^ 40 * 6619762 * 2
def baseEnd_6619762 : Nat := 3399119724368434384431275

theorem tailTrace_6619762 : CollatzResearch.WordTrace tailWord_6619762 prefixEnd_6619762 3399119724368434384431275 := by
  unfold tailWord_6619762
  simp only [CollatzResearch.WordTrace]
  refine ⟨60360638860935078546451385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160961703629160209457203693 60360638860935078546451385)
  ·
    refine ⟨45270479145701308909838539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60360638860935078546451385 45270479145701308909838539)
    ·
      refine ⟨67905718718551963364757809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45270479145701308909838539 67905718718551963364757809)
      ·
        refine ⟨50929289038913972523568357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67905718718551963364757809 50929289038913972523568357)
        ·
          refine ⟨9549241694796369848169067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50929289038913972523568357 9549241694796369848169067)
          ·
            refine ⟨14323862542194554772253601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9549241694796369848169067 14323862542194554772253601)
            ·
              refine ⟨10742896906645916079190201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14323862542194554772253601 10742896906645916079190201)
              ·
                refine ⟨8057172679984437059392651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10742896906645916079190201 8057172679984437059392651)
                ·
                  refine ⟨12085759019976655589088977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8057172679984437059392651 12085759019976655589088977)
                  ·
                    refine ⟨9064319264982491691816733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12085759019976655589088977 9064319264982491691816733)
                    ·
                      refine ⟨3399119724368434384431275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9064319264982491691816733 3399119724368434384431275)
                      ·
                        rfl

theorem cell23_6619762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_6619762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619762 prefixEnd_6619762 := by exact prefixLift 6619762
  have htrace : WordTrace (prefixWord ++ tailWord_6619762) baseStart_6619762 baseEnd_6619762 := by
    simpa [prefixWord, tailWord_6619762, baseEnd_6619762] using wordTrace_append hprefix tailTrace_6619762
  have hstable : (prefixWord ++ tailWord_6619762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619762).length < 2 ^ (prefixWord ++ tailWord_6619762).sum := by decide
  have hdescent : baseEnd_6619762 < baseStart_6619762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619801 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_6619801 : Nat := 118140960795 + 6619801 * 2 ^ 59
def prefixEnd_6619801 : Nat := 4983230072969 + 3 ^ 40 * 6619801 * 2
def baseEnd_6619801 : Nat := 3399139750113959731843595

theorem tailTrace_6619801 : CollatzResearch.WordTrace tailWord_6619801 prefixEnd_6619801 3399139750113959731843595 := by
  unfold tailWord_6619801
  simp only [CollatzResearch.WordTrace]
  refine ⟨241443977890599023846475257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160962651927066015897650171 241443977890599023846475257)
  ·
    refine ⟨181082983417949267884856443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241443977890599023846475257 181082983417949267884856443)
    ·
      refine ⟨271624475126923901827284665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181082983417949267884856443 271624475126923901827284665)
      ·
        refine ⟨203718356345192926370463499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271624475126923901827284665 203718356345192926370463499)
        ·
          refine ⟨305577534517789389555695249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203718356345192926370463499 305577534517789389555695249)
          ·
            refine ⟨229183150888342042166771437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305577534517789389555695249 229183150888342042166771437)
            ·
              refine ⟨85943681583128265812539289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229183150888342042166771437 85943681583128265812539289)
              ·
                refine ⟨64457761187346199359404467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85943681583128265812539289 64457761187346199359404467)
                ·
                  refine ⟨96686641781019299039106701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64457761187346199359404467 96686641781019299039106701)
                  ·
                    refine ⟨36257490667882237139665013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96686641781019299039106701 36257490667882237139665013)
                    ·
                      refine ⟨3399139750113959731843595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36257490667882237139665013 3399139750113959731843595)
                      ·
                        rfl

theorem cell23_6619801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_6619801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619801 prefixEnd_6619801 := by exact prefixLift 6619801
  have htrace : WordTrace (prefixWord ++ tailWord_6619801) baseStart_6619801 baseEnd_6619801 := by
    simpa [prefixWord, tailWord_6619801, baseEnd_6619801] using wordTrace_append hprefix tailTrace_6619801
  have hstable : (prefixWord ++ tailWord_6619801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619801).length < 2 ^ (prefixWord ++ tailWord_6619801).sum := by decide
  have hdescent : baseEnd_6619801 < baseStart_6619801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619851 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 5, 7]
def baseStart_6619851 : Nat := 118140960795 + 6619851 * 2 ^ 59
def prefixEnd_6619851 : Nat := 4983230072969 + 3 ^ 40 * 6619851 * 2
def baseEnd_6619851 : Nat := 1133055141382228178739455

theorem tailTrace_6619851 : CollatzResearch.WordTrace tailWord_6619851 prefixEnd_6619851 1133055141382228178739455 := by
  unfold tailWord_6619851
  simp only [CollatzResearch.WordTrace]
  refine ⟨241445801540417882385795407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160963867693611921590530271 241445801540417882385795407)
  ·
    refine ⟨362168702310626823578693111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241445801540417882385795407 362168702310626823578693111)
    ·
      refine ⟨543253053465940235368039667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362168702310626823578693111 543253053465940235368039667)
      ·
        refine ⟨814879580198910353052059501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543253053465940235368039667 814879580198910353052059501)
        ·
          refine ⟨305579842574591382394522313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814879580198910353052059501 305579842574591382394522313)
          ·
            refine ⟨229184881930943536795891735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305579842574591382394522313 229184881930943536795891735)
            ·
              refine ⟨343777322896415305193837603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229184881930943536795891735 343777322896415305193837603)
              ·
                refine ⟨515665984344622957790756405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343777322896415305193837603 515665984344622957790756405)
                ·
                  refine ⟨48343686032308402292883413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 515665984344622957790756405 48343686032308402292883413)
                  ·
                    refine ⟨1133055141382228178739455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48343686032308402292883413 1133055141382228178739455)
                    ·
                      rfl

theorem cell23_6619851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 7].length) (baseStart_6619851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619851 prefixEnd_6619851 := by exact prefixLift 6619851
  have htrace : WordTrace (prefixWord ++ tailWord_6619851) baseStart_6619851 baseEnd_6619851 := by
    simpa [prefixWord, tailWord_6619851, baseEnd_6619851] using wordTrace_append hprefix tailTrace_6619851
  have hstable : (prefixWord ++ tailWord_6619851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619851).length < 2 ^ (prefixWord ++ tailWord_6619851).sum := by decide
  have hdescent : baseEnd_6619851 < baseStart_6619851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619888 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_6619888 : Nat := 118140960795 + 6619888 * 2 ^ 59
def prefixEnd_6619888 : Nat := 4983230072969 + 3 ^ 40 * 6619888 * 2
def baseEnd_6619888 : Nat := 3399184422930900891455695

theorem tailTrace_6619888 : CollatzResearch.WordTrace tailWord_6619888 prefixEnd_6619888 3399184422930900891455695 := by
  unfold tailWord_6619888
  simp only [CollatzResearch.WordTrace]
  refine ⟨120723575520641918852446159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160964767360855891803261545 120723575520641918852446159)
  ·
    refine ⟨181085363280962878278669239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120723575520641918852446159 181085363280962878278669239)
    ·
      refine ⟨271628044921444317418003859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181085363280962878278669239 271628044921444317418003859)
      ·
        refine ⟨407442067382166476127005789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271628044921444317418003859 407442067382166476127005789)
        ·
          refine ⟨152790775268312428547627171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407442067382166476127005789 152790775268312428547627171)
          ·
            refine ⟨229186162902468642821440757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152790775268312428547627171 229186162902468642821440757)
            ·
              refine ⟨21486202772106435264510071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229186162902468642821440757 21486202772106435264510071)
              ·
                refine ⟨32229304158159652896765107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21486202772106435264510071 32229304158159652896765107)
                ·
                  refine ⟨48343956237239479345147661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32229304158159652896765107 48343956237239479345147661)
                  ·
                    refine ⟨18128983588964804754430373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48343956237239479345147661 18128983588964804754430373)
                    ·
                      refine ⟨3399184422930900891455695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18128983588964804754430373 3399184422930900891455695)
                      ·
                        rfl

theorem cell23_6619888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_6619888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619888 prefixEnd_6619888 := by exact prefixLift 6619888
  have htrace : WordTrace (prefixWord ++ tailWord_6619888) baseStart_6619888 baseEnd_6619888 := by
    simpa [prefixWord, tailWord_6619888, baseEnd_6619888] using wordTrace_append hprefix tailTrace_6619888
  have hstable : (prefixWord ++ tailWord_6619888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619888).length < 2 ^ (prefixWord ++ tailWord_6619888).sum := by decide
  have hdescent : baseEnd_6619888 < baseStart_6619888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619918 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_6619918 : Nat := 118140960795 + 6619918 * 2 ^ 59
def prefixEnd_6619918 : Nat := 4983230072969 + 3 ^ 40 * 6619918 * 2
def baseEnd_6619918 : Nat := 3399199827350535774080557

theorem tailTrace_6619918 : CollatzResearch.WordTrace tailWord_6619918 prefixEnd_6619918 3399199827350535774080557 := by
  unfold tailWord_6619918
  simp only [CollatzResearch.WordTrace]
  refine ⟨30181030653896894103560551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160965496820783435218989605 30181030653896894103560551)
  ·
    refine ⟨45271545980845341155340827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30181030653896894103560551 45271545980845341155340827)
    ·
      refine ⟨67907318971268011733011241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45271545980845341155340827 67907318971268011733011241)
      ·
        refine ⟨50930489228451008799758431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67907318971268011733011241 50930489228451008799758431)
        ·
          refine ⟨76395733842676513199637647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50930489228451008799758431 76395733842676513199637647)
          ·
            refine ⟨114593600764014769799456471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76395733842676513199637647 114593600764014769799456471)
            ·
              refine ⟨171890401146022154699184707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114593600764014769799456471 171890401146022154699184707)
              ·
                refine ⟨257835601719033232048777061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171890401146022154699184707 257835601719033232048777061)
                ·
                  refine ⟨48344175322318731009145699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257835601719033232048777061 48344175322318731009145699)
                  ·
                    refine ⟨72516262983478096513718549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48344175322318731009145699 72516262983478096513718549)
                    ·
                      refine ⟨3399199827350535774080557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72516262983478096513718549 3399199827350535774080557)
                      ·
                        rfl

theorem cell23_6619918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_6619918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619918 prefixEnd_6619918 := by exact prefixLift 6619918
  have htrace : WordTrace (prefixWord ++ tailWord_6619918) baseStart_6619918 baseEnd_6619918 := by
    simpa [prefixWord, tailWord_6619918, baseEnd_6619918] using wordTrace_append hprefix tailTrace_6619918
  have hstable : (prefixWord ++ tailWord_6619918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619918).length < 2 ^ (prefixWord ++ tailWord_6619918).sum := by decide
  have hdescent : baseEnd_6619918 < baseStart_6619918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6619966 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_6619966 : Nat := 118140960795 + 6619966 * 2 ^ 59
def prefixEnd_6619966 : Nat := 4983230072969 + 3 ^ 40 * 6619966 * 2
def baseEnd_6619966 : Nat := 1133074824807317195426779

theorem tailTrace_6619966 : CollatzResearch.WordTrace tailWord_6619966 prefixEnd_6619966 1133074824807317195426779 := by
  unfold tailWord_6619966
  simp only [CollatzResearch.WordTrace]
  refine ⟨30181249491875157128278969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160966663956667504684154501 30181249491875157128278969)
  ·
    refine ⟨22635937118906367846209227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30181249491875157128278969 22635937118906367846209227)
    ·
      refine ⟨33953905678359551769313841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22635937118906367846209227 33953905678359551769313841)
      ·
        refine ⟨25465429258769663826985381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33953905678359551769313841 25465429258769663826985381)
        ·
          refine ⟨4774767986019311967559759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25465429258769663826985381 4774767986019311967559759)
          ·
            refine ⟨7162151979028967951339639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774767986019311967559759 7162151979028967951339639)
            ·
              refine ⟨10743227968543451927009459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7162151979028967951339639 10743227968543451927009459)
              ·
                refine ⟨16114841952815177890514189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10743227968543451927009459 16114841952815177890514189)
                ·
                  refine ⟨6043065732305691708942821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16114841952815177890514189 6043065732305691708942821)
                  ·
                    refine ⟨1133074824807317195426779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6043065732305691708942821 1133074824807317195426779)
                    ·
                      rfl

theorem cell23_6619966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_6619966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6619966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6619966 prefixEnd_6619966 := by exact prefixLift 6619966
  have htrace : WordTrace (prefixWord ++ tailWord_6619966) baseStart_6619966 baseEnd_6619966 := by
    simpa [prefixWord, tailWord_6619966, baseEnd_6619966] using wordTrace_append hprefix tailTrace_6619966
  have hstable : (prefixWord ++ tailWord_6619966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6619966).length < 2 ^ (prefixWord ++ tailWord_6619966).sum := by decide
  have hdescent : baseEnd_6619966 < baseStart_6619966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6619966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620005 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_6620005 : Nat := 118140960795 + 6620005 * 2 ^ 59
def prefixEnd_6620005 : Nat := 4983230072969 + 3 ^ 40 * 6620005 * 2
def baseEnd_6620005 : Nat := 1133081500055825644564219

theorem tailTrace_6620005 : CollatzResearch.WordTrace tailWord_6620005 prefixEnd_6620005 1133081500055825644564219 := by
  unfold tailWord_6620005
  simp only [CollatzResearch.WordTrace]
  refine ⟨241451418381859966686901469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160967612254573311124600979 241451418381859966686901469)
  ·
    refine ⟨90544281893197487507588051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241451418381859966686901469 90544281893197487507588051)
    ·
      refine ⟨135816422839796231261382077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90544281893197487507588051 135816422839796231261382077)
      ·
        refine ⟨50931158564923586723018279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135816422839796231261382077 50931158564923586723018279)
        ·
          refine ⟨76396737847385380084527419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50931158564923586723018279 76396737847385380084527419)
          ·
            refine ⟨114595106771078070126791129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76396737847385380084527419 114595106771078070126791129)
            ·
              refine ⟨85946330078308552595093347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114595106771078070126791129 85946330078308552595093347)
              ·
                refine ⟨128919495117462828892640021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85946330078308552595093347 128919495117462828892640021)
                ·
                  refine ⟨6043101333631070104342501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128919495117462828892640021 6043101333631070104342501)
                  ·
                    refine ⟨1133081500055825644564219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6043101333631070104342501 1133081500055825644564219)
                    ·
                      rfl

theorem cell23_6620005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_6620005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620005 prefixEnd_6620005 := by exact prefixLift 6620005
  have htrace : WordTrace (prefixWord ++ tailWord_6620005) baseStart_6620005 baseEnd_6620005 := by
    simpa [prefixWord, tailWord_6620005, baseEnd_6620005] using wordTrace_append hprefix tailTrace_6620005
  have hstable : (prefixWord ++ tailWord_6620005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620005).length < 2 ^ (prefixWord ++ tailWord_6620005).sum := by decide
  have hdescent : baseEnd_6620005 < baseStart_6620005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620042 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6620042 : Nat := 118140960795 + 6620042 * 2 ^ 59
def prefixEnd_6620042 : Nat := 4983230072969 + 3 ^ 40 * 6620042 * 2
def baseEnd_6620042 : Nat := 3399263498951693288929987

theorem tailTrace_6620042 : CollatzResearch.WordTrace tailWord_6620042 prefixEnd_6620042 3399263498951693288929987 := by
  unfold tailWord_6620042
  simp only [CollatzResearch.WordTrace]
  refine ⟨60363191970681480501499595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160968511921817281337332253 60363191970681480501499595)
  ·
    refine ⟨90544787956022220752249393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60363191970681480501499595 90544787956022220752249393)
    ·
      refine ⟨67908590967016665564187045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90544787956022220752249393 67908590967016665564187045)
      ·
        refine ⟨12732860806315624793285071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67908590967016665564187045 12732860806315624793285071)
        ·
          refine ⟨19099291209473437189927607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12732860806315624793285071 19099291209473437189927607)
          ·
            refine ⟨28648936814210155784891411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19099291209473437189927607 28648936814210155784891411)
            ·
              refine ⟨42973405221315233677337117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28648936814210155784891411 42973405221315233677337117)
              ·
                refine ⟨16115026957993212629001419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42973405221315233677337117 16115026957993212629001419)
                ·
                  refine ⟨24172540436989818943502129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16115026957993212629001419 24172540436989818943502129)
                  ·
                    refine ⟨18129405327742364207626597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24172540436989818943502129 18129405327742364207626597)
                    ·
                      refine ⟨3399263498951693288929987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18129405327742364207626597 3399263498951693288929987)
                      ·
                        rfl

theorem cell23_6620042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6620042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620042 prefixEnd_6620042 := by exact prefixLift 6620042
  have htrace : WordTrace (prefixWord ++ tailWord_6620042) baseStart_6620042 baseEnd_6620042 := by
    simpa [prefixWord, tailWord_6620042, baseEnd_6620042] using wordTrace_append hprefix tailTrace_6620042
  have hstable : (prefixWord ++ tailWord_6620042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620042).length < 2 ^ (prefixWord ++ tailWord_6620042).sum := by decide
  have hdescent : baseEnd_6620042 < baseStart_6620042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620048 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 3, 9]
def baseStart_6620048 : Nat := 118140960795 + 6620048 * 2 ^ 59
def prefixEnd_6620048 : Nat := 4983230072969 + 3 ^ 40 * 6620048 * 2
def baseEnd_6620048 : Nat := 1133088859945206755151653

theorem tailTrace_6620048 : CollatzResearch.WordTrace tailWord_6620048 prefixEnd_6620048 1133088859945206755151653 := by
  unfold tailWord_6620048
  simp only [CollatzResearch.WordTrace]
  refine ⟨120726493360352092515358399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160968657813802790020477865 120726493360352092515358399)
  ·
    refine ⟨181089740040528138773037599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120726493360352092515358399 181089740040528138773037599)
    ·
      refine ⟨271634610060792208159556399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181089740040528138773037599 271634610060792208159556399)
      ·
        refine ⟨407451915091188312239334599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271634610060792208159556399 407451915091188312239334599)
        ·
          refine ⟨611177872636782468359001899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407451915091188312239334599 611177872636782468359001899)
          ·
            refine ⟨916766808955173702538502849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611177872636782468359001899 916766808955173702538502849)
            ·
              refine ⟨687575106716380276903877137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916766808955173702538502849 687575106716380276903877137)
              ·
                refine ⟨515681330037285207677907853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687575106716380276903877137 515681330037285207677907853)
                ·
                  refine ⟨193380498763981952879215445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515681330037285207677907853 193380498763981952879215445)
                  ·
                    refine ⟨1133088859945206755151653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 193380498763981952879215445 1133088859945206755151653)
                    ·
                      rfl

theorem cell23_6620048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_6620048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620048 prefixEnd_6620048 := by exact prefixLift 6620048
  have htrace : WordTrace (prefixWord ++ tailWord_6620048) baseStart_6620048 baseEnd_6620048 := by
    simpa [prefixWord, tailWord_6620048, baseEnd_6620048] using wordTrace_append hprefix tailTrace_6620048
  have hstable : (prefixWord ++ tailWord_6620048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620048).length < 2 ^ (prefixWord ++ tailWord_6620048).sum := by decide
  have hdescent : baseEnd_6620048 < baseStart_6620048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620052 : List Nat := [2, 4, 2, 1, 1, 1, 5, 7]
def baseStart_6620052 : Nat := 118140960795 + 6620052 * 2 ^ 59
def prefixEnd_6620052 : Nat := 4983230072969 + 3 ^ 40 * 6620052 * 2
def baseEnd_6620052 : Nat := 125898838287342157400183

theorem tailTrace_6620052 : CollatzResearch.WordTrace tailWord_6620052 prefixEnd_6620052 125898838287342157400183 := by
  unfold tailWord_6620052
  simp only [CollatzResearch.WordTrace]
  refine ⟨120726566306344846856931205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160968755075126462475908273 120726566306344846856931205)
  ·
    refine ⟨22636231182439658785674601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120726566306344846856931205 22636231182439658785674601)
    ·
      refine ⟨16977173386829744089255951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22636231182439658785674601 16977173386829744089255951)
      ·
        refine ⟨25465760080244616133883927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16977173386829744089255951 25465760080244616133883927)
        ·
          refine ⟨38198640120366924200825891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25465760080244616133883927 38198640120366924200825891)
          ·
            refine ⟨57297960180550386301238837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38198640120366924200825891 57297960180550386301238837)
            ·
              refine ⟨5371683766926598715741141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57297960180550386301238837 5371683766926598715741141)
              ·
                refine ⟨125898838287342157400183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5371683766926598715741141 125898838287342157400183)
                ·
                  rfl

theorem cell23_6620052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 7].length) (baseStart_6620052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620052 prefixEnd_6620052 := by exact prefixLift 6620052
  have htrace : WordTrace (prefixWord ++ tailWord_6620052) baseStart_6620052 baseEnd_6620052 := by
    simpa [prefixWord, tailWord_6620052, baseEnd_6620052] using wordTrace_append hprefix tailTrace_6620052
  have hstable : (prefixWord ++ tailWord_6620052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620052).length < 2 ^ (prefixWord ++ tailWord_6620052).sum := by decide
  have hdescent : baseEnd_6620052 < baseStart_6620052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620063 : List Nat := [1, 1, 2, 5, 2, 2, 2, 3, 1, 2, 2]
def baseStart_6620063 : Nat := 118140960795 + 6620063 * 2 ^ 59
def prefixEnd_6620063 : Nat := 4983230072969 + 3 ^ 40 * 6620063 * 2
def baseEnd_6620063 : Nat := 3399274282045437706767391

theorem tailTrace_6620063 : CollatzResearch.WordTrace tailWord_6620063 prefixEnd_6620063 3399274282045437706767391 := by
  unfold tailWord_6620063
  simp only [CollatzResearch.WordTrace]
  refine ⟨241453533815649842592512843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160969022543766561728341895 241453533815649842592512843)
  ·
    refine ⟨362180300723474763888769265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241453533815649842592512843 362180300723474763888769265)
    ·
      refine ⟨271635225542606072916576949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362180300723474763888769265 271635225542606072916576949)
      ·
        refine ⟨25465802394619319335929089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271635225542606072916576949 25465802394619319335929089)
        ·
          refine ⟨19099351795964489501946817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25465802394619319335929089 19099351795964489501946817)
          ·
            refine ⟨14324513846973367126460113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19099351795964489501946817 14324513846973367126460113)
            ·
              refine ⟨10743385385230025344845085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14324513846973367126460113 10743385385230025344845085)
              ·
                refine ⟨4028769519461259504316907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10743385385230025344845085 4028769519461259504316907)
                ·
                  refine ⟨6043154279191889256475361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4028769519461259504316907 6043154279191889256475361)
                  ·
                    refine ⟨4532365709393916942356521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6043154279191889256475361 4532365709393916942356521)
                    ·
                      refine ⟨3399274282045437706767391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4532365709393916942356521 3399274282045437706767391)
                      ·
                        rfl

theorem cell23_6620063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_6620063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620063 prefixEnd_6620063 := by exact prefixLift 6620063
  have htrace : WordTrace (prefixWord ++ tailWord_6620063) baseStart_6620063 baseEnd_6620063 := by
    simpa [prefixWord, tailWord_6620063, baseEnd_6620063] using wordTrace_append hprefix tailTrace_6620063
  have hstable : (prefixWord ++ tailWord_6620063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620063).length < 2 ^ (prefixWord ++ tailWord_6620063).sum := by decide
  have hdescent : baseEnd_6620063 < baseStart_6620063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620066 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_6620066 : Nat := 118140960795 + 6620066 * 2 ^ 59
def prefixEnd_6620066 : Nat := 4983230072969 + 3 ^ 40 * 6620066 * 2
def baseEnd_6620066 : Nat := 3399275822487401195029877

theorem tailTrace_6620066 : CollatzResearch.WordTrace tailWord_6620066 prefixEnd_6620066 3399275822487401195029877 := by
  unfold tailWord_6620066
  simp only [CollatzResearch.WordTrace]
  refine ⟨60363410808659743526218013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160969095489759316069914701 60363410808659743526218013)
  ·
    refine ⟨22636279053247403822331755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60363410808659743526218013 22636279053247403822331755)
    ·
      refine ⟨33954418579871105733497633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22636279053247403822331755 33954418579871105733497633)
      ·
        refine ⟨25465813934903329300123225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33954418579871105733497633 25465813934903329300123225)
        ·
          refine ⟨19099360451177496975092419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25465813934903329300123225 19099360451177496975092419)
          ·
            refine ⟨28649040676766245462638629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19099360451177496975092419 28649040676766245462638629)
            ·
              refine ⟨5371695126893671024244743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28649040676766245462638629 5371695126893671024244743)
              ·
                refine ⟨8057542690340506536367115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371695126893671024244743 8057542690340506536367115)
                ·
                  refine ⟨12086314035510759804550673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8057542690340506536367115 12086314035510759804550673)
                  ·
                    refine ⟨9064735526633069853413005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12086314035510759804550673 9064735526633069853413005)
                    ·
                      refine ⟨3399275822487401195029877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9064735526633069853413005 3399275822487401195029877)
                      ·
                        rfl

theorem cell23_6620066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_6620066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620066 prefixEnd_6620066 := by exact prefixLift 6620066
  have htrace : WordTrace (prefixWord ++ tailWord_6620066) baseStart_6620066 baseEnd_6620066 := by
    simpa [prefixWord, tailWord_6620066, baseEnd_6620066] using wordTrace_append hprefix tailTrace_6620066
  have hstable : (prefixWord ++ tailWord_6620066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620066).length < 2 ^ (prefixWord ++ tailWord_6620066).sum := by decide
  have hdescent : baseEnd_6620066 < baseStart_6620066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620096 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 2, 1, 3]
def baseStart_6620096 : Nat := 118140960795 + 6620096 * 2 ^ 59
def prefixEnd_6620096 : Nat := 4983230072969 + 3 ^ 40 * 6620096 * 2
def baseEnd_6620096 : Nat := 3399291226907036077654739

theorem tailTrace_6620096 : CollatzResearch.WordTrace tailWord_6620096 prefixEnd_6620096 3399291226907036077654739 := by
  unfold tailWord_6620096
  simp only [CollatzResearch.WordTrace]
  refine ⟨120727368712265144614232071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160969824949686859485642761 120727368712265144614232071)
  ·
    refine ⟨181091053068397716921348107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120727368712265144614232071 181091053068397716921348107)
    ·
      refine ⟨271636579602596575382022161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181091053068397716921348107 271636579602596575382022161)
      ·
        refine ⟨203727434701947431536516621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271636579602596575382022161 203727434701947431536516621)
        ·
          refine ⟨76397788013230286826193733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203727434701947431536516621 76397788013230286826193733)
          ·
            refine ⟨14324585252480678779911325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76397788013230286826193733 14324585252480678779911325)
            ·
              refine ⟨5371719469680254542466747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14324585252480678779911325 5371719469680254542466747)
              ·
                refine ⟨8057579204520381813700121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371719469680254542466747 8057579204520381813700121)
                ·
                  refine ⟨6043184403390286360275091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8057579204520381813700121 6043184403390286360275091)
                  ·
                    refine ⟨9064776605085429540412637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6043184403390286360275091 9064776605085429540412637)
                    ·
                      refine ⟨3399291226907036077654739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9064776605085429540412637 3399291226907036077654739)
                      ·
                        rfl

theorem cell23_6620096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_6620096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620096 prefixEnd_6620096 := by exact prefixLift 6620096
  have htrace : WordTrace (prefixWord ++ tailWord_6620096) baseStart_6620096 baseEnd_6620096 := by
    simpa [prefixWord, tailWord_6620096, baseEnd_6620096] using wordTrace_append hprefix tailTrace_6620096
  have hstable : (prefixWord ++ tailWord_6620096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620096).length < 2 ^ (prefixWord ++ tailWord_6620096).sum := by decide
  have hdescent : baseEnd_6620096 < baseStart_6620096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620122 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_6620122 : Nat := 118140960795 + 6620122 * 2 ^ 59
def prefixEnd_6620122 : Nat := 4983230072969 + 3 ^ 40 * 6620122 * 2
def baseEnd_6620122 : Nat := 3399304577404052975929619

theorem tailTrace_6620122 : CollatzResearch.WordTrace tailWord_6620122 prefixEnd_6620122 3399304577404052975929619 := by
  unfold tailWord_6620122
  simp only [CollatzResearch.WordTrace]
  refine ⟨60363921430609023917227655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160970457148290730445940413 60363921430609023917227655)
  ·
    refine ⟨90545882145913535875841483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60363921430609023917227655 90545882145913535875841483)
    ·
      refine ⟨135818823218870303813762225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90545882145913535875841483 135818823218870303813762225)
      ·
        refine ⟨101864117414152727860321669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135818823218870303813762225 101864117414152727860321669)
        ·
          refine ⟨19099522015153636473810313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101864117414152727860321669 19099522015153636473810313)
          ·
            refine ⟨14324641511365227355357735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19099522015153636473810313 14324641511365227355357735)
            ·
              refine ⟨21486962267047841033036603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14324641511365227355357735 21486962267047841033036603)
              ·
                refine ⟨32230443400571761549554905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21486962267047841033036603 32230443400571761549554905)
                ·
                  refine ⟨24172832550428821162166179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32230443400571761549554905 24172832550428821162166179)
                  ·
                    refine ⟨36259248825643231743249269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24172832550428821162166179 36259248825643231743249269)
                    ·
                      refine ⟨3399304577404052975929619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36259248825643231743249269 3399304577404052975929619)
                      ·
                        rfl

theorem cell23_6620122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_6620122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620122 prefixEnd_6620122 := by exact prefixLift 6620122
  have htrace : WordTrace (prefixWord ++ tailWord_6620122) baseStart_6620122 baseEnd_6620122 := by
    simpa [prefixWord, tailWord_6620122, baseEnd_6620122] using wordTrace_append hprefix tailTrace_6620122
  have hstable : (prefixWord ++ tailWord_6620122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620122).length < 2 ^ (prefixWord ++ tailWord_6620122).sum := by decide
  have hdescent : baseEnd_6620122 < baseStart_6620122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620155 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 6, 5]
def baseStart_6620155 : Nat := 118140960795 + 6620155 * 2 ^ 59
def prefixEnd_6620155 : Nat := 4983230072969 + 3 ^ 40 * 6620155 * 2
def baseEnd_6620155 : Nat := 1133107174088550448938989

theorem tailTrace_6620155 : CollatzResearch.WordTrace tailWord_6620155 prefixEnd_6620155 1133107174088550448938989 := by
  unfold tailWord_6620155
  simp only [CollatzResearch.WordTrace]
  refine ⟨241456889331316542304861919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160971259554211028203241279 241456889331316542304861919)
  ·
    refine ⟨362185333996974813457292879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241456889331316542304861919 362185333996974813457292879)
    ·
      refine ⟨543278000995462220185939319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362185333996974813457292879 543278000995462220185939319)
      ·
        refine ⟨814917001493193330278908979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543278000995462220185939319 814917001493193330278908979)
        ·
          refine ⟨1222375502239789995418363469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814917001493193330278908979 1222375502239789995418363469)
          ·
            refine ⟨458390813339921248281886301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1222375502239789995418363469 458390813339921248281886301)
            ·
              refine ⟨171896555002470468105707363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458390813339921248281886301 171896555002470468105707363)
              ·
                refine ⟨257844832503705702158561045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171896555002470468105707363 257844832503705702158561045)
                ·
                  refine ⟨12086476523611204788682549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 257844832503705702158561045 12086476523611204788682549)
                  ·
                    refine ⟨1133107174088550448938989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12086476523611204788682549 1133107174088550448938989)
                    ·
                      rfl

theorem cell23_6620155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 5].length) (baseStart_6620155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620155 prefixEnd_6620155 := by exact prefixLift 6620155
  have htrace : WordTrace (prefixWord ++ tailWord_6620155) baseStart_6620155 baseEnd_6620155 := by
    simpa [prefixWord, tailWord_6620155, baseEnd_6620155] using wordTrace_append hprefix tailTrace_6620155
  have hstable : (prefixWord ++ tailWord_6620155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620155).length < 2 ^ (prefixWord ++ tailWord_6620155).sum := by decide
  have hdescent : baseEnd_6620155 < baseStart_6620155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620165 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_6620165 : Nat := 118140960795 + 6620165 * 2 ^ 59
def prefixEnd_6620165 : Nat := 4983230072969 + 3 ^ 40 * 6620165 * 2
def baseEnd_6620165 : Nat := 3399326657072196307691921

theorem tailTrace_6620165 : CollatzResearch.WordTrace tailWord_6620165 prefixEnd_6620165 3399326657072196307691921 := by
  unfold tailWord_6620165
  simp only [CollatzResearch.WordTrace]
  refine ⟨241457254061280314012725949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160971502707520209341817299 241457254061280314012725949)
  ·
    refine ⟨90546470272980117754772231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241457254061280314012725949 90546470272980117754772231)
    ·
      refine ⟨135819705409470176632158347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90546470272980117754772231 135819705409470176632158347)
      ·
        refine ⟨203729558114205264948237521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135819705409470176632158347 203729558114205264948237521)
        ·
          refine ⟨152797168585653948711178141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203729558114205264948237521 152797168585653948711178141)
          ·
            refine ⟨57298938219620230766691803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152797168585653948711178141 57298938219620230766691803)
            ·
              refine ⟨85948407329430346150037705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57298938219620230766691803 85948407329430346150037705)
              ·
                refine ⟨64461305497072759612528279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85948407329430346150037705 64461305497072759612528279)
                ·
                  refine ⟨96691958245609139418792419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64461305497072759612528279 96691958245609139418792419)
                  ·
                    refine ⟨145037937368413709128188629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96691958245609139418792419 145037937368413709128188629)
                    ·
                      refine ⟨3399326657072196307691921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145037937368413709128188629 3399326657072196307691921)
                      ·
                        rfl

theorem cell23_6620165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_6620165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620165 prefixEnd_6620165 := by exact prefixLift 6620165
  have htrace : WordTrace (prefixWord ++ tailWord_6620165) baseStart_6620165 baseEnd_6620165 := by
    simpa [prefixWord, tailWord_6620165, baseEnd_6620165] using wordTrace_append hprefix tailTrace_6620165
  have hstable : (prefixWord ++ tailWord_6620165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620165).length < 2 ^ (prefixWord ++ tailWord_6620165).sum := by decide
  have hdescent : baseEnd_6620165 < baseStart_6620165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620172 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_6620172 : Nat := 118140960795 + 6620172 * 2 ^ 59
def prefixEnd_6620172 : Nat := 4983230072969 + 3 ^ 40 * 6620172 * 2
def baseEnd_6620172 : Nat := 1133110083812259260101463

theorem tailTrace_6620172 : CollatzResearch.WordTrace tailWord_6620172 prefixEnd_6620172 1133110083812259260101463 := by
  unfold tailWord_6620172
  simp only [CollatzResearch.WordTrace]
  refine ⟨120728754686127477104115385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160971672914836636138820513 120728754686127477104115385)
  ·
    refine ⟨90546566014595607828086539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120728754686127477104115385 90546566014595607828086539)
    ·
      refine ⟨135819849021893411742129809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90546566014595607828086539 135819849021893411742129809)
      ·
        refine ⟨101864886766420058806597357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135819849021893411742129809 101864886766420058806597357)
        ·
          refine ⟨38199332537407522052474009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101864886766420058806597357 38199332537407522052474009)
          ·
            refine ⟨28649499403055641539355507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38199332537407522052474009 28649499403055641539355507)
            ·
              refine ⟨42974249104583462309033261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28649499403055641539355507 42974249104583462309033261)
              ·
                refine ⟨16115343414218798365887473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42974249104583462309033261 16115343414218798365887473)
                ·
                  refine ⟨12086507560664098774415605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16115343414218798365887473 12086507560664098774415605)
                  ·
                    refine ⟨1133110083812259260101463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12086507560664098774415605 1133110083812259260101463)
                    ·
                      rfl

theorem cell23_6620172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_6620172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620172 prefixEnd_6620172 := by exact prefixLift 6620172
  have htrace : WordTrace (prefixWord ++ tailWord_6620172) baseStart_6620172 baseEnd_6620172 := by
    simpa [prefixWord, tailWord_6620172, baseEnd_6620172] using wordTrace_append hprefix tailTrace_6620172
  have hstable : (prefixWord ++ tailWord_6620172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620172).length < 2 ^ (prefixWord ++ tailWord_6620172).sum := by decide
  have hdescent : baseEnd_6620172 < baseStart_6620172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620199 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6620199 : Nat := 118140960795 + 6620199 * 2 ^ 59
def prefixEnd_6620199 : Nat := 4983230072969 + 3 ^ 40 * 6620199 * 2
def baseEnd_6620199 : Nat := 3399344115414449174666765

theorem tailTrace_6620199 : CollatzResearch.WordTrace tailWord_6620199 prefixEnd_6620199 3399344115414449174666765 := by
  unfold tailWord_6620199
  simp only [CollatzResearch.WordTrace]
  refine ⟨241458494143157137819463651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160972329428771425212975767 241458494143157137819463651)
  ·
    refine ⟨362187741214735706729195477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241458494143157137819463651 362187741214735706729195477)
    ·
      refine ⟨8488775184720368126465519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 362187741214735706729195477 8488775184720368126465519)
      ·
        refine ⟨12733162777080552189698279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8488775184720368126465519 12733162777080552189698279)
        ·
          refine ⟨19099744165620828284547419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12733162777080552189698279 19099744165620828284547419)
          ·
            refine ⟨28649616248431242426821129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19099744165620828284547419 28649616248431242426821129)
            ·
              refine ⟨21487212186323431820115847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28649616248431242426821129 21487212186323431820115847)
              ·
                refine ⟨32230818279485147730173771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21487212186323431820115847 32230818279485147730173771)
                ·
                  refine ⟨48346227419227721595260657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32230818279485147730173771 48346227419227721595260657)
                  ·
                    refine ⟨36259670564420791196445493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48346227419227721595260657 36259670564420791196445493)
                    ·
                      refine ⟨3399344115414449174666765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36259670564420791196445493 3399344115414449174666765)
                      ·
                        rfl

theorem cell23_6620199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6620199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620199 prefixEnd_6620199 := by exact prefixLift 6620199
  have htrace : WordTrace (prefixWord ++ tailWord_6620199) baseStart_6620199 baseEnd_6620199 := by
    simpa [prefixWord, tailWord_6620199, baseEnd_6620199] using wordTrace_append hprefix tailTrace_6620199
  have hstable : (prefixWord ++ tailWord_6620199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620199).length < 2 ^ (prefixWord ++ tailWord_6620199).sum := by decide
  have hdescent : baseEnd_6620199 < baseStart_6620199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620209 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 2, 4, 2]
def baseStart_6620209 : Nat := 118140960795 + 6620209 * 2 ^ 59
def prefixEnd_6620209 : Nat := 4983230072969 + 3 ^ 40 * 6620209 * 2
def baseEnd_6620209 : Nat := 3399349250220994135541719

theorem tailTrace_6620209 : CollatzResearch.WordTrace tailWord_6620209 prefixEnd_6620209 3399349250220994135541719 := by
  unfold tailWord_6620209
  simp only [CollatzResearch.WordTrace]
  refine ⟨241458858873120909527327681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160972572582080606351551787 241458858873120909527327681)
  ·
    refine ⟨181094144154840682145495761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241458858873120909527327681 181094144154840682145495761)
    ·
      refine ⟨135820608116130511609121821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181094144154840682145495761 135820608116130511609121821)
      ·
        refine ⟨50932728043548941853420683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135820608116130511609121821 50932728043548941853420683)
        ·
          refine ⟨76399092065323412780131025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50932728043548941853420683 76399092065323412780131025)
          ·
            refine ⟨57299319048992559585098269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76399092065323412780131025 57299319048992559585098269)
            ·
              refine ⟨21487244643372209844411851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57299319048992559585098269 21487244643372209844411851)
              ·
                refine ⟨32230866965058314766617777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21487244643372209844411851 32230866965058314766617777)
                ·
                  refine ⟨24173150223793736074963333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32230866965058314766617777 24173150223793736074963333)
                  ·
                    refine ⟨4532465666961325514055625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24173150223793736074963333 4532465666961325514055625)
                    ·
                      refine ⟨3399349250220994135541719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4532465666961325514055625 3399349250220994135541719)
                      ·
                        rfl

theorem cell23_6620209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_6620209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620209 prefixEnd_6620209 := by exact prefixLift 6620209
  have htrace : WordTrace (prefixWord ++ tailWord_6620209) baseStart_6620209 baseEnd_6620209 := by
    simpa [prefixWord, tailWord_6620209, baseEnd_6620209] using wordTrace_append hprefix tailTrace_6620209
  have hstable : (prefixWord ++ tailWord_6620209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620209).length < 2 ^ (prefixWord ++ tailWord_6620209).sum := by decide
  have hdescent : baseEnd_6620209 < baseStart_6620209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620215 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 10]
def baseStart_6620215 : Nat := 118140960795 + 6620215 * 2 ^ 59
def prefixEnd_6620215 : Nat := 4983230072969 + 3 ^ 40 * 6620215 * 2
def baseEnd_6620215 : Nat := 377705814567213456896299

theorem tailTrace_6620215 : CollatzResearch.WordTrace tailWord_6620215 prefixEnd_6620215 377705814567213456896299 := by
  unfold tailWord_6620215
  simp only [CollatzResearch.WordTrace]
  refine ⟨241459077711099172552046099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160972718474066115034697399 241459077711099172552046099)
  ·
    refine ⟨362188616566648758828069149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241459077711099172552046099 362188616566648758828069149)
    ·
      refine ⟨135820731212493284560525931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362188616566648758828069149 135820731212493284560525931)
      ·
        refine ⟨203731096818739926840788897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135820731212493284560525931 203731096818739926840788897)
        ·
          refine ⟨152798322614054945130591673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203731096818739926840788897 152798322614054945130591673)
          ·
            refine ⟨114598741960541208847943755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152798322614054945130591673 114598741960541208847943755)
            ·
              refine ⟨171898112940811813271915633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114598741960541208847943755 171898112940811813271915633)
              ·
                refine ⟨128923584705608859953936725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171898112940811813271915633 128923584705608859953936725)
                ·
                  refine ⟨377705814567213456896299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 128923584705608859953936725 377705814567213456896299)
                  ·
                    rfl

theorem cell23_6620215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 10].length) (baseStart_6620215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620215 prefixEnd_6620215 := by exact prefixLift 6620215
  have htrace : WordTrace (prefixWord ++ tailWord_6620215) baseStart_6620215 baseEnd_6620215 := by
    simpa [prefixWord, tailWord_6620215, baseEnd_6620215] using wordTrace_append hprefix tailTrace_6620215
  have hstable : (prefixWord ++ tailWord_6620215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620215).length < 2 ^ (prefixWord ++ tailWord_6620215).sum := by decide
  have hdescent : baseEnd_6620215 < baseStart_6620215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620229 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_6620229 : Nat := 118140960795 + 6620229 * 2 ^ 59
def prefixEnd_6620229 : Nat := 4983230072969 + 3 ^ 40 * 6620229 * 2
def baseEnd_6620229 : Nat := 3399359519834084057291627

theorem tailTrace_6620229 : CollatzResearch.WordTrace tailWord_6620229 prefixEnd_6620229 3399359519834084057291627 := by
  unfold tailWord_6620229
  simp only [CollatzResearch.WordTrace]
  refine ⟨241459588333048452943055741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160973058888698968628703827 241459588333048452943055741)
  ·
    refine ⟨90547345624893169853645903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241459588333048452943055741 90547345624893169853645903)
    ·
      refine ⟨135821018437339754780468855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90547345624893169853645903 135821018437339754780468855)
      ·
        refine ⟨203731527656009632170703283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135821018437339754780468855 203731527656009632170703283)
        ·
          refine ⟨305597291484014448256054925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203731527656009632170703283 305597291484014448256054925)
          ·
            refine ⟨114598984306505418096020597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305597291484014448256054925 114598984306505418096020597)
            ·
              refine ⟨10743654778734882946501931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114598984306505418096020597 10743654778734882946501931)
              ·
                refine ⟨16115482168102324419752897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10743654778734882946501931 16115482168102324419752897)
                ·
                  refine ⟨12086611626076743314814673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16115482168102324419752897 12086611626076743314814673)
                  ·
                    refine ⟨9064958719557557486111005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12086611626076743314814673 9064958719557557486111005)
                    ·
                      refine ⟨3399359519834084057291627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9064958719557557486111005 3399359519834084057291627)
                      ·
                        rfl

theorem cell23_6620229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_6620229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620229 prefixEnd_6620229 := by exact prefixLift 6620229
  have htrace : WordTrace (prefixWord ++ tailWord_6620229) baseStart_6620229 baseEnd_6620229 := by
    simpa [prefixWord, tailWord_6620229, baseEnd_6620229] using wordTrace_append hprefix tailTrace_6620229
  have hstable : (prefixWord ++ tailWord_6620229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620229).length < 2 ^ (prefixWord ++ tailWord_6620229).sum := by decide
  have hdescent : baseEnd_6620229 < baseStart_6620229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620235 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 8]
def baseStart_6620235 : Nat := 118140960795 + 6620235 * 2 ^ 59
def prefixEnd_6620235 : Nat := 4983230072969 + 3 ^ 40 * 6620235 * 2
def baseEnd_6620235 : Nat := 3399362600718011033816599

theorem tailTrace_6620235 : CollatzResearch.WordTrace tailWord_6620235 prefixEnd_6620235 3399362600718011033816599 := by
  unfold tailWord_6620235
  simp only [CollatzResearch.WordTrace]
  refine ⟨241459807171026715967774159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160973204780684477311849439 241459807171026715967774159)
  ·
    refine ⟨362189710756540073951661239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241459807171026715967774159 362189710756540073951661239)
    ·
      refine ⟨543284566134810110927491859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362189710756540073951661239 543284566134810110927491859)
      ·
        refine ⟨814926849202215166391237789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543284566134810110927491859 814926849202215166391237789)
        ·
          refine ⟨305597568450830687396714171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814926849202215166391237789 305597568450830687396714171)
          ·
            refine ⟨458396352676246031095071257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305597568450830687396714171 458396352676246031095071257)
            ·
              refine ⟨343797264507184523321303443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458396352676246031095071257 343797264507184523321303443)
              ·
                refine ⟨515695896760776784981955165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343797264507184523321303443 515695896760776784981955165)
                ·
                  refine ⟨193385961285291294368233187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515695896760776784981955165 193385961285291294368233187)
                  ·
                    refine ⟨290078941927936941552349781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193385961285291294368233187 290078941927936941552349781)
                    ·
                      refine ⟨3399362600718011033816599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 290078941927936941552349781 3399362600718011033816599)
                      ·
                        rfl

theorem cell23_6620235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_6620235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620235 prefixEnd_6620235 := by exact prefixLift 6620235
  have htrace : WordTrace (prefixWord ++ tailWord_6620235) baseStart_6620235 baseEnd_6620235 := by
    simpa [prefixWord, tailWord_6620235, baseEnd_6620235] using wordTrace_append hprefix tailTrace_6620235
  have hstable : (prefixWord ++ tailWord_6620235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620235).length < 2 ^ (prefixWord ++ tailWord_6620235).sum := by decide
  have hdescent : baseEnd_6620235 < baseStart_6620235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620252 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6620252 : Nat := 118140960795 + 6620252 * 2 ^ 59
def prefixEnd_6620252 : Nat := 4983230072969 + 3 ^ 40 * 6620252 * 2
def baseEnd_6620252 : Nat := 3399371329889137467304021

theorem tailTrace_6620252 : CollatzResearch.WordTrace tailWord_6620252 prefixEnd_6620252 3399371329889137467304021 := by
  unfold tailWord_6620252
  simp only [CollatzResearch.WordTrace]
  refine ⟨120730213605982563935571505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160973618141310085247428673 120730213605982563935571505)
  ·
    refine ⟨90547660204486922951678629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120730213605982563935571505 90547660204486922951678629)
    ·
      refine ⟨16977686288341298053439743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90547660204486922951678629 16977686288341298053439743)
      ·
        refine ⟨25466529432511947080159615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16977686288341298053439743 25466529432511947080159615)
        ·
          refine ⟨38199794148767920620239423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25466529432511947080159615 38199794148767920620239423)
          ·
            refine ⟨57299691223151880930359135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38199794148767920620239423 57299691223151880930359135)
            ·
              refine ⟨85949536834727821395538703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57299691223151880930359135 85949536834727821395538703)
              ·
                refine ⟨128924305252091732093308055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85949536834727821395538703 128924305252091732093308055)
                ·
                  refine ⟨193386457878137598139962083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128924305252091732093308055 193386457878137598139962083)
                  ·
                    refine ⟨290079686817206397209943125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193386457878137598139962083 290079686817206397209943125)
                    ·
                      refine ⟨3399371329889137467304021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 290079686817206397209943125 3399371329889137467304021)
                      ·
                        rfl

theorem cell23_6620252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6620252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620252 prefixEnd_6620252 := by exact prefixLift 6620252
  have htrace : WordTrace (prefixWord ++ tailWord_6620252) baseStart_6620252 baseEnd_6620252 := by
    simpa [prefixWord, tailWord_6620252, baseEnd_6620252] using wordTrace_append hprefix tailTrace_6620252
  have hstable : (prefixWord ++ tailWord_6620252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620252).length < 2 ^ (prefixWord ++ tailWord_6620252).sum := by decide
  have hdescent : baseEnd_6620252 < baseStart_6620252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620253 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6620253 : Nat := 118140960795 + 6620253 * 2 ^ 59
def prefixEnd_6620253 : Nat := 4983230072969 + 3 ^ 40 * 6620253 * 2
def baseEnd_6620253 : Nat := 1133123947789930654463839

theorem tailTrace_6620253 : CollatzResearch.WordTrace tailWord_6620253 prefixEnd_6620253 1133123947789930654463839 := by
  unfold tailWord_6620253
  simp only [CollatzResearch.WordTrace]
  refine ⟨241460463684961505041929413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160973642456641003361286275 241460463684961505041929413)
  ·
    refine ⟨45273836940930282195361765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241460463684961505041929413 45273836940930282195361765)
    ·
      refine ⟨8488844426424427911630331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45273836940930282195361765 8488844426424427911630331)
      ·
        refine ⟨12733266639636641867445497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8488844426424427911630331 12733266639636641867445497)
        ·
          refine ⟨9549949979727481400584123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12733266639636641867445497 9549949979727481400584123)
          ·
            refine ⟨14324924969591222100876185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9549949979727481400584123 14324924969591222100876185)
            ·
              refine ⟨10743693727193416575657139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14324924969591222100876185 10743693727193416575657139)
              ·
                refine ⟨16115540590790124863485709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10743693727193416575657139 16115540590790124863485709)
                ·
                  refine ⟨6043327721546296823807141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16115540590790124863485709 6043327721546296823807141)
                  ·
                    refine ⟨1133123947789930654463839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6043327721546296823807141 1133123947789930654463839)
                    ·
                      rfl

theorem cell23_6620253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6620253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620253 prefixEnd_6620253 := by exact prefixLift 6620253
  have htrace : WordTrace (prefixWord ++ tailWord_6620253) baseStart_6620253 baseEnd_6620253 := by
    simpa [prefixWord, tailWord_6620253, baseEnd_6620253] using wordTrace_append hprefix tailTrace_6620253
  have hstable : (prefixWord ++ tailWord_6620253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620253).length < 2 ^ (prefixWord ++ tailWord_6620253).sum := by decide
  have hdescent : baseEnd_6620253 < baseStart_6620253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620266 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 6]
def baseStart_6620266 : Nat := 118140960795 + 6620266 * 2 ^ 59
def prefixEnd_6620266 : Nat := 4983230072969 + 3 ^ 40 * 6620266 * 2
def baseEnd_6620266 : Nat := 377708724290922268058773

theorem tailTrace_6620266 : CollatzResearch.WordTrace tailWord_6620266 prefixEnd_6620266 377708724290922268058773 := by
  unfold tailWord_6620266
  simp only [CollatzResearch.WordTrace]
  refine ⟨60365234458478602065538163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160973958555942938841435101 60365234458478602065538163)
  ·
    refine ⟨90547851687717903098307245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60365234458478602065538163 90547851687717903098307245)
    ·
      refine ⟨33955444382894213661865217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90547851687717903098307245 33955444382894213661865217)
      ·
        refine ⟨25466583287170660246398913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33955444382894213661865217 25466583287170660246398913)
        ·
          refine ⟨19099937465377995184799185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25466583287170660246398913 19099937465377995184799185)
          ·
            refine ⟨14324953099033496388599389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19099937465377995184799185 14324953099033496388599389)
            ·
              refine ⟨5371857412137561145724771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14324953099033496388599389 5371857412137561145724771)
              ·
                refine ⟨8057786118206341718587157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371857412137561145724771 8057786118206341718587157)
                ·
                  refine ⟨377708724290922268058773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8057786118206341718587157 377708724290922268058773)
                  ·
                    rfl

theorem cell23_6620266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_6620266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620266 prefixEnd_6620266 := by exact prefixLift 6620266
  have htrace : WordTrace (prefixWord ++ tailWord_6620266) baseStart_6620266 baseEnd_6620266 := by
    simpa [prefixWord, tailWord_6620266, baseEnd_6620266] using wordTrace_append hprefix tailTrace_6620266
  have hstable : (prefixWord ++ tailWord_6620266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620266).length < 2 ^ (prefixWord ++ tailWord_6620266).sum := by decide
  have hdescent : baseEnd_6620266 < baseStart_6620266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620279 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 1, 5]
def baseStart_6620279 : Nat := 118140960795 + 6620279 * 2 ^ 59
def prefixEnd_6620279 : Nat := 4983230072969 + 3 ^ 40 * 6620279 * 2
def baseEnd_6620279 : Nat := 1133128397955602953888799

theorem tailTrace_6620279 : CollatzResearch.WordTrace tailWord_6620279 prefixEnd_6620279 1133128397955602953888799 := by
  unfold tailWord_6620279
  simp only [CollatzResearch.WordTrace]
  refine ⟨241461411982867311482375891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160974274655244874321583927 241461411982867311482375891)
  ·
    refine ⟨362192117974300967223563837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241461411982867311482375891 362192117974300967223563837)
    ·
      refine ⟨135822044240362862708836439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362192117974300967223563837 135822044240362862708836439)
      ·
        refine ⟨203733066360544294063254659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135822044240362862708836439 203733066360544294063254659)
        ·
          refine ⟨305599599540816441094881989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203733066360544294063254659 305599599540816441094881989)
          ·
            refine ⟨57299924913903082705290373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305599599540816441094881989 57299924913903082705290373)
            ·
              refine ⟨10743735921356828007241945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57299924913903082705290373 10743735921356828007241945)
              ·
                refine ⟨8057801941017621005431459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10743735921356828007241945 8057801941017621005431459)
                ·
                  refine ⟨12086702911526431508147189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8057801941017621005431459 12086702911526431508147189)
                  ·
                    refine ⟨1133128397955602953888799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12086702911526431508147189 1133128397955602953888799)
                    ·
                      rfl

theorem cell23_6620279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_6620279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620279 prefixEnd_6620279 := by exact prefixLift 6620279
  have htrace : WordTrace (prefixWord ++ tailWord_6620279) baseStart_6620279 baseEnd_6620279 := by
    simpa [prefixWord, tailWord_6620279, baseEnd_6620279] using wordTrace_append hprefix tailTrace_6620279
  have hstable : (prefixWord ++ tailWord_6620279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620279).length < 2 ^ (prefixWord ++ tailWord_6620279).sum := by decide
  have hdescent : baseEnd_6620279 < baseStart_6620279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620349 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_6620349 : Nat := 118140960795 + 6620349 * 2 ^ 59
def prefixEnd_6620349 : Nat := 4983230072969 + 3 ^ 40 * 6620349 * 2
def baseEnd_6620349 : Nat := 3399421137512623587791075

theorem tailTrace_6620349 : CollatzResearch.WordTrace tailWord_6620349 prefixEnd_6620349 3399421137512623587791075 := by
  unfold tailWord_6620349
  simp only [CollatzResearch.WordTrace]
  refine ⟨241463965092613713437424101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160975976728409142291616067 241463965092613713437424101)
  ·
    refine ⟨45274493454865071269517019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241463965092613713437424101 45274493454865071269517019)
    ·
      refine ⟨67911740182297606904275529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45274493454865071269517019 67911740182297606904275529)
      ·
        refine ⟨50933805136723205178206647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67911740182297606904275529 50933805136723205178206647)
        ·
          refine ⟨76400707705084807767309971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50933805136723205178206647 76400707705084807767309971)
          ·
            refine ⟨114601061557627211650964957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76400707705084807767309971 114601061557627211650964957)
            ·
              refine ⟨42975398084110204369111859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114601061557627211650964957 42975398084110204369111859)
              ·
                refine ⟨64463097126165306553667789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42975398084110204369111859 64463097126165306553667789)
                ·
                  refine ⟨24173661422311989957625421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64463097126165306553667789 24173661422311989957625421)
                  ·
                    refine ⟨9065123033366996234109533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24173661422311989957625421 9065123033366996234109533)
                    ·
                      refine ⟨3399421137512623587791075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9065123033366996234109533 3399421137512623587791075)
                      ·
                        rfl

theorem cell23_6620349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_6620349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620349 prefixEnd_6620349 := by exact prefixLift 6620349
  have htrace : WordTrace (prefixWord ++ tailWord_6620349) baseStart_6620349 baseEnd_6620349 := by
    simpa [prefixWord, tailWord_6620349, baseEnd_6620349] using wordTrace_append hprefix tailTrace_6620349
  have hstable : (prefixWord ++ tailWord_6620349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620349).length < 2 ^ (prefixWord ++ tailWord_6620349).sum := by decide
  have hdescent : baseEnd_6620349 < baseStart_6620349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620353 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6620353 : Nat := 118140960795 + 6620353 * 2 ^ 59
def prefixEnd_6620353 : Nat := 4983230072969 + 3 ^ 40 * 6620353 * 2
def baseEnd_6620353 : Nat := 3399423191435241572141057

theorem tailTrace_6620353 : CollatzResearch.WordTrace tailWord_6620353 prefixEnd_6620353 3399423191435241572141057 := by
  unfold tailWord_6620353
  simp only [CollatzResearch.WordTrace]
  refine ⟨241464110984599222120569713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160976073989732814747046475 241464110984599222120569713)
  ·
    refine ⟨181098083238449416590427285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241464110984599222120569713 181098083238449416590427285)
    ·
      refine ⟨8488972651802316402676279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 181098083238449416590427285 8488972651802316402676279)
      ·
        refine ⟨12733458977703474604014419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8488972651802316402676279 12733458977703474604014419)
        ·
          refine ⟨19100188466555211906021629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12733458977703474604014419 19100188466555211906021629)
          ·
            refine ⟨7162570674958204464758111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19100188466555211906021629 7162570674958204464758111)
            ·
              refine ⟨10743856012437306697137167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7162570674958204464758111 10743856012437306697137167)
              ·
                refine ⟨16115784018655960045705751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10743856012437306697137167 16115784018655960045705751)
                ·
                  refine ⟨24173676027983940068558627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16115784018655960045705751 24173676027983940068558627)
                  ·
                    refine ⟨36260514041975910102837941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24173676027983940068558627 36260514041975910102837941)
                    ·
                      refine ⟨3399423191435241572141057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36260514041975910102837941 3399423191435241572141057)
                      ·
                        rfl

theorem cell23_6620353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6620353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620353 prefixEnd_6620353 := by exact prefixLift 6620353
  have htrace : WordTrace (prefixWord ++ tailWord_6620353) baseStart_6620353 baseEnd_6620353 := by
    simpa [prefixWord, tailWord_6620353, baseEnd_6620353] using wordTrace_append hprefix tailTrace_6620353
  have hstable : (prefixWord ++ tailWord_6620353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620353).length < 2 ^ (prefixWord ++ tailWord_6620353).sum := by decide
  have hdescent : baseEnd_6620353 < baseStart_6620353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620419 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 4]
def baseStart_6620419 : Nat := 118140960795 + 6620419 * 2 ^ 59
def prefixEnd_6620419 : Nat := 4983230072969 + 3 ^ 40 * 6620419 * 2
def baseEnd_6620419 : Nat := 3399457081158438313915753

theorem tailTrace_6620419 : CollatzResearch.WordTrace tailWord_6620419 prefixEnd_6620419 3399457081158438313915753 := by
  unfold tailWord_6620419
  simp only [CollatzResearch.WordTrace]
  refine ⟨241466518202360115392472311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160977678801573410261648207 241466518202360115392472311)
  ·
    refine ⟨362199777303540173088708467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241466518202360115392472311 362199777303540173088708467)
    ·
      refine ⟨543299665955310259633062701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362199777303540173088708467 543299665955310259633062701)
      ·
        refine ⟨203737374733241347362398513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 543299665955310259633062701 203737374733241347362398513)
        ·
          refine ⟨152803031049931010521798885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203737374733241347362398513 152803031049931010521798885)
          ·
            refine ⟨28650568321862064472837291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152803031049931010521798885 28650568321862064472837291)
            ·
              refine ⟨42975852482793096709255937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28650568321862064472837291 42975852482793096709255937)
              ·
                refine ⟨32231889362094822531941953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42975852482793096709255937 32231889362094822531941953)
                ·
                  refine ⟨24173917021571116898956465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32231889362094822531941953 24173917021571116898956465)
                  ·
                    refine ⟨18130437766178337674217349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24173917021571116898956465 18130437766178337674217349)
                    ·
                      refine ⟨3399457081158438313915753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18130437766178337674217349 3399457081158438313915753)
                      ·
                        rfl

theorem cell23_6620419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_6620419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620419 prefixEnd_6620419 := by exact prefixLift 6620419
  have htrace : WordTrace (prefixWord ++ tailWord_6620419) baseStart_6620419 baseEnd_6620419 := by
    simpa [prefixWord, tailWord_6620419, baseEnd_6620419] using wordTrace_append hprefix tailTrace_6620419
  have hstable : (prefixWord ++ tailWord_6620419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620419).length < 2 ^ (prefixWord ++ tailWord_6620419).sum := by decide
  have hdescent : baseEnd_6620419 < baseStart_6620419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620434 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6620434 : Nat := 118140960795 + 6620434 * 2 ^ 59
def prefixEnd_6620434 : Nat := 4983230072969 + 3 ^ 40 * 6620434 * 2
def baseEnd_6620434 : Nat := 3399464783368255755228185

theorem tailTrace_6620434 : CollatzResearch.WordTrace tailWord_6620434 prefixEnd_6620434 3399464783368255755228185 := by
  unfold tailWord_6620434
  simp only [CollatzResearch.WordTrace]
  refine ⟨60366766324326443238567089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160978043531537181969512237 60366766324326443238567089)
  ·
    refine ⟨45275074743244832428925317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60366766324326443238567089 45275074743244832428925317)
    ·
      refine ⟨8489076514358406080423497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45275074743244832428925317 8489076514358406080423497)
      ·
        refine ⟨6366807385768804560317623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8489076514358406080423497 6366807385768804560317623)
        ·
          refine ⟨9550211078653206840476435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6366807385768804560317623 9550211078653206840476435)
          ·
            refine ⟨14325316617979810260714653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9550211078653206840476435 14325316617979810260714653)
            ·
              refine ⟨5371993731742428847767995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14325316617979810260714653 5371993731742428847767995)
              ·
                refine ⟨8057990597613643271651993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371993731742428847767995 8057990597613643271651993)
                ·
                  refine ⟨6043492948210232453738995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8057990597613643271651993 6043492948210232453738995)
                  ·
                    refine ⟨9065239422315348680608493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6043492948210232453738995 9065239422315348680608493)
                    ·
                      refine ⟨3399464783368255755228185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9065239422315348680608493 3399464783368255755228185)
                      ·
                        rfl

theorem cell23_6620434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6620434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620434 prefixEnd_6620434 := by exact prefixLift 6620434
  have htrace : WordTrace (prefixWord ++ tailWord_6620434) baseStart_6620434 baseEnd_6620434 := by
    simpa [prefixWord, tailWord_6620434, baseEnd_6620434] using wordTrace_append hprefix tailTrace_6620434
  have hstable : (prefixWord ++ tailWord_6620434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620434).length < 2 ^ (prefixWord ++ tailWord_6620434).sum := by decide
  have hdescent : baseEnd_6620434 < baseStart_6620434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620476 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_6620476 : Nat := 118140960795 + 6620476 * 2 ^ 59
def prefixEnd_6620476 : Nat := 4983230072969 + 3 ^ 40 * 6620476 * 2
def baseEnd_6620476 : Nat := 1133162116518581530300997

theorem tailTrace_6620476 : CollatzResearch.WordTrace tailWord_6620476 prefixEnd_6620476 1133162116518581530300997 := by
  unfold tailWord_6620476
  simp only [CollatzResearch.WordTrace]
  refine ⟨120734298581576807063648641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160979064775435742751531521 120734298581576807063648641)
  ·
    refine ⟨90550723936182605297736481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120734298581576807063648641 90550723936182605297736481)
    ·
      refine ⟨67913042952136953973302361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90550723936182605297736481 67913042952136953973302361)
      ·
        refine ⟨50934782214102715479976771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67913042952136953973302361 50934782214102715479976771)
        ·
          refine ⟨76402173321154073219965157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50934782214102715479976771 76402173321154073219965157)
          ·
            refine ⟨14325407497716388728743467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76402173321154073219965157 14325407497716388728743467)
            ·
              refine ⟨21488111246574583093115201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14325407497716388728743467 21488111246574583093115201)
              ·
                refine ⟨16116083434930937319836401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21488111246574583093115201 16116083434930937319836401)
                ·
                  refine ⟨12087062576198202989877301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16116083434930937319836401 12087062576198202989877301)
                  ·
                    refine ⟨1133162116518581530300997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12087062576198202989877301 1133162116518581530300997)
                    ·
                      rfl

theorem cell23_6620476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_6620476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620476 prefixEnd_6620476 := by exact prefixLift 6620476
  have htrace : WordTrace (prefixWord ++ tailWord_6620476) baseStart_6620476 baseEnd_6620476 := by
    simpa [prefixWord, tailWord_6620476, baseEnd_6620476] using wordTrace_append hprefix tailTrace_6620476
  have hstable : (prefixWord ++ tailWord_6620476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620476).length < 2 ^ (prefixWord ++ tailWord_6620476).sum := by decide
  have hdescent : baseEnd_6620476 < baseStart_6620476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620496 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 1, 6, 2]
def baseStart_6620496 : Nat := 118140960795 + 6620496 * 2 ^ 59
def prefixEnd_6620496 : Nat := 4983230072969 + 3 ^ 40 * 6620496 * 2
def baseEnd_6620496 : Nat := 3399496619168834512652899

theorem tailTrace_6620496 : CollatzResearch.WordTrace tailWord_6620496 prefixEnd_6620496 3399496619168834512652899 := by
  unfold tailWord_6620496
  simp only [CollatzResearch.WordTrace]
  refine ⟨120734663311540578771512671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160979551082054105028683561 120734663311540578771512671)
  ·
    refine ⟨181101994967310868157269007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120734663311540578771512671 181101994967310868157269007)
    ·
      refine ⟨271652992450966302235903511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181101994967310868157269007 271652992450966302235903511)
      ·
        refine ⟨407479488676449453353855267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271652992450966302235903511 407479488676449453353855267)
        ·
          refine ⟨611219233014674180030782901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407479488676449453353855267 611219233014674180030782901)
          ·
            refine ⟨57301803095125704377885897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 611219233014674180030782901 57301803095125704377885897)
            ·
              refine ⟨42976352321344278283414423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57301803095125704377885897 42976352321344278283414423)
              ·
                refine ⟨64464528482016417425121635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42976352321344278283414423 64464528482016417425121635)
                ·
                  refine ⟨96696792723024626137682453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64464528482016417425121635 96696792723024626137682453)
                  ·
                    refine ⟨4532662158891779350203865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96696792723024626137682453 4532662158891779350203865)
                    ·
                      refine ⟨3399496619168834512652899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4532662158891779350203865 3399496619168834512652899)
                      ·
                        rfl

theorem cell23_6620496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 6, 2].length) (baseStart_6620496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620496 prefixEnd_6620496 := by exact prefixLift 6620496
  have htrace : WordTrace (prefixWord ++ tailWord_6620496) baseStart_6620496 baseEnd_6620496 := by
    simpa [prefixWord, tailWord_6620496, baseEnd_6620496] using wordTrace_append hprefix tailTrace_6620496
  have hstable : (prefixWord ++ tailWord_6620496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620496).length < 2 ^ (prefixWord ++ tailWord_6620496).sum := by decide
  have hdescent : baseEnd_6620496 < baseStart_6620496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620506 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_6620506 : Nat := 118140960795 + 6620506 * 2 ^ 59
def prefixEnd_6620506 : Nat := 4983230072969 + 3 ^ 40 * 6620506 * 2
def baseEnd_6620506 : Nat := 1133167251325126491175951

theorem tailTrace_6620506 : CollatzResearch.WordTrace tailWord_6620506 prefixEnd_6620506 1133167251325126491175951 := by
  unfold tailWord_6620506
  simp only [CollatzResearch.WordTrace]
  refine ⟨60367422838261232312722343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160979794235363286167259581 60367422838261232312722343)
  ·
    refine ⟨90551134257391848469083515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60367422838261232312722343 90551134257391848469083515)
    ·
      refine ⟨135826701386087772703625273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90551134257391848469083515 135826701386087772703625273)
      ·
        refine ⟨101870026039565829527718955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135826701386087772703625273 101870026039565829527718955)
        ·
          refine ⟨152805039059348744291578433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101870026039565829527718955 152805039059348744291578433)
          ·
            refine ⟨114603779294511558218683825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152805039059348744291578433 114603779294511558218683825)
            ·
              refine ⟨85952834470883668664012869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114603779294511558218683825 85952834470883668664012869)
              ·
                refine ⟨16116156463290687874502413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85952834470883668664012869 16116156463290687874502413)
                ·
                  refine ⟨6043558673734007952938405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16116156463290687874502413 6043558673734007952938405)
                  ·
                    refine ⟨1133167251325126491175951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6043558673734007952938405 1133167251325126491175951)
                    ·
                      rfl

theorem cell23_6620506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_6620506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620506 prefixEnd_6620506 := by exact prefixLift 6620506
  have htrace : WordTrace (prefixWord ++ tailWord_6620506) baseStart_6620506 baseEnd_6620506 := by
    simpa [prefixWord, tailWord_6620506, baseEnd_6620506] using wordTrace_append hprefix tailTrace_6620506
  have hstable : (prefixWord ++ tailWord_6620506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620506).length < 2 ^ (prefixWord ++ tailWord_6620506).sum := by decide
  have hdescent : baseEnd_6620506 < baseStart_6620506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620539 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 6]
def baseStart_6620539 : Nat := 118140960795 + 6620539 * 2 ^ 59
def prefixEnd_6620539 : Nat := 4983230072969 + 3 ^ 40 * 6620539 * 2
def baseEnd_6620539 : Nat := 3399518698836977844415201

theorem tailTrace_6620539 : CollatzResearch.WordTrace tailWord_6620539 prefixEnd_6620539 3399518698836977844415201 := by
  unfold tailWord_6620539
  simp only [CollatzResearch.WordTrace]
  refine ⟨241470894961925375886840671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160980596641283583924560447 241470894961925375886840671)
  ·
    refine ⟨362206342442888063830261007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241470894961925375886840671 362206342442888063830261007)
    ·
      refine ⟨543309513664332095745391511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362206342442888063830261007 543309513664332095745391511)
      ·
        refine ⟨814964270496498143618087267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543309513664332095745391511 814964270496498143618087267)
        ·
          refine ⟨1222446405744747215427130901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814964270496498143618087267 1222446405744747215427130901)
          ·
            refine ⟨57302175269285025723146761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1222446405744747215427130901 57302175269285025723146761)
            ·
              refine ⟨42976631451963769292360071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57302175269285025723146761 42976631451963769292360071)
              ·
                refine ⟨64464947177945653938540107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42976631451963769292360071 64464947177945653938540107)
                ·
                  refine ⟨96697420766918480907810161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64464947177945653938540107 96697420766918480907810161)
                  ·
                    refine ⟨72523065575188860680857621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96697420766918480907810161 72523065575188860680857621)
                    ·
                      refine ⟨3399518698836977844415201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72523065575188860680857621 3399518698836977844415201)
                      ·
                        rfl

theorem cell23_6620539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_6620539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620539 prefixEnd_6620539 := by exact prefixLift 6620539
  have htrace : WordTrace (prefixWord ++ tailWord_6620539) baseStart_6620539 baseEnd_6620539 := by
    simpa [prefixWord, tailWord_6620539, baseEnd_6620539] using wordTrace_append hprefix tailTrace_6620539
  have hstable : (prefixWord ++ tailWord_6620539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620539).length < 2 ^ (prefixWord ++ tailWord_6620539).sum := by decide
  have hdescent : baseEnd_6620539 < baseStart_6620539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620574 : List Nat := [4, 3, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_6620574 : Nat := 118140960795 + 6620574 * 2 ^ 59
def prefixEnd_6620574 : Nat := 4983230072969 + 3 ^ 40 * 6620574 * 2
def baseEnd_6620574 : Nat := 1133178890219961735825847

theorem tailTrace_6620574 : CollatzResearch.WordTrace tailWord_6620574 prefixEnd_6620574 1133178890219961735825847 := by
  unfold tailWord_6620574
  simp only [CollatzResearch.WordTrace]
  refine ⟨30184021439599822108045597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160981447677865717909576517 30184021439599822108045597)
  ·
    refine ⟨11319008039849933290517099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30184021439599822108045597 11319008039849933290517099)
    ·
      refine ⟨16978512059774899935775649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319008039849933290517099 16978512059774899935775649)
      ·
        refine ⟨12733884044831174951831737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16978512059774899935775649 12733884044831174951831737)
        ·
          refine ⟨9550413033623381213873803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12733884044831174951831737 9550413033623381213873803)
          ·
            refine ⟨14325619550435071820810705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9550413033623381213873803 14325619550435071820810705)
            ·
              refine ⟨10744214662826303865608029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14325619550435071820810705 10744214662826303865608029)
              ·
                refine ⟨4029080498559863949603011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10744214662826303865608029 4029080498559863949603011)
                ·
                  refine ⟨6043620747839795924404517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029080498559863949603011 6043620747839795924404517)
                  ·
                    refine ⟨1133178890219961735825847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6043620747839795924404517 1133178890219961735825847)
                    ·
                      rfl

theorem cell23_6620574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_6620574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620574 prefixEnd_6620574 := by exact prefixLift 6620574
  have htrace : WordTrace (prefixWord ++ tailWord_6620574) baseStart_6620574 baseEnd_6620574 := by
    simpa [prefixWord, tailWord_6620574, baseEnd_6620574] using wordTrace_append hprefix tailTrace_6620574
  have hstable : (prefixWord ++ tailWord_6620574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620574).length < 2 ^ (prefixWord ++ tailWord_6620574).sum := by decide
  have hdescent : baseEnd_6620574 < baseStart_6620574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620583 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 1, 5]
def baseStart_6620583 : Nat := 118140960795 + 6620583 * 2 ^ 59
def prefixEnd_6620583 : Nat := 4983230072969 + 3 ^ 40 * 6620583 * 2
def baseEnd_6620583 : Nat := 1133180430661925224088333

theorem tailTrace_6620583 : CollatzResearch.WordTrace tailWord_6620583 prefixEnd_6620583 1133180430661925224088333 := by
  unfold tailWord_6620583
  simp only [CollatzResearch.WordTrace]
  refine ⟨241472499773765971401442403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160981666515843980934294935 241472499773765971401442403)
  ·
    refine ⟨362208749660648957102163605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241472499773765971401442403 362208749660648957102163605)
    ·
      refine ⟨16978535140342919864163919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 362208749660648957102163605 16978535140342919864163919)
      ·
        refine ⟨25467802710514379796245879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16978535140342919864163919 25467802710514379796245879)
        ·
          refine ⟨38201704065771569694368819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25467802710514379796245879 38201704065771569694368819)
          ·
            refine ⟨57302556098657354541553229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38201704065771569694368819 57302556098657354541553229)
            ·
              refine ⟨21488458536996507953082461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57302556098657354541553229 21488458536996507953082461)
              ·
                refine ⟨8058171951373690482405923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21488458536996507953082461 8058171951373690482405923)
                ·
                  refine ⟨12087257927060535723608885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058171951373690482405923 12087257927060535723608885)
                  ·
                    refine ⟨1133180430661925224088333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12087257927060535723608885 1133180430661925224088333)
                    ·
                      rfl

theorem cell23_6620583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_6620583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620583 prefixEnd_6620583 := by exact prefixLift 6620583
  have htrace : WordTrace (prefixWord ++ tailWord_6620583) baseStart_6620583 baseEnd_6620583 := by
    simpa [prefixWord, tailWord_6620583, baseEnd_6620583] using wordTrace_append hprefix tailTrace_6620583
  have hstable : (prefixWord ++ tailWord_6620583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620583).length < 2 ^ (prefixWord ++ tailWord_6620583).sum := by decide
  have hdescent : baseEnd_6620583 < baseStart_6620583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620597 : List Nat := [1, 3, 3, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_6620597 : Nat := 118140960795 + 6620597 * 2 ^ 59
def prefixEnd_6620597 : Nat := 4983230072969 + 3 ^ 40 * 6620597 * 2
def baseEnd_6620597 : Nat := 3399548480714938617489935

theorem tailTrace_6620597 : CollatzResearch.WordTrace tailWord_6620597 prefixEnd_6620597 3399548480714938617489935 := by
  unfold tailWord_6620597
  simp only [CollatzResearch.WordTrace]
  refine ⟨241473010395715251792452045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160982006930476834528301363 241473010395715251792452045)
  ·
    refine ⟨90552378898393219422169517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241473010395715251792452045 90552378898393219422169517)
    ·
      refine ⟨33957142086897457283313569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90552378898393219422169517 33957142086897457283313569)
      ·
        refine ⟨25467856565173092962485177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33957142086897457283313569 25467856565173092962485177)
        ·
          refine ⟨19100892423879819721863883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25467856565173092962485177 19100892423879819721863883)
          ·
            refine ⟨28651338635819729582795825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19100892423879819721863883 28651338635819729582795825)
            ·
              refine ⟨21488503976864797187096869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28651338635819729582795825 21488503976864797187096869)
              ·
                refine ⟨4029094495662149472580663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21488503976864797187096869 4029094495662149472580663)
                ·
                  refine ⟨6043641743493224208870995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029094495662149472580663 6043641743493224208870995)
                  ·
                    refine ⟨9065462615239836313306493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6043641743493224208870995 9065462615239836313306493)
                    ·
                      refine ⟨3399548480714938617489935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9065462615239836313306493 3399548480714938617489935)
                      ·
                        rfl

theorem cell23_6620597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_6620597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620597 prefixEnd_6620597 := by exact prefixLift 6620597
  have htrace : WordTrace (prefixWord ++ tailWord_6620597) baseStart_6620597 baseEnd_6620597 := by
    simpa [prefixWord, tailWord_6620597, baseEnd_6620597] using wordTrace_append hprefix tailTrace_6620597
  have hstable : (prefixWord ++ tailWord_6620597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620597).length < 2 ^ (prefixWord ++ tailWord_6620597).sum := by decide
  have hdescent : baseEnd_6620597 < baseStart_6620597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620616 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_6620616 : Nat := 118140960795 + 6620616 * 2 ^ 59
def prefixEnd_6620616 : Nat := 4983230072969 + 3 ^ 40 * 6620616 * 2
def baseEnd_6620616 : Nat := 3399558236847374043152347

theorem tailTrace_6620616 : CollatzResearch.WordTrace tailWord_6620616 prefixEnd_6620616 3399558236847374043152347 := by
  unfold tailWord_6620616
  simp only [CollatzResearch.WordTrace]
  refine ⟨120736851691323209018696851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160982468921764278691595801 120736851691323209018696851)
  ·
    refine ⟨181105277536984813528045277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120736851691323209018696851 181105277536984813528045277)
    ·
      refine ⟨67914479076369305073016979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181105277536984813528045277 67914479076369305073016979)
      ·
        refine ⟨101871718614553957609525469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67914479076369305073016979 101871718614553957609525469)
        ·
          refine ⟨38201894480457734103572051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101871718614553957609525469 38201894480457734103572051)
          ·
            refine ⟨57302841720686601155358077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38201894480457734103572051 57302841720686601155358077)
            ·
              refine ⟨21488565645257475433259279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57302841720686601155358077 21488565645257475433259279)
              ·
                refine ⟨32232848467886213149888919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21488565645257475433259279 32232848467886213149888919)
                ·
                  refine ⟨48349272701829319724833379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32232848467886213149888919 48349272701829319724833379)
                  ·
                    refine ⟨72523909052743979587250069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48349272701829319724833379 72523909052743979587250069)
                    ·
                      refine ⟨3399558236847374043152347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72523909052743979587250069 3399558236847374043152347)
                      ·
                        rfl

theorem cell23_6620616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_6620616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620616 prefixEnd_6620616 := by exact prefixLift 6620616
  have htrace : WordTrace (prefixWord ++ tailWord_6620616) baseStart_6620616 baseEnd_6620616 := by
    simpa [prefixWord, tailWord_6620616, baseEnd_6620616] using wordTrace_append hprefix tailTrace_6620616
  have hstable : (prefixWord ++ tailWord_6620616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620616).length < 2 ^ (prefixWord ++ tailWord_6620616).sum := by decide
  have hdescent : baseEnd_6620616 < baseStart_6620616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620620 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_6620620 : Nat := 118140960795 + 6620620 * 2 ^ 59
def prefixEnd_6620620 : Nat := 4983230072969 + 3 ^ 40 * 6620620 * 2
def baseEnd_6620620 : Nat := 3399560290769992027502329

theorem tailTrace_6620620 : CollatzResearch.WordTrace tailWord_6620620 prefixEnd_6620620 3399560290769992027502329 := by
  unfold tailWord_6620620
  simp only [CollatzResearch.WordTrace]
  refine ⟨120736924637315963360269657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160982566183087951147026209 120736924637315963360269657)
  ·
    refine ⟨90552693477986972520202243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120736924637315963360269657 90552693477986972520202243)
    ·
      refine ⟨135829040216980458780303365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90552693477986972520202243 135829040216980458780303365)
      ·
        refine ⟨25467945040683836021306881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135829040216980458780303365 25467945040683836021306881)
        ·
          refine ⟨19100958780512877015980161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25467945040683836021306881 19100958780512877015980161)
          ·
            refine ⟨14325719085384657761985121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19100958780512877015980161 14325719085384657761985121)
            ·
              refine ⟨10744289314038493321488841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14325719085384657761985121 10744289314038493321488841)
              ·
                refine ⟨8058216985528869991116631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10744289314038493321488841 8058216985528869991116631)
                ·
                  refine ⟨12087325478293304986674947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058216985528869991116631 12087325478293304986674947)
                  ·
                    refine ⟨18130988217439957480012421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12087325478293304986674947 18130988217439957480012421)
                    ·
                      refine ⟨3399560290769992027502329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18130988217439957480012421 3399560290769992027502329)
                      ·
                        rfl

theorem cell23_6620620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_6620620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620620 prefixEnd_6620620 := by exact prefixLift 6620620
  have htrace : WordTrace (prefixWord ++ tailWord_6620620) baseStart_6620620 baseEnd_6620620 := by
    simpa [prefixWord, tailWord_6620620, baseEnd_6620620] using wordTrace_append hprefix tailTrace_6620620
  have hstable : (prefixWord ++ tailWord_6620620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620620).length < 2 ^ (prefixWord ++ tailWord_6620620).sum := by decide
  have hdescent : baseEnd_6620620 < baseStart_6620620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620623 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 3]
def baseStart_6620623 : Nat := 118140960795 + 6620623 * 2 ^ 59
def prefixEnd_6620623 : Nat := 4983230072969 + 3 ^ 40 * 6620623 * 2
def baseEnd_6620623 : Nat := 3399561831211955515764815

theorem tailTrace_6620623 : CollatzResearch.WordTrace tailWord_6620623 prefixEnd_6620623 3399561831211955515764815 := by
  unfold tailWord_6620623
  simp only [CollatzResearch.WordTrace]
  refine ⟨241473958693621058232898523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160982639129080705488599015 241473958693621058232898523)
  ·
    refine ⟨362210938040431587349347785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241473958693621058232898523 362210938040431587349347785)
    ·
      refine ⟨271658203530323690512010839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362210938040431587349347785 271658203530323690512010839)
      ·
        refine ⟨407487305295485535768016259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271658203530323690512010839 407487305295485535768016259)
        ·
          refine ⟨611230957943228303652024389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407487305295485535768016259 611230957943228303652024389)
          ·
            refine ⟨114605804614355306934754573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 611230957943228303652024389 114605804614355306934754573)
            ·
              refine ⟨42977176730383240100532965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114605804614355306934754573 42977176730383240100532965)
              ·
                refine ⟨8058220636946857518849931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42977176730383240100532965 8058220636946857518849931)
                ·
                  refine ⟨12087330955420286278274897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058220636946857518849931 12087330955420286278274897)
                  ·
                    refine ⟨9065498216565214708706173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12087330955420286278274897 9065498216565214708706173)
                    ·
                      refine ⟨3399561831211955515764815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9065498216565214708706173 3399561831211955515764815)
                      ·
                        rfl

theorem cell23_6620623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 3].length) (baseStart_6620623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620623 prefixEnd_6620623 := by exact prefixLift 6620623
  have htrace : WordTrace (prefixWord ++ tailWord_6620623) baseStart_6620623 baseEnd_6620623 := by
    simpa [prefixWord, tailWord_6620623, baseEnd_6620623] using wordTrace_append hprefix tailTrace_6620623
  have hstable : (prefixWord ++ tailWord_6620623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620623).length < 2 ^ (prefixWord ++ tailWord_6620623).sum := by decide
  have hdescent : baseEnd_6620623 < baseStart_6620623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620630 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_6620630 : Nat := 118140960795 + 6620630 * 2 ^ 59
def prefixEnd_6620630 : Nat := 4983230072969 + 3 ^ 40 * 6620630 * 2
def baseEnd_6620630 : Nat := 1133188475192178996125761

theorem tailTrace_6620630 : CollatzResearch.WordTrace tailWord_6620630 prefixEnd_6620630 1133188475192178996125761 := by
  unfold tailWord_6620630
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092138375287231151775209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160982809336397132285602229 15092138375287231151775209)
  ·
    refine ⟨11319103781465423363831407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15092138375287231151775209 11319103781465423363831407)
    ·
      refine ⟨16978655672198135045747111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319103781465423363831407 16978655672198135045747111)
      ·
        refine ⟨25467983508297202568620667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16978655672198135045747111 25467983508297202568620667)
        ·
          refine ⟨38201975262445803852931001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25467983508297202568620667 38201975262445803852931001)
          ·
            refine ⟨28651481446834352889698251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38201975262445803852931001 28651481446834352889698251)
            ·
              refine ⟨42977222170251529334547377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28651481446834352889698251 42977222170251529334547377)
              ·
                refine ⟨32232916627688647000910533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42977222170251529334547377 32232916627688647000910533)
                ·
                  refine ⟨6043671867691621312670725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32232916627688647000910533 6043671867691621312670725)
                  ·
                    refine ⟨1133188475192178996125761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6043671867691621312670725 1133188475192178996125761)
                    ·
                      rfl

theorem cell23_6620630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_6620630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620630 prefixEnd_6620630 := by exact prefixLift 6620630
  have htrace : WordTrace (prefixWord ++ tailWord_6620630) baseStart_6620630 baseEnd_6620630 := by
    simpa [prefixWord, tailWord_6620630, baseEnd_6620630] using wordTrace_append hprefix tailTrace_6620630
  have hstable : (prefixWord ++ tailWord_6620630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620630).length < 2 ^ (prefixWord ++ tailWord_6620630).sum := by decide
  have hdescent : baseEnd_6620630 < baseStart_6620630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620674 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6620674 : Nat := 118140960795 + 6620674 * 2 ^ 59
def prefixEnd_6620674 : Nat := 4983230072969 + 3 ^ 40 * 6620674 * 2
def baseEnd_6620674 : Nat := 3399588018725334816227081

theorem tailTrace_6620674 : CollatzResearch.WordTrace tailWord_6620674 prefixEnd_6620674 3399588018725334816227081 := by
  unfold tailWord_6620674
  simp only [CollatzResearch.WordTrace]
  refine ⟨60368954704109073485751269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160983879210957529295336717 60368954704109073485751269)
  ·
    refine ⟨11319179007020451278578363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60368954704109073485751269 11319179007020451278578363)
    ·
      refine ⟨16978768510530676917867545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319179007020451278578363 16978768510530676917867545)
      ·
        refine ⟨12734076382898007688400659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16978768510530676917867545 12734076382898007688400659)
        ·
          refine ⟨19101114574347011532600989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12734076382898007688400659 19101114574347011532600989)
          ·
            refine ⟨7162917965380129324725371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19101114574347011532600989 7162917965380129324725371)
            ·
              refine ⟨10744376948070193987088057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7162917965380129324725371 10744376948070193987088057)
              ·
                refine ⟨8058282711052645490316043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10744376948070193987088057 8058282711052645490316043)
                ·
                  refine ⟨12087424066578968235474065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058282711052645490316043 12087424066578968235474065)
                  ·
                    refine ⟨9065568049934226176605549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12087424066578968235474065 9065568049934226176605549)
                    ·
                      refine ⟨3399588018725334816227081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9065568049934226176605549 3399588018725334816227081)
                      ·
                        rfl

theorem cell23_6620674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6620674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620674 prefixEnd_6620674 := by exact prefixLift 6620674
  have htrace : WordTrace (prefixWord ++ tailWord_6620674) baseStart_6620674 baseEnd_6620674 := by
    simpa [prefixWord, tailWord_6620674, baseEnd_6620674] using wordTrace_append hprefix tailTrace_6620674
  have hstable : (prefixWord ++ tailWord_6620674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620674).length < 2 ^ (prefixWord ++ tailWord_6620674).sum := by decide
  have hdescent : baseEnd_6620674 < baseStart_6620674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620723 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 4]
def baseStart_6620723 : Nat := 118140960795 + 6620723 * 2 ^ 59
def prefixEnd_6620723 : Nat := 4983230072969 + 3 ^ 40 * 6620723 * 2
def baseEnd_6620723 : Nat := 3399613179277405124514355

theorem tailTrace_6620723 : CollatzResearch.WordTrace tailWord_6620723 prefixEnd_6620723 3399613179277405124514355 := by
  unfold tailWord_6620723
  simp only [CollatzResearch.WordTrace]
  refine ⟨241477605993258775311538823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160985070662172516874359215 241477605993258775311538823)
  ·
    refine ⟨362216408989888162967308235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241477605993258775311538823 362216408989888162967308235)
    ·
      refine ⟨543324613484832244450962353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362216408989888162967308235 543324613484832244450962353)
      ·
        refine ⟨407493460113624183338221765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543324613484832244450962353 407493460113624183338221765)
        ·
          refine ⟨76405023771304534375916581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407493460113624183338221765 76405023771304534375916581)
          ·
            refine ⟨14325941957119600195484359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76405023771304534375916581 14325941957119600195484359)
            ·
              refine ⟨21488912935679400293226539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14325941957119600195484359 21488912935679400293226539)
              ·
                refine ⟨32233369403519100439839809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21488912935679400293226539 32233369403519100439839809)
                ·
                  refine ⟨24175027052639325329879857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32233369403519100439839809 24175027052639325329879857)
                  ·
                    refine ⟨18131270289479493997409893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24175027052639325329879857 18131270289479493997409893)
                    ·
                      refine ⟨3399613179277405124514355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18131270289479493997409893 3399613179277405124514355)
                      ·
                        rfl

theorem cell23_6620723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_6620723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620723 prefixEnd_6620723 := by exact prefixLift 6620723
  have htrace : WordTrace (prefixWord ++ tailWord_6620723) baseStart_6620723 baseEnd_6620723 := by
    simpa [prefixWord, tailWord_6620723, baseEnd_6620723] using wordTrace_append hprefix tailTrace_6620723
  have hstable : (prefixWord ++ tailWord_6620723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620723).length < 2 ^ (prefixWord ++ tailWord_6620723).sum := by decide
  have hdescent : baseEnd_6620723 < baseStart_6620723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620727 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 2, 2, 2]
def baseStart_6620727 : Nat := 118140960795 + 6620727 * 2 ^ 59
def prefixEnd_6620727 : Nat := 4983230072969 + 3 ^ 40 * 6620727 * 2
def baseEnd_6620727 : Nat := 3399615233200023108864337

theorem tailTrace_6620727 : CollatzResearch.WordTrace tailWord_6620727 prefixEnd_6620727 3399615233200023108864337 := by
  unfold tailWord_6620727
  simp only [CollatzResearch.WordTrace]
  refine ⟨241477751885244283994684435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160985167923496189329789623 241477751885244283994684435)
  ·
    refine ⟨362216627827866425992026653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241477751885244283994684435 362216627827866425992026653)
    ·
      refine ⟨135831235435449909747009995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362216627827866425992026653 135831235435449909747009995)
      ·
        refine ⟨203746853153174864620514993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135831235435449909747009995 203746853153174864620514993)
        ·
          refine ⟨152810139864881148465386245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203746853153174864620514993 152810139864881148465386245)
          ·
            refine ⟨28651901224665215337259921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152810139864881148465386245 28651901224665215337259921)
            ·
              refine ⟨21488925918498911502944941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28651901224665215337259921 21488925918498911502944941)
              ·
                refine ⟨8058347219437091813604353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21488925918498911502944941 8058347219437091813604353)
                ·
                  refine ⟨6043760414577818860203265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8058347219437091813604353 6043760414577818860203265)
                  ·
                    refine ⟨4532820310933364145152449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6043760414577818860203265 4532820310933364145152449)
                    ·
                      refine ⟨3399615233200023108864337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4532820310933364145152449 3399615233200023108864337)
                      ·
                        rfl

theorem cell23_6620727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_6620727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620727 prefixEnd_6620727 := by exact prefixLift 6620727
  have htrace : WordTrace (prefixWord ++ tailWord_6620727) baseStart_6620727 baseEnd_6620727 := by
    simpa [prefixWord, tailWord_6620727, baseEnd_6620727] using wordTrace_append hprefix tailTrace_6620727
  have hstable : (prefixWord ++ tailWord_6620727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620727).length < 2 ^ (prefixWord ++ tailWord_6620727).sum := by decide
  have hdescent : baseEnd_6620727 < baseStart_6620727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620823 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 8]
def baseStart_6620823 : Nat := 118140960795 + 6620823 * 2 ^ 59
def prefixEnd_6620823 : Nat := 4983230072969 + 3 ^ 40 * 6620823 * 2
def baseEnd_6620823 : Nat := 377740503038094970362655

theorem tailTrace_6620823 : CollatzResearch.WordTrace tailWord_6620823 prefixEnd_6620823 377740503038094970362655 := by
  unfold tailWord_6620823
  simp only [CollatzResearch.WordTrace]
  refine ⟨241481253292896492390179123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160987502195264328260119415 241481253292896492390179123)
  ·
    refine ⟨362221879939344738585268685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241481253292896492390179123 362221879939344738585268685)
    ·
      refine ⟨135833204977254276969475757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362221879939344738585268685 135833204977254276969475757)
      ·
        refine ⟨50937451866470353863553409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135833204977254276969475757 50937451866470353863553409)
        ·
          refine ⟨38203088899852765397665057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50937451866470353863553409 38203088899852765397665057)
          ·
            refine ⟨28652316674889574048248793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38203088899852765397665057 28652316674889574048248793)
            ·
              refine ⟨21489237506167180536186595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28652316674889574048248793 21489237506167180536186595)
              ·
                refine ⟨32233856259250770804279893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21489237506167180536186595 32233856259250770804279893)
                ·
                  refine ⟨377740503038094970362655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32233856259250770804279893 377740503038094970362655)
                  ·
                    rfl

theorem cell23_6620823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 8].length) (baseStart_6620823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620823 prefixEnd_6620823 := by exact prefixLift 6620823
  have htrace : WordTrace (prefixWord ++ tailWord_6620823) baseStart_6620823 baseEnd_6620823 := by
    simpa [prefixWord, tailWord_6620823, baseEnd_6620823] using wordTrace_append hprefix tailTrace_6620823
  have hstable : (prefixWord ++ tailWord_6620823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620823).length < 2 ^ (prefixWord ++ tailWord_6620823).sum := by decide
  have hdescent : baseEnd_6620823 < baseStart_6620823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620854 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_6620854 : Nat := 118140960795 + 6620854 * 2 ^ 59
def prefixEnd_6620854 : Nat := 4983230072969 + 3 ^ 40 * 6620854 * 2
def baseEnd_6620854 : Nat := 3399680445243144111976253

theorem tailTrace_6620854 : CollatzResearch.WordTrace tailWord_6620854 prefixEnd_6620854 3399680445243144111976253 := by
  unfold tailWord_6620854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092648997236511542784851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160988255970522789789705077 15092648997236511542784851)
  ·
    refine ⟨22638973495854767314177277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15092648997236511542784851 22638973495854767314177277)
    ·
      refine ⟨8489615060945537742816479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22638973495854767314177277 8489615060945537742816479)
      ·
        refine ⟨12734422591418306614224719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8489615060945537742816479 12734422591418306614224719)
        ·
          refine ⟨19101633887127459921337079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12734422591418306614224719 19101633887127459921337079)
          ·
            refine ⟨28652450830691189882005619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19101633887127459921337079 28652450830691189882005619)
            ·
              refine ⟨42978676246036784823008429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28652450830691189882005619 42978676246036784823008429)
              ·
                refine ⟨16117003592263794308628161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42978676246036784823008429 16117003592263794308628161)
                ·
                  refine ⟨12087752694197845731471121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16117003592263794308628161 12087752694197845731471121)
                  ·
                    refine ⟨9065814520648384298603341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12087752694197845731471121 9065814520648384298603341)
                    ·
                      refine ⟨3399680445243144111976253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9065814520648384298603341 3399680445243144111976253)
                      ·
                        rfl

theorem cell23_6620854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_6620854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620854 prefixEnd_6620854 := by exact prefixLift 6620854
  have htrace : WordTrace (prefixWord ++ tailWord_6620854) baseStart_6620854 baseEnd_6620854 := by
    simpa [prefixWord, tailWord_6620854, baseEnd_6620854] using wordTrace_append hprefix tailTrace_6620854
  have hstable : (prefixWord ++ tailWord_6620854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620854).length < 2 ^ (prefixWord ++ tailWord_6620854).sum := by decide
  have hdescent : baseEnd_6620854 < baseStart_6620854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620890 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_6620890 : Nat := 118140960795 + 6620890 * 2 ^ 59
def prefixEnd_6620890 : Nat := 4983230072969 + 3 ^ 40 * 6620890 * 2
def baseEnd_6620890 : Nat := 3399698930546705971126087

theorem tailTrace_6620890 : CollatzResearch.WordTrace tailWord_6620890 prefixEnd_6620890 3399698930546705971126087 := by
  unfold tailWord_6620890
  simp only [CollatzResearch.WordTrace]
  refine ⟨60370924245913440708217031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160989131322435841888578749 60370924245913440708217031)
  ·
    refine ⟨90556386368870161062325547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60370924245913440708217031 90556386368870161062325547)
    ·
      refine ⟨135834579553305241593488321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90556386368870161062325547 135834579553305241593488321)
      ·
        refine ⟨101875934664978931195116241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135834579553305241593488321 101875934664978931195116241)
        ·
          refine ⟨76406950998734198396337181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101875934664978931195116241 76406950998734198396337181)
          ·
            refine ⟨28652606624525324398626443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76406950998734198396337181 28652606624525324398626443)
            ·
              refine ⟨42978909936787986597939665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28652606624525324398626443 42978909936787986597939665)
              ·
                refine ⟨32234182452590989948454749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42978909936787986597939665 32234182452590989948454749)
                ·
                  refine ⟨12087818419721621230670531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32234182452590989948454749 12087818419721621230670531)
                  ·
                    refine ⟨18131727629582431846005797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12087818419721621230670531 18131727629582431846005797)
                    ·
                      refine ⟨3399698930546705971126087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18131727629582431846005797 3399698930546705971126087)
                      ·
                        rfl

theorem cell23_6620890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_6620890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620890 prefixEnd_6620890 := by exact prefixLift 6620890
  have htrace : WordTrace (prefixWord ++ tailWord_6620890) baseStart_6620890 baseEnd_6620890 := by
    simpa [prefixWord, tailWord_6620890, baseEnd_6620890] using wordTrace_append hprefix tailTrace_6620890
  have hstable : (prefixWord ++ tailWord_6620890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620890).length < 2 ^ (prefixWord ++ tailWord_6620890).sum := by decide
  have hdescent : baseEnd_6620890 < baseStart_6620890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620900 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_6620900 : Nat := 118140960795 + 6620900 * 2 ^ 59
def prefixEnd_6620900 : Nat := 4983230072969 + 3 ^ 40 * 6620900 * 2
def baseEnd_6620900 : Nat := 1133234688451083644000347

theorem tailTrace_6620900 : CollatzResearch.WordTrace tailWord_6620900 prefixEnd_6620900 1133234688451083644000347 := by
  unfold tailWord_6620900
  simp only [CollatzResearch.WordTrace]
  refine ⟨120742030856808767270366077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160989374475745023027154769 120742030856808767270366077)
  ·
    refine ⟨45278261571303287726387279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120742030856808767270366077 45278261571303287726387279)
    ·
      refine ⟨67917392356954931589580919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45278261571303287726387279 67917392356954931589580919)
      ·
        refine ⟨101876088535432397384371379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67917392356954931589580919 101876088535432397384371379)
        ·
          refine ⟨152814132803148596076557069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101876088535432397384371379 152814132803148596076557069)
          ·
            refine ⟨57305299801180723528708901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152814132803148596076557069 57305299801180723528708901)
            ·
              refine ⟨10744743712721385661632919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57305299801180723528708901 10744743712721385661632919)
              ·
                refine ⟨16117115569082078492449379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10744743712721385661632919 16117115569082078492449379)
                ·
                  refine ⟨24175673353623117738674069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16117115569082078492449379 24175673353623117738674069)
                  ·
                    refine ⟨1133234688451083644000347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24175673353623117738674069 1133234688451083644000347)
                    ·
                      rfl

theorem cell23_6620900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_6620900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620900 prefixEnd_6620900 := by exact prefixLift 6620900
  have htrace : WordTrace (prefixWord ++ tailWord_6620900) baseStart_6620900 baseEnd_6620900 := by
    simpa [prefixWord, tailWord_6620900, baseEnd_6620900] using wordTrace_append hprefix tailTrace_6620900
  have hstable : (prefixWord ++ tailWord_6620900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620900).length < 2 ^ (prefixWord ++ tailWord_6620900).sum := by decide
  have hdescent : baseEnd_6620900 < baseStart_6620900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620907 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 5, 2, 2]
def baseStart_6620907 : Nat := 118140960795 + 6620907 * 2 ^ 59
def prefixEnd_6620907 : Nat := 4983230072969 + 3 ^ 40 * 6620907 * 2
def baseEnd_6620907 : Nat := 3399707659717832404613509

theorem tailTrace_6620907 : CollatzResearch.WordTrace tailWord_6620907 prefixEnd_6620907 3399707659717832404613509 := by
  unfold tailWord_6620907
  simp only [CollatzResearch.WordTrace]
  refine ⟨241484317024592174736236975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160989544683061449824157983 241484317024592174736236975)
  ·
    refine ⟨362226475536888262104355463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241484317024592174736236975 362226475536888262104355463)
    ·
      refine ⟨543339713305332393156533195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362226475536888262104355463 543339713305332393156533195)
      ·
        refine ⟨815009569957998589734799793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543339713305332393156533195 815009569957998589734799793)
        ·
          refine ⟨611257177468498942301099845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815009569957998589734799793 611257177468498942301099845)
          ·
            refine ⟨114610720775343551681456221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 611257177468498942301099845 114610720775343551681456221)
            ·
              refine ⟨42979020290753831880546083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114610720775343551681456221 42979020290753831880546083)
              ·
                refine ⟨64468530436130747820819125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42979020290753831880546083 64468530436130747820819125)
                ·
                  refine ⟨6043924728387257608201793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64468530436130747820819125 6043924728387257608201793)
                  ·
                    refine ⟨4532943546290443206151345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6043924728387257608201793 4532943546290443206151345)
                    ·
                      refine ⟨3399707659717832404613509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4532943546290443206151345 3399707659717832404613509)
                      ·
                        rfl

theorem cell23_6620907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 2, 2].length) (baseStart_6620907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620907 prefixEnd_6620907 := by exact prefixLift 6620907
  have htrace : WordTrace (prefixWord ++ tailWord_6620907) baseStart_6620907 baseEnd_6620907 := by
    simpa [prefixWord, tailWord_6620907, baseEnd_6620907] using wordTrace_append hprefix tailTrace_6620907
  have hstable : (prefixWord ++ tailWord_6620907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620907).length < 2 ^ (prefixWord ++ tailWord_6620907).sum := by decide
  have hdescent : baseEnd_6620907 < baseStart_6620907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620930 : List Nat := [3, 4, 1, 1, 1, 1, 12]
def baseStart_6620930 : Nat := 118140960795 + 6620930 * 2 ^ 59
def prefixEnd_6620930 : Nat := 4983230072969 + 3 ^ 40 * 6620930 * 2
def baseEnd_6620930 : Nat := 41971845305838096476863

theorem tailTrace_6620930 : CollatzResearch.WordTrace tailWord_6620930 prefixEnd_6620930 41971845305838096476863 := by
  unfold tailWord_6620930
  simp only [CollatzResearch.WordTrace]
  refine ⟨60371288975877212416081061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160990103935672566442882829 60371288975877212416081061)
  ·
    refine ⟨11319616682976977328015199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60371288975877212416081061 11319616682976977328015199)
    ·
      refine ⟨16979425024465465992022799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319616682976977328015199 16979425024465465992022799)
      ·
        refine ⟨25469137536698198988034199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16979425024465465992022799 25469137536698198988034199)
        ·
          refine ⟨38203706305047298482051299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25469137536698198988034199 38203706305047298482051299)
          ·
            refine ⟨57305559457570947723076949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38203706305047298482051299 57305559457570947723076949)
            ·
              refine ⟨41971845305838096476863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 57305559457570947723076949 41971845305838096476863)
              ·
                rfl

theorem cell23_6620930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 12].length) (baseStart_6620930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620930 prefixEnd_6620930 := by exact prefixLift 6620930
  have htrace : WordTrace (prefixWord ++ tailWord_6620930) baseStart_6620930 baseEnd_6620930 := by
    simpa [prefixWord, tailWord_6620930, baseEnd_6620930] using wordTrace_append hprefix tailTrace_6620930
  have hstable : (prefixWord ++ tailWord_6620930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620930).length < 2 ^ (prefixWord ++ tailWord_6620930).sum := by decide
  have hdescent : baseEnd_6620930 < baseStart_6620930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620933 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_6620933 : Nat := 118140960795 + 6620933 * 2 ^ 59
def prefixEnd_6620933 : Nat := 4983230072969 + 3 ^ 40 * 6620933 * 2
def baseEnd_6620933 : Nat := 3399721010214849302888389

theorem tailTrace_6620933 : CollatzResearch.WordTrace tailWord_6620933 prefixEnd_6620933 3399721010214849302888389 := by
  unfold tailWord_6620933
  simp only [CollatzResearch.WordTrace]
  refine ⟨241485265322497981176683453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160990176881665320784455635 241485265322497981176683453)
  ·
    refine ⟨90556974495936742941256295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241485265322497981176683453 90556974495936742941256295)
    ·
      refine ⟨135835461743905114411884443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90556974495936742941256295 135835461743905114411884443)
      ·
        refine ⟨203753192615857671617826665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135835461743905114411884443 203753192615857671617826665)
        ·
          refine ⟨152814894461893253713369999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203753192615857671617826665 152814894461893253713369999)
          ·
            refine ⟨229222341692839880570054999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152814894461893253713369999 229222341692839880570054999)
            ·
              refine ⟨343833512539259820855082499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229222341692839880570054999 343833512539259820855082499)
              ·
                refine ⟨515750268808889731282623749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343833512539259820855082499 515750268808889731282623749)
                ·
                  refine ⟨96703175401666824615491953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 515750268808889731282623749 96703175401666824615491953)
                  ·
                    refine ⟨72527381551250118461618965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96703175401666824615491953 72527381551250118461618965)
                    ·
                      refine ⟨3399721010214849302888389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72527381551250118461618965 3399721010214849302888389)
                      ·
                        rfl

theorem cell23_6620933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_6620933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620933 prefixEnd_6620933 := by exact prefixLift 6620933
  have htrace : WordTrace (prefixWord ++ tailWord_6620933) baseStart_6620933 baseEnd_6620933 := by
    simpa [prefixWord, tailWord_6620933, baseEnd_6620933] using wordTrace_append hprefix tailTrace_6620933
  have hstable : (prefixWord ++ tailWord_6620933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620933).length < 2 ^ (prefixWord ++ tailWord_6620933).sum := by decide
  have hdescent : baseEnd_6620933 < baseStart_6620933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620940 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_6620940 : Nat := 118140960795 + 6620940 * 2 ^ 59
def prefixEnd_6620940 : Nat := 4983230072969 + 3 ^ 40 * 6620940 * 2
def baseEnd_6620940 : Nat := 3399724604579430775500857

theorem tailTrace_6620940 : CollatzResearch.WordTrace tailWord_6620940 prefixEnd_6620940 3399724604579430775500857 := by
  unfold tailWord_6620940
  simp only [CollatzResearch.WordTrace]
  refine ⟨120742760316736310686094137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160990347088981747581458849 120742760316736310686094137)
  ·
    refine ⟨90557070237552233014570603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120742760316736310686094137 90557070237552233014570603)
    ·
      refine ⟨135835605356328349521855905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90557070237552233014570603 135835605356328349521855905)
      ·
        refine ⟨101876704017246262141391929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135835605356328349521855905 101876704017246262141391929)
        ·
          refine ⟨76407528012934696606043947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101876704017246262141391929 76407528012934696606043947)
          ·
            refine ⟨114611292019402044909065921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76407528012934696606043947 114611292019402044909065921)
            ·
              refine ⟨85958469014551533681799441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114611292019402044909065921 85958469014551533681799441)
              ·
                refine ⟨64468851760913650261349581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85958469014551533681799441 64468851760913650261349581)
                ·
                  refine ⟨24175819410342618848006093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64468851760913650261349581 24175819410342618848006093)
                  ·
                    refine ⟨9065932278878482068002285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24175819410342618848006093 9065932278878482068002285)
                    ·
                      refine ⟨3399724604579430775500857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9065932278878482068002285 3399724604579430775500857)
                      ·
                        rfl

theorem cell23_6620940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_6620940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620940 prefixEnd_6620940 := by exact prefixLift 6620940
  have htrace : WordTrace (prefixWord ++ tailWord_6620940) baseStart_6620940 baseEnd_6620940 := by
    simpa [prefixWord, tailWord_6620940, baseEnd_6620940] using wordTrace_append hprefix tailTrace_6620940
  have hstable : (prefixWord ++ tailWord_6620940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620940).length < 2 ^ (prefixWord ++ tailWord_6620940).sum := by decide
  have hdescent : baseEnd_6620940 < baseStart_6620940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620943 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 2, 7]
def baseStart_6620943 : Nat := 118140960795 + 6620943 * 2 ^ 59
def prefixEnd_6620943 : Nat := 4983230072969 + 3 ^ 40 * 6620943 * 2
def baseEnd_6620943 : Nat := 1133242048340464754587781

theorem tailTrace_6620943 : CollatzResearch.WordTrace tailWord_6620943 prefixEnd_6620943 1133242048340464754587781 := by
  unfold tailWord_6620943
  simp only [CollatzResearch.WordTrace]
  refine ⟨241485630052461752884547483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160990420034974501923031655 241485630052461752884547483)
  ·
    refine ⟨362228445078692629326821225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241485630052461752884547483 362228445078692629326821225)
    ·
      refine ⟨271671333809019471995115919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362228445078692629326821225 271671333809019471995115919)
      ·
        refine ⟨407507000713529207992673879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271671333809019471995115919 407507000713529207992673879)
        ·
          refine ⟨611260501070293811989010819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407507000713529207992673879 611260501070293811989010819)
          ·
            refine ⟨916890751605440717983516229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611260501070293811989010819 916890751605440717983516229)
            ·
              refine ⟨171917015926020134621909293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 916890751605440717983516229 171917015926020134621909293)
              ·
                refine ⟨64468880972257550483215985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171917015926020134621909293 64468880972257550483215985)
                ·
                  refine ⟨48351660729193162862411989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64468880972257550483215985 48351660729193162862411989)
                  ·
                    refine ⟨1133242048340464754587781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48351660729193162862411989 1133242048340464754587781)
                    ·
                      rfl

theorem cell23_6620943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_6620943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620943 prefixEnd_6620943 := by exact prefixLift 6620943
  have htrace : WordTrace (prefixWord ++ tailWord_6620943) baseStart_6620943 baseEnd_6620943 := by
    simpa [prefixWord, tailWord_6620943, baseEnd_6620943] using wordTrace_append hprefix tailTrace_6620943
  have hstable : (prefixWord ++ tailWord_6620943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620943).length < 2 ^ (prefixWord ++ tailWord_6620943).sum := by decide
  have hdescent : baseEnd_6620943 < baseStart_6620943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620958 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6620958 : Nat := 118140960795 + 6620958 * 2 ^ 59
def prefixEnd_6620958 : Nat := 4983230072969 + 3 ^ 40 * 6620958 * 2
def baseEnd_6620958 : Nat := 3399733847231211705075775

theorem tailTrace_6620958 : CollatzResearch.WordTrace tailWord_6620958 prefixEnd_6620958 3399733847231211705075775 := by
  unfold tailWord_6620958
  simp only [CollatzResearch.WordTrace]
  refine ⟨30185772143425926305792941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160990784764938273630895685 30185772143425926305792941)
  ·
    refine ⟨11319664553784722364672353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30185772143425926305792941 11319664553784722364672353)
    ·
      refine ⟨8489748415338541773504265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11319664553784722364672353 8489748415338541773504265)
      ·
        refine ⟨6367311311503906330128199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8489748415338541773504265 6367311311503906330128199)
        ·
          refine ⟨9550966967255859495192299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367311311503906330128199 9550966967255859495192299)
          ·
            refine ⟨14326450450883789242788449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9550966967255859495192299 14326450450883789242788449)
            ·
              refine ⟨10744837838162841932091337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14326450450883789242788449 10744837838162841932091337)
              ·
                refine ⟨8058628378622131449068503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10744837838162841932091337 8058628378622131449068503)
                ·
                  refine ⟨12087942567933197173602755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058628378622131449068503 12087942567933197173602755)
                  ·
                    refine ⟨18131913851899795760404133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12087942567933197173602755 18131913851899795760404133)
                    ·
                      refine ⟨3399733847231211705075775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18131913851899795760404133 3399733847231211705075775)
                      ·
                        rfl

theorem cell23_6620958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6620958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620958 prefixEnd_6620958 := by exact prefixLift 6620958
  have htrace : WordTrace (prefixWord ++ tailWord_6620958) baseStart_6620958 baseEnd_6620958 := by
    simpa [prefixWord, tailWord_6620958, baseEnd_6620958] using wordTrace_append hprefix tailTrace_6620958
  have hstable : (prefixWord ++ tailWord_6620958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620958).length < 2 ^ (prefixWord ++ tailWord_6620958).sum := by decide
  have hdescent : baseEnd_6620958 < baseStart_6620958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6620984 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 1, 3, 2]
def baseStart_6620984 : Nat := 118140960795 + 6620984 * 2 ^ 59
def prefixEnd_6620984 : Nat := 4983230072969 + 3 ^ 40 * 6620984 * 2
def baseEnd_6620984 : Nat := 3399747197728228603350655

theorem tailTrace_6620984 : CollatzResearch.WordTrace tailWord_6620984 prefixEnd_6620984 3399747197728228603350655 := by
  unfold tailWord_6620984
  simp only [CollatzResearch.WordTrace]
  refine ⟨120743562722656608443395003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160991416963542144591193337 120743562722656608443395003)
  ·
    refine ⟨181115344083984912665092505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120743562722656608443395003 181115344083984912665092505)
    ·
      refine ⟨135836508062988684498819379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181115344083984912665092505 135836508062988684498819379)
      ·
        refine ⟨203754762094483026748229069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135836508062988684498819379 203754762094483026748229069)
        ·
          refine ⟨76408035785431135030585901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203754762094483026748229069 76408035785431135030585901)
          ·
            refine ⟨28653013419536675636469713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76408035785431135030585901 28653013419536675636469713)
            ·
              refine ⟨21489760064652506727352285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28653013419536675636469713 21489760064652506727352285)
              ·
                refine ⟨8058660024244690022757107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21489760064652506727352285 8058660024244690022757107)
                ·
                  refine ⟨12087990036367035034135661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058660024244690022757107 12087990036367035034135661)
                  ·
                    refine ⟨4532996263637638137800873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12087990036367035034135661 4532996263637638137800873)
                    ·
                      refine ⟨3399747197728228603350655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4532996263637638137800873 3399747197728228603350655)
                      ·
                        rfl

theorem cell23_6620984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_6620984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6620984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6620984 prefixEnd_6620984 := by exact prefixLift 6620984
  have htrace : WordTrace (prefixWord ++ tailWord_6620984) baseStart_6620984 baseEnd_6620984 := by
    simpa [prefixWord, tailWord_6620984, baseEnd_6620984] using wordTrace_append hprefix tailTrace_6620984
  have hstable : (prefixWord ++ tailWord_6620984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6620984).length < 2 ^ (prefixWord ++ tailWord_6620984).sum := by decide
  have hdescent : baseEnd_6620984 < baseStart_6620984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6620984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621064 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_6621064 : Nat := 118140960795 + 6621064 * 2 ^ 59
def prefixEnd_6621064 : Nat := 4983230072969 + 3 ^ 40 * 6621064 * 2
def baseEnd_6621064 : Nat := 3399788276180588290350287

theorem tailTrace_6621064 : CollatzResearch.WordTrace tailWord_6621064 prefixEnd_6621064 3399788276180588290350287 := by
  unfold tailWord_6621064
  simp only [CollatzResearch.WordTrace]
  refine ⟨120745021642511695274851123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160993362190015593699801497 120745021642511695274851123)
  ·
    refine ⟨181117532463767542912276685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120745021642511695274851123 181117532463767542912276685)
    ·
      refine ⟨67919074673912828592103757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181117532463767542912276685 67919074673912828592103757)
      ·
        refine ⟨25469653002717310722038909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67919074673912828592103757 25469653002717310722038909)
        ·
          refine ⟨9551119876018991520764591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25469653002717310722038909 9551119876018991520764591)
          ·
            refine ⟨14326679814028487281146887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9551119876018991520764591 14326679814028487281146887)
            ·
              refine ⟨21490019721042730921720331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14326679814028487281146887 21490019721042730921720331)
              ·
                refine ⟨32235029581564096382580497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21490019721042730921720331 32235029581564096382580497)
                ·
                  refine ⟨24176272186173072286935373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32235029581564096382580497 24176272186173072286935373)
                  ·
                    refine ⟨9066102069814902107600765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24176272186173072286935373 9066102069814902107600765)
                    ·
                      refine ⟨3399788276180588290350287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9066102069814902107600765 3399788276180588290350287)
                      ·
                        rfl

theorem cell23_6621064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_6621064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621064 prefixEnd_6621064 := by exact prefixLift 6621064
  have htrace : WordTrace (prefixWord ++ tailWord_6621064) baseStart_6621064 baseEnd_6621064 := by
    simpa [prefixWord, tailWord_6621064, baseEnd_6621064] using wordTrace_append hprefix tailTrace_6621064
  have hstable : (prefixWord ++ tailWord_6621064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621064).length < 2 ^ (prefixWord ++ tailWord_6621064).sum := by decide
  have hdescent : baseEnd_6621064 < baseStart_6621064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621084 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_6621084 : Nat := 118140960795 + 6621084 * 2 ^ 59
def prefixEnd_6621084 : Nat := 4983230072969 + 3 ^ 40 * 6621084 * 2
def baseEnd_6621084 : Nat := 1133266181931226070700065

theorem tailTrace_6621084 : CollatzResearch.WordTrace tailWord_6621084 prefixEnd_6621084 1133266181931226070700065 := by
  unfold tailWord_6621084
  simp only [CollatzResearch.WordTrace]
  refine ⟨120745386372475466982715153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160993848496633955976953537 120745386372475466982715153)
  ·
    refine ⟨90559039779356600237036365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120745386372475466982715153 90559039779356600237036365)
    ·
      refine ⟨33959639917258725088888637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90559039779356600237036365 33959639917258725088888637)
      ·
        refine ⟨12734864968972021908333239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33959639917258725088888637 12734864968972021908333239)
        ·
          refine ⟨19102297453458032862499859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12734864968972021908333239 19102297453458032862499859)
          ·
            refine ⟨28653446180187049293749789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19102297453458032862499859 28653446180187049293749789)
            ·
              refine ⟨10745042317570143485156171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28653446180187049293749789 10745042317570143485156171)
              ·
                refine ⟨16117563476355215227734257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10745042317570143485156171 16117563476355215227734257)
                ·
                  refine ⟨12088172607266411420800693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16117563476355215227734257 12088172607266411420800693)
                  ·
                    refine ⟨1133266181931226070700065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12088172607266411420800693 1133266181931226070700065)
                    ·
                      rfl

theorem cell23_6621084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_6621084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621084 prefixEnd_6621084 := by exact prefixLift 6621084
  have htrace : WordTrace (prefixWord ++ tailWord_6621084) baseStart_6621084 baseEnd_6621084 := by
    simpa [prefixWord, tailWord_6621084, baseEnd_6621084] using wordTrace_append hprefix tailTrace_6621084
  have hstable : (prefixWord ++ tailWord_6621084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621084).length < 2 ^ (prefixWord ++ tailWord_6621084).sum := by decide
  have hdescent : baseEnd_6621084 < baseStart_6621084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621107 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 3]
def baseStart_6621107 : Nat := 118140960795 + 6621107 * 2 ^ 59
def prefixEnd_6621107 : Nat := 4983230072969 + 3 ^ 40 * 6621107 * 2
def baseEnd_6621107 : Nat := 3399810355848731622112589

theorem tailTrace_6621107 : CollatzResearch.WordTrace tailWord_6621107 prefixEnd_6621107 3399810355848731622112589 := by
  unfold tailWord_6621107
  simp only [CollatzResearch.WordTrace]
  refine ⟨241491611623867608893517575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160994407749245072595678383 241491611623867608893517575)
  ·
    refine ⟨362237417435801413340276363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241491611623867608893517575 362237417435801413340276363)
    ·
      refine ⟨543356126153702120010414545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362237417435801413340276363 543356126153702120010414545)
      ·
        refine ⟨407517094615276590007810909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543356126153702120010414545 407517094615276590007810909)
        ·
          refine ⟨152818910480728721252929091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407517094615276590007810909 152818910480728721252929091)
          ·
            refine ⟨229228365721093081879393637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152818910480728721252929091 229228365721093081879393637)
            ·
              refine ⟨42980318572704952852386307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229228365721093081879393637 42980318572704952852386307)
              ·
                refine ⟨64470477859057429278579461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42980318572704952852386307 64470477859057429278579461)
                ·
                  refine ⟨12088214598573267989733649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64470477859057429278579461 12088214598573267989733649)
                  ·
                    refine ⟨9066160948929950992300237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12088214598573267989733649 9066160948929950992300237)
                    ·
                      refine ⟨3399810355848731622112589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9066160948929950992300237 3399810355848731622112589)
                      ·
                        rfl

theorem cell23_6621107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_6621107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621107 prefixEnd_6621107 := by exact prefixLift 6621107
  have htrace : WordTrace (prefixWord ++ tailWord_6621107) baseStart_6621107 baseEnd_6621107 := by
    simpa [prefixWord, tailWord_6621107, baseEnd_6621107] using wordTrace_append hprefix tailTrace_6621107
  have hstable : (prefixWord ++ tailWord_6621107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621107).length < 2 ^ (prefixWord ++ tailWord_6621107).sum := by decide
  have hdescent : baseEnd_6621107 < baseStart_6621107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621165 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_6621165 : Nat := 118140960795 + 6621165 * 2 ^ 59
def prefixEnd_6621165 : Nat := 4983230072969 + 3 ^ 40 * 6621165 * 2
def baseEnd_6621165 : Nat := 1133280045908897465062441

theorem tailTrace_6621165 : CollatzResearch.WordTrace tailWord_6621165 prefixEnd_6621165 1133280045908897465062441 := by
  unfold tailWord_6621165
  simp only [CollatzResearch.WordTrace]
  refine ⟨241493727057657484799128949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160995818038438323199419299 241493727057657484799128949)
  ·
    refine ⟨22640036911655389199918339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241493727057657484799128949 22640036911655389199918339)
    ·
      refine ⟨33960055367483083799877509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22640036911655389199918339 33960055367483083799877509)
      ·
        refine ⟨6367510381403078212477033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33960055367483083799877509 6367510381403078212477033)
        ·
          refine ⟨4775632786052308659357775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6367510381403078212477033 4775632786052308659357775)
          ·
            refine ⟨7163449179078462989036663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775632786052308659357775 7163449179078462989036663)
            ·
              refine ⟨10745173768617694483554995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7163449179078462989036663 10745173768617694483554995)
              ·
                refine ⟨16117760652926541725332493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10745173768617694483554995 16117760652926541725332493)
                ·
                  refine ⟨6044160244847453146999685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16117760652926541725332493 6044160244847453146999685)
                  ·
                    refine ⟨1133280045908897465062441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044160244847453146999685 1133280045908897465062441)
                    ·
                      rfl

theorem cell23_6621165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_6621165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621165 prefixEnd_6621165 := by exact prefixLift 6621165
  have htrace : WordTrace (prefixWord ++ tailWord_6621165) baseStart_6621165 baseEnd_6621165 := by
    simpa [prefixWord, tailWord_6621165, baseEnd_6621165] using wordTrace_append hprefix tailTrace_6621165
  have hstable : (prefixWord ++ tailWord_6621165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621165).length < 2 ^ (prefixWord ++ tailWord_6621165).sum := by decide
  have hdescent : baseEnd_6621165 < baseStart_6621165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621171 : List Nat := [1, 1, 1, 2, 2, 2, 1, 8, 1, 1, 3]
def baseStart_6621171 : Nat := 118140960795 + 6621171 * 2 ^ 59
def prefixEnd_6621171 : Nat := 4983230072969 + 3 ^ 40 * 6621171 * 2
def baseEnd_6621171 : Nat := 3399843218610619371712295

theorem tailTrace_6621171 : CollatzResearch.WordTrace tailWord_6621171 prefixEnd_6621171 3399843218610619371712295 := by
  unfold tailWord_6621171
  simp only [CollatzResearch.WordTrace]
  refine ⟨241493945895635747823847367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160995963930423831882564911 241493945895635747823847367)
  ·
    refine ⟨362240918843453621735771051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241493945895635747823847367 362240918843453621735771051)
    ·
      refine ⟨543361378265180432603656577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362240918843453621735771051 543361378265180432603656577)
      ·
        refine ⟨407521033698885324452742433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543361378265180432603656577 407521033698885324452742433)
        ·
          refine ⟨305640775274163993339556825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407521033698885324452742433 305640775274163993339556825)
          ·
            refine ⟨229230581455622995004667619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305640775274163993339556825 229230581455622995004667619)
            ·
              refine ⟨343845872183434492507001429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229230581455622995004667619 343845872183434492507001429)
              ·
                refine ⟨4029443814649622959066423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 343845872183434492507001429 4029443814649622959066423)
                ·
                  refine ⟨6044165721974434438599635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029443814649622959066423 6044165721974434438599635)
                  ·
                    refine ⟨9066248582961651657899453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6044165721974434438599635 9066248582961651657899453)
                    ·
                      refine ⟨3399843218610619371712295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9066248582961651657899453 3399843218610619371712295)
                      ·
                        rfl

theorem cell23_6621171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 1, 3].length) (baseStart_6621171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621171 prefixEnd_6621171 := by exact prefixLift 6621171
  have htrace : WordTrace (prefixWord ++ tailWord_6621171) baseStart_6621171 baseEnd_6621171 := by
    simpa [prefixWord, tailWord_6621171, baseEnd_6621171] using wordTrace_append hprefix tailTrace_6621171
  have hstable : (prefixWord ++ tailWord_6621171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621171).length < 2 ^ (prefixWord ++ tailWord_6621171).sum := by decide
  have hdescent : baseEnd_6621171 < baseStart_6621171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621191 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 1, 5]
def baseStart_6621191 : Nat := 118140960795 + 6621191 * 2 ^ 59
def prefixEnd_6621191 : Nat := 4983230072969 + 3 ^ 40 * 6621191 * 2
def baseEnd_6621191 : Nat := 1133284496074569764487401

theorem tailTrace_6621191 : CollatzResearch.WordTrace tailWord_6621191 prefixEnd_6621191 1133284496074569764487401 := by
  unfold tailWord_6621191
  simp only [CollatzResearch.WordTrace]
  refine ⟨241494675355563291239575427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160996450237042194159716951 241494675355563291239575427)
  ·
    refine ⟨362242013033344936859363141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241494675355563291239575427 362242013033344936859363141)
    ·
      refine ⟨67920377443752175661130589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362242013033344936859363141 67920377443752175661130589)
      ·
        refine ⟨25470141541407065872923971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67920377443752175661130589 25470141541407065872923971)
        ·
          refine ⟨38205212312110598809385957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25470141541407065872923971 38205212312110598809385957)
          ·
            refine ⟨7163477308520737276759867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38205212312110598809385957 7163477308520737276759867)
            ·
              refine ⟨10745215962781105915139801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7163477308520737276759867 10745215962781105915139801)
              ·
                refine ⟨8058911972085829436354851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10745215962781105915139801 8058911972085829436354851)
                ·
                  refine ⟨12088367958128744154532277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058911972085829436354851 12088367958128744154532277)
                  ·
                    refine ⟨1133284496074569764487401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12088367958128744154532277 1133284496074569764487401)
                    ·
                      rfl

theorem cell23_6621191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_6621191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621191 prefixEnd_6621191 := by exact prefixLift 6621191
  have htrace : WordTrace (prefixWord ++ tailWord_6621191) baseStart_6621191 baseEnd_6621191 := by
    simpa [prefixWord, tailWord_6621191, baseEnd_6621191] using wordTrace_append hprefix tailTrace_6621191
  have hstable : (prefixWord ++ tailWord_6621191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621191).length < 2 ^ (prefixWord ++ tailWord_6621191).sum := by decide
  have hdescent : baseEnd_6621191 < baseStart_6621191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621217 : List Nat := [1, 2, 3, 2, 4, 11]
def baseStart_6621217 : Nat := 118140960795 + 6621217 * 2 ^ 59
def prefixEnd_6621217 : Nat := 4983230072969 + 3 ^ 40 * 6621217 * 2
def baseEnd_6621217 : Nat := 13991221558521506961881

theorem tailTrace_6621217 : CollatzResearch.WordTrace tailWord_6621217 prefixEnd_6621217 13991221558521506961881 := by
  unfold tailWord_6621217
  simp only [CollatzResearch.WordTrace]
  refine ⟨241495623653469097680021905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160997082435646065120014603 241495623653469097680021905)
  ·
    refine ⟨181121717740101823260016429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241495623653469097680021905 181121717740101823260016429)
    ·
      refine ⟨67920644152538183722506161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181121717740101823260016429 67920644152538183722506161)
      ·
        refine ⟨50940483114403637791879621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67920644152538183722506161 50940483114403637791879621)
        ·
          refine ⟨9551340583950682085977429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50940483114403637791879621 9551340583950682085977429)
          ·
            refine ⟨13991221558521506961881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9551340583950682085977429 13991221558521506961881)
            ·
              rfl

theorem cell23_6621217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 11].length) (baseStart_6621217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621217 prefixEnd_6621217 := by exact prefixLift 6621217
  have htrace : WordTrace (prefixWord ++ tailWord_6621217) baseStart_6621217 baseEnd_6621217 := by
    simpa [prefixWord, tailWord_6621217, baseEnd_6621217] using wordTrace_append hprefix tailTrace_6621217
  have hstable : (prefixWord ++ tailWord_6621217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621217).length < 2 ^ (prefixWord ++ tailWord_6621217).sum := by decide
  have hdescent : baseEnd_6621217 < baseStart_6621217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621221 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_6621221 : Nat := 118140960795 + 6621221 * 2 ^ 59
def prefixEnd_6621221 : Nat := 4983230072969 + 3 ^ 40 * 6621221 * 2
def baseEnd_6621221 : Nat := 1133289630881114725362355

theorem tailTrace_6621221 : CollatzResearch.WordTrace tailWord_6621221 prefixEnd_6621221 1133289630881114725362355 := by
  unfold tailWord_6621221
  simp only [CollatzResearch.WordTrace]
  refine ⟨241495769545454606363167517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160997179696969737575445011 241495769545454606363167517)
  ·
    refine ⟨90560913579545477386187819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241495769545454606363167517 90560913579545477386187819)
    ·
      refine ⟨135841370369318216079281729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90560913579545477386187819 135841370369318216079281729)
      ·
        refine ⟨101881027776988662059461297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135841370369318216079281729 101881027776988662059461297)
        ·
          refine ⟨76410770832741496544595973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101881027776988662059461297 76410770832741496544595973)
          ·
            refine ⟨14327019531139030602111745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76410770832741496544595973 14327019531139030602111745)
            ·
              refine ⟨10745264648354272951583809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14327019531139030602111745 10745264648354272951583809)
              ·
                refine ⟨8058948486265704713687857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10745264648354272951583809 8058948486265704713687857)
                ·
                  refine ⟨6044211364699278535265893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8058948486265704713687857 6044211364699278535265893)
                  ·
                    refine ⟨1133289630881114725362355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044211364699278535265893 1133289630881114725362355)
                    ·
                      rfl

theorem cell23_6621221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_6621221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621221 prefixEnd_6621221 := by exact prefixLift 6621221
  have htrace : WordTrace (prefixWord ++ tailWord_6621221) baseStart_6621221 baseEnd_6621221 := by
    simpa [prefixWord, tailWord_6621221, baseEnd_6621221] using wordTrace_append hprefix tailTrace_6621221
  have hstable : (prefixWord ++ tailWord_6621221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621221).length < 2 ^ (prefixWord ++ tailWord_6621221).sum := by decide
  have hdescent : baseEnd_6621221 < baseStart_6621221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621234 : List Nat := [3, 2, 1, 1, 2, 5, 1, 8]
def baseStart_6621234 : Nat := 118140960795 + 6621234 * 2 ^ 59
def prefixEnd_6621234 : Nat := 4983230072969 + 3 ^ 40 * 6621234 * 2
def baseEnd_6621234 : Nat := 125921317329327875008315

theorem tailTrace_6621234 : CollatzResearch.WordTrace tailWord_6621234 prefixEnd_6621234 125921317329327875008315 := by
  unfold tailWord_6621234
  simp only [CollatzResearch.WordTrace]
  refine ⟨60374060923601877395847689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160997495796271673055593837 60374060923601877395847689)
  ·
    refine ⟨45280545692701408046885767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60374060923601877395847689 45280545692701408046885767)
    ·
      refine ⟨67920818539052112070328651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45280545692701408046885767 67920818539052112070328651)
      ·
        refine ⟨101881227808578168105492977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67920818539052112070328651 101881227808578168105492977)
        ·
          refine ⟨76410920856433626079119733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101881227808578168105492977 76410920856433626079119733)
          ·
            refine ⟨7163523830290652444917475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76410920856433626079119733 7163523830290652444917475)
            ·
              refine ⟨10745285745435978667376213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7163523830290652444917475 10745285745435978667376213)
              ·
                refine ⟨125921317329327875008315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10745285745435978667376213 125921317329327875008315)
                ·
                  rfl

theorem cell23_6621234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 8].length) (baseStart_6621234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621234 prefixEnd_6621234 := by exact prefixLift 6621234
  have htrace : WordTrace (prefixWord ++ tailWord_6621234) baseStart_6621234 baseEnd_6621234 := by
    simpa [prefixWord, tailWord_6621234, baseEnd_6621234] using wordTrace_append hprefix tailTrace_6621234
  have hstable : (prefixWord ++ tailWord_6621234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621234).length < 2 ^ (prefixWord ++ tailWord_6621234).sum := by decide
  have hdescent : baseEnd_6621234 < baseStart_6621234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621237 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_6621237 : Nat := 118140960795 + 6621237 * 2 ^ 59
def prefixEnd_6621237 : Nat := 4983230072969 + 3 ^ 40 * 6621237 * 2
def baseEnd_6621237 : Nat := 3399877108333816113486991

theorem tailTrace_6621237 : CollatzResearch.WordTrace tailWord_6621237 prefixEnd_6621237 3399877108333816113486991 := by
  unfold tailWord_6621237
  simp only [CollatzResearch.WordTrace]
  refine ⟨241496353113396641095749965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160997568742264427397166643 241496353113396641095749965)
  ·
    refine ⟨90561132417523740410906237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241496353113396641095749965 90561132417523740410906237)
    ·
      refine ⟨33960424656571402654089839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90561132417523740410906237 33960424656571402654089839)
      ·
        refine ⟨50940636984857103981134759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33960424656571402654089839 50940636984857103981134759)
        ·
          refine ⟨76410955477285655971702139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50940636984857103981134759 76410955477285655971702139)
          ·
            refine ⟨114616433215928483957553209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76410955477285655971702139 114616433215928483957553209)
            ·
              refine ⟨85962324911946362968164907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114616433215928483957553209 85962324911946362968164907)
              ·
                refine ⟨128943487367919544452247361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85962324911946362968164907 128943487367919544452247361)
                ·
                  refine ⟨96707615525939658339185521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128943487367919544452247361 96707615525939658339185521)
                  ·
                    refine ⟨72530711644454743754389141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96707615525939658339185521 72530711644454743754389141)
                    ·
                      refine ⟨3399877108333816113486991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72530711644454743754389141 3399877108333816113486991)
                      ·
                        rfl

theorem cell23_6621237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_6621237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621237 prefixEnd_6621237 := by exact prefixLift 6621237
  have htrace : WordTrace (prefixWord ++ tailWord_6621237) baseStart_6621237 baseEnd_6621237 := by
    simpa [prefixWord, tailWord_6621237, baseEnd_6621237] using wordTrace_append hprefix tailTrace_6621237
  have hstable : (prefixWord ++ tailWord_6621237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621237).length < 2 ^ (prefixWord ++ tailWord_6621237).sum := by decide
  have hdescent : baseEnd_6621237 < baseStart_6621237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621241 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 4]
def baseStart_6621241 : Nat := 118140960795 + 6621241 * 2 ^ 59
def prefixEnd_6621241 : Nat := 4983230072969 + 3 ^ 40 * 6621241 * 2
def baseEnd_6621241 : Nat := 3399879162256434097836973

theorem tailTrace_6621241 : CollatzResearch.WordTrace tailWord_6621241 prefixEnd_6621241 3399879162256434097836973 := by
  unfold tailWord_6621241
  simp only [CollatzResearch.WordTrace]
  refine ⟨241496499005382149778895577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160997666003588099852597051 241496499005382149778895577)
  ·
    refine ⟨181122374254036612334171683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241496499005382149778895577 181122374254036612334171683)
    ·
      refine ⟨271683561381054918501257525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181122374254036612334171683 271683561381054918501257525)
      ·
        refine ⟨25470333879473898609492893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271683561381054918501257525 25470333879473898609492893)
        ·
          refine ⟨9551375204802711978559835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25470333879473898609492893 9551375204802711978559835)
          ·
            refine ⟨14327062807204067967839753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9551375204802711978559835 14327062807204067967839753)
            ·
              refine ⟨10745297105403050975879815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14327062807204067967839753 10745297105403050975879815)
              ·
                refine ⟨16117945658104576463819723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10745297105403050975879815 16117945658104576463819723)
                ·
                  refine ⟨24176918487156864695729585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16117945658104576463819723 24176918487156864695729585)
                  ·
                    refine ⟨18132688865367648521797189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24176918487156864695729585 18132688865367648521797189)
                    ·
                      refine ⟨3399879162256434097836973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18132688865367648521797189 3399879162256434097836973)
                      ·
                        rfl

theorem cell23_6621241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_6621241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621241 prefixEnd_6621241 := by exact prefixLift 6621241
  have htrace : WordTrace (prefixWord ++ tailWord_6621241) baseStart_6621241 baseEnd_6621241 := by
    simpa [prefixWord, tailWord_6621241, baseEnd_6621241] using wordTrace_append hprefix tailTrace_6621241
  have hstable : (prefixWord ++ tailWord_6621241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621241).length < 2 ^ (prefixWord ++ tailWord_6621241).sum := by decide
  have hdescent : baseEnd_6621241 < baseStart_6621241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621257 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_6621257 : Nat := 118140960795 + 6621257 * 2 ^ 59
def prefixEnd_6621257 : Nat := 4983230072969 + 3 ^ 40 * 6621257 * 2
def baseEnd_6621257 : Nat := 3399887377946906035236899

theorem tailTrace_6621257 : CollatzResearch.WordTrace tailWord_6621257 prefixEnd_6621257 3399887377946906035236899 := by
  unfold tailWord_6621257
  simp only [CollatzResearch.WordTrace]
  refine ⟨241497082573324184511478025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160998055048882789674318683 241497082573324184511478025)
  ·
    refine ⟨181122811929993138383608519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241497082573324184511478025 181122811929993138383608519)
    ·
      refine ⟨271684217894989707575412779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181122811929993138383608519 271684217894989707575412779)
      ·
        refine ⟨407526326842484561363119169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271684217894989707575412779 407526326842484561363119169)
        ·
          refine ⟨305644745131863421022339377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407526326842484561363119169 305644745131863421022339377)
          ·
            refine ⟨229233558848897565766754533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305644745131863421022339377 229233558848897565766754533)
            ·
              refine ⟨42981292284168293581266475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229233558848897565766754533 42981292284168293581266475)
              ·
                refine ⟨64471938426252440371899713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42981292284168293581266475 64471938426252440371899713)
                ·
                  refine ⟨48353953819689330278924785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64471938426252440371899713 48353953819689330278924785)
                  ·
                    refine ⟨36265465364766997709193589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48353953819689330278924785 36265465364766997709193589)
                    ·
                      refine ⟨3399887377946906035236899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36265465364766997709193589 3399887377946906035236899)
                      ·
                        rfl

theorem cell23_6621257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_6621257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621257 prefixEnd_6621257 := by exact prefixLift 6621257
  have htrace : WordTrace (prefixWord ++ tailWord_6621257) baseStart_6621257 baseEnd_6621257 := by
    simpa [prefixWord, tailWord_6621257, baseEnd_6621257] using wordTrace_append hprefix tailTrace_6621257
  have hstable : (prefixWord ++ tailWord_6621257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621257).length < 2 ^ (prefixWord ++ tailWord_6621257).sum := by decide
  have hdescent : baseEnd_6621257 < baseStart_6621257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621261 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_6621261 : Nat := 118140960795 + 6621261 * 2 ^ 59
def prefixEnd_6621261 : Nat := 4983230072969 + 3 ^ 40 * 6621261 * 2
def baseEnd_6621261 : Nat := 3399889431869524019586881

theorem tailTrace_6621261 : CollatzResearch.WordTrace tailWord_6621261 prefixEnd_6621261 3399889431869524019586881 := by
  unfold tailWord_6621261
  simp only [CollatzResearch.WordTrace]
  refine ⟨241497228465309693194623637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160998152310206462129749091 241497228465309693194623637)
  ·
    refine ⟨11320182584311391868497983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 241497228465309693194623637 11320182584311391868497983)
    ·
      refine ⟨16980273876467087802746975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11320182584311391868497983 16980273876467087802746975)
      ·
        refine ⟨25470410814700631704120463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16980273876467087802746975 25470410814700631704120463)
        ·
          refine ⟨38205616222050947556180695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25470410814700631704120463 38205616222050947556180695)
          ·
            refine ⟨57308424333076421334271043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38205616222050947556180695 57308424333076421334271043)
            ·
              refine ⟨85962636499614632001406565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57308424333076421334271043 85962636499614632001406565)
              ·
                refine ⟨16117994343677743500263731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85962636499614632001406565 16117994343677743500263731)
                ·
                  refine ⟨24176991515516615250395597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16117994343677743500263731 24176991515516615250395597)
                  ·
                    refine ⟨9066371818318730718898349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24176991515516615250395597 9066371818318730718898349)
                    ·
                      refine ⟨3399889431869524019586881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9066371818318730718898349 3399889431869524019586881)
                      ·
                        rfl

theorem cell23_6621261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_6621261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621261 prefixEnd_6621261 := by exact prefixLift 6621261
  have htrace : WordTrace (prefixWord ++ tailWord_6621261) baseStart_6621261 baseEnd_6621261 := by
    simpa [prefixWord, tailWord_6621261, baseEnd_6621261] using wordTrace_append hprefix tailTrace_6621261
  have hstable : (prefixWord ++ tailWord_6621261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621261).length < 2 ^ (prefixWord ++ tailWord_6621261).sum := by decide
  have hdescent : baseEnd_6621261 < baseStart_6621261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621294 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_6621294 : Nat := 118140960795 + 6621294 * 2 ^ 59
def prefixEnd_6621294 : Nat := 4983230072969 + 3 ^ 40 * 6621294 * 2
def baseEnd_6621294 : Nat := 1133302125577040796824743

theorem tailTrace_6621294 : CollatzResearch.WordTrace tailWord_6621294 prefixEnd_6621294 1133302125577040796824743 := by
  unfold tailWord_6621294
  simp only [CollatzResearch.WordTrace]
  refine ⟨30187304009273767478821867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160998954716126759887049957 30187304009273767478821867)
  ·
    refine ⟨45280956013910651218232801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30187304009273767478821867 45280956013910651218232801)
    ·
      refine ⟨33960717010432988413674601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45280956013910651218232801 33960717010432988413674601)
      ·
        refine ⟨25470537757824741310255951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33960717010432988413674601 25470537757824741310255951)
        ·
          refine ⟨38205806636737111965383927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25470537757824741310255951 38205806636737111965383927)
          ·
            refine ⟨57308709955105667948075891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38205806636737111965383927 57308709955105667948075891)
            ·
              refine ⟨85963064932658501922113837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57308709955105667948075891 85963064932658501922113837)
              ·
                refine ⟨32236149349746938220792689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85963064932658501922113837 32236149349746938220792689)
                ·
                  refine ⟨24177112012310203665594517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32236149349746938220792689 24177112012310203665594517)
                  ·
                    refine ⟨1133302125577040796824743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24177112012310203665594517 1133302125577040796824743)
                    ·
                      rfl

theorem cell23_6621294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_6621294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621294 prefixEnd_6621294 := by exact prefixLift 6621294
  have htrace : WordTrace (prefixWord ++ tailWord_6621294) baseStart_6621294 baseEnd_6621294 := by
    simpa [prefixWord, tailWord_6621294, baseEnd_6621294] using wordTrace_append hprefix tailTrace_6621294
  have hstable : (prefixWord ++ tailWord_6621294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621294).length < 2 ^ (prefixWord ++ tailWord_6621294).sum := by decide
  have hdescent : baseEnd_6621294 < baseStart_6621294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621341 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 7]
def baseStart_6621341 : Nat := 118140960795 + 6621341 * 2 ^ 59
def prefixEnd_6621341 : Nat := 4983230072969 + 3 ^ 40 * 6621341 * 2
def baseEnd_6621341 : Nat := 377770056702431522954057

theorem tailTrace_6621341 : CollatzResearch.WordTrace tailWord_6621341 prefixEnd_6621341 377770056702431522954057 := by
  unfold tailWord_6621341
  simp only [CollatzResearch.WordTrace]
  refine ⟨241500146305019866857535877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161000097536679911238357251 241500146305019866857535877)
  ·
    refine ⟨45281277432191225035787977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241500146305019866857535877 45281277432191225035787977)
    ·
      refine ⟨33960958074143418776840983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45281277432191225035787977 33960958074143418776840983)
      ·
        refine ⟨50941437111215128165261475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33960958074143418776840983 50941437111215128165261475)
        ·
          refine ⟨76412155666822692247892213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50941437111215128165261475 76412155666822692247892213)
          ·
            refine ⟨7163639593764627398239895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76412155666822692247892213 7163639593764627398239895)
            ·
              refine ⟨10745459390646941097359843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7163639593764627398239895 10745459390646941097359843)
              ·
                refine ⟨16118189085970411646039765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10745459390646941097359843 16118189085970411646039765)
                ·
                  refine ⟨377770056702431522954057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16118189085970411646039765 377770056702431522954057)
                  ·
                    rfl

theorem cell23_6621341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_6621341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621341 prefixEnd_6621341 := by exact prefixLift 6621341
  have htrace : WordTrace (prefixWord ++ tailWord_6621341) baseStart_6621341 baseEnd_6621341 := by
    simpa [prefixWord, tailWord_6621341, baseEnd_6621341] using wordTrace_append hprefix tailTrace_6621341
  have hstable : (prefixWord ++ tailWord_6621341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621341).length < 2 ^ (prefixWord ++ tailWord_6621341).sum := by decide
  have hdescent : baseEnd_6621341 < baseStart_6621341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621391 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 2, 4, 2]
def baseStart_6621391 : Nat := 118140960795 + 6621391 * 2 ^ 59
def prefixEnd_6621391 : Nat := 4983230072969 + 3 ^ 40 * 6621391 * 2
def baseEnd_6621391 : Nat := 3399956184354608510961283

theorem tailTrace_6621391 : CollatzResearch.WordTrace tailWord_6621391 prefixEnd_6621391 3399956184354608510961283 := by
  unfold tailWord_6621391
  simp only [CollatzResearch.WordTrace]
  refine ⟨241501969954838725396856027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161001313303225816931237351 241501969954838725396856027)
  ·
    refine ⟨362252954932258088095284041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241501969954838725396856027 362252954932258088095284041)
    ·
      refine ⟨271689716199193566071463031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362252954932258088095284041 271689716199193566071463031)
      ·
        refine ⟨407534574298790349107194547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271689716199193566071463031 407534574298790349107194547)
        ·
          refine ⟨611301861448185523660791821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407534574298790349107194547 611301861448185523660791821)
          ·
            refine ⟨229238198043069571372796933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611301861448185523660791821 229238198043069571372796933)
            ·
              refine ⟨42982162133075544632399425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229238198043069571372796933 42982162133075544632399425)
              ·
                refine ⟨32236621599806658474299569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42982162133075544632399425 32236621599806658474299569)
                ·
                  refine ⟨24177466199854993855724677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32236621599806658474299569 24177466199854993855724677)
                  ·
                    refine ⟨4533274912472811347948377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24177466199854993855724677 4533274912472811347948377)
                    ·
                      refine ⟨3399956184354608510961283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533274912472811347948377 3399956184354608510961283)
                      ·
                        rfl

theorem cell23_6621391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 4, 2].length) (baseStart_6621391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621391 prefixEnd_6621391 := by exact prefixLift 6621391
  have htrace : WordTrace (prefixWord ++ tailWord_6621391) baseStart_6621391 baseEnd_6621391 := by
    simpa [prefixWord, tailWord_6621391, baseEnd_6621391] using wordTrace_append hprefix tailTrace_6621391
  have hstable : (prefixWord ++ tailWord_6621391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621391).length < 2 ^ (prefixWord ++ tailWord_6621391).sum := by decide
  have hdescent : baseEnd_6621391 < baseStart_6621391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621398 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6621398 : Nat := 118140960795 + 6621398 * 2 ^ 59
def prefixEnd_6621398 : Nat := 4983230072969 + 3 ^ 40 * 6621398 * 2
def baseEnd_6621398 : Nat := 3399959778719189983573751

theorem tailTrace_6621398 : CollatzResearch.WordTrace tailWord_6621398 prefixEnd_6621398 3399959778719189983573751 := by
  unfold tailWord_6621398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15093889079113335349522553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161001483510542243728240565 15093889079113335349522553)
  ·
    refine ⟨11320416809335001512141915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15093889079113335349522553 11320416809335001512141915)
    ·
      refine ⟨16980625214002502268212873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11320416809335001512141915 16980625214002502268212873)
      ·
        refine ⟨12735468910501876701159655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16980625214002502268212873 12735468910501876701159655)
        ·
          refine ⟨19103203365752815051739483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12735468910501876701159655 19103203365752815051739483)
          ·
            refine ⟨28654805048629222577609225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19103203365752815051739483 28654805048629222577609225)
            ·
              refine ⟨21491103786471916933206919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28654805048629222577609225 21491103786471916933206919)
              ·
                refine ⟨32236655679707875399810379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21491103786471916933206919 32236655679707875399810379)
                ·
                  refine ⟨48354983519561813099715569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32236655679707875399810379 48354983519561813099715569)
                  ·
                    refine ⟨36266237639671359824786677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48354983519561813099715569 36266237639671359824786677)
                    ·
                      refine ⟨3399959778719189983573751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36266237639671359824786677 3399959778719189983573751)
                      ·
                        rfl

theorem cell23_6621398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6621398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621398 prefixEnd_6621398 := by exact prefixLift 6621398
  have htrace : WordTrace (prefixWord ++ tailWord_6621398) baseStart_6621398 baseEnd_6621398 := by
    simpa [prefixWord, tailWord_6621398, baseEnd_6621398] using wordTrace_append hprefix tailTrace_6621398
  have hstable : (prefixWord ++ tailWord_6621398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621398).length < 2 ^ (prefixWord ++ tailWord_6621398).sum := by decide
  have hdescent : baseEnd_6621398 < baseStart_6621398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621448 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 6]
def baseStart_6621448 : Nat := 118140960795 + 6621448 * 2 ^ 59
def prefixEnd_6621448 : Nat := 4983230072969 + 3 ^ 40 * 6621448 * 2
def baseEnd_6621448 : Nat := 377776161416879420883169

theorem tailTrace_6621448 : CollatzResearch.WordTrace tailWord_6621448 prefixEnd_6621448 377776161416879420883169 := by
  unfold tailWord_6621448
  simp only [CollatzResearch.WordTrace]
  refine ⟨120752024457816112065840499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161002699277088149421120665 120752024457816112065840499)
  ·
    refine ⟨181128036686724168098760749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120752024457816112065840499 181128036686724168098760749)
    ·
      refine ⟨67923013757521563037035281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181128036686724168098760749 67923013757521563037035281)
      ·
        refine ⟨50942260318141172277776461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67923013757521563037035281 50942260318141172277776461)
        ·
          refine ⟨19103347619302939604166173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50942260318141172277776461 19103347619302939604166173)
          ·
            refine ⟨7163755357238602351562315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19103347619302939604166173 7163755357238602351562315)
            ·
              refine ⟨10745633035857903527343473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7163755357238602351562315 10745633035857903527343473)
              ·
                refine ⟨8059224776893427645507605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10745633035857903527343473 8059224776893427645507605)
                ·
                  refine ⟨377776161416879420883169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8059224776893427645507605 377776161416879420883169)
                  ·
                    rfl

theorem cell23_6621448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 6].length) (baseStart_6621448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621448 prefixEnd_6621448 := by exact prefixLift 6621448
  have htrace : WordTrace (prefixWord ++ tailWord_6621448) baseStart_6621448 baseEnd_6621448 := by
    simpa [prefixWord, tailWord_6621448, baseEnd_6621448] using wordTrace_append hprefix tailTrace_6621448
  have hstable : (prefixWord ++ tailWord_6621448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621448).length < 2 ^ (prefixWord ++ tailWord_6621448).sum := by decide
  have hdescent : baseEnd_6621448 < baseStart_6621448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621486 : List Nat := [4, 1, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_6621486 : Nat := 118140960795 + 6621486 * 2 ^ 59
def prefixEnd_6621486 : Nat := 4983230072969 + 3 ^ 40 * 6621486 * 2
def baseEnd_6621486 : Nat := 1133334988338928546424449

theorem tailTrace_6621486 : CollatzResearch.WordTrace tailWord_6621486 prefixEnd_6621486 1133334988338928546424449 := by
  unfold tailWord_6621486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188179361186819577695539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161003623259663037747709541 30188179361186819577695539)
  ·
    refine ⟨45282269041780229366543309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30188179361186819577695539 45282269041780229366543309)
    ·
      refine ⟨16980850890667586012453741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45282269041780229366543309 16980850890667586012453741)
      ·
        refine ⟨6367819084000344754670153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16980850890667586012453741 6367819084000344754670153)
        ·
          refine ⟨4775864313000258566002615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6367819084000344754670153 4775864313000258566002615)
          ·
            refine ⟨7163796469500387849003923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775864313000258566002615 7163796469500387849003923)
            ·
              refine ⟨10745694704250581773505885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7163796469500387849003923 10745694704250581773505885)
              ·
                refine ⟨4029635514093968165064707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10745694704250581773505885 4029635514093968165064707)
                ·
                  refine ⟨6044453271140952247597061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029635514093968165064707 6044453271140952247597061)
                  ·
                    refine ⟨1133334988338928546424449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044453271140952247597061 1133334988338928546424449)
                    ·
                      rfl

theorem cell23_6621486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_6621486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621486 prefixEnd_6621486 := by exact prefixLift 6621486
  have htrace : WordTrace (prefixWord ++ tailWord_6621486) baseStart_6621486 baseEnd_6621486 := by
    simpa [prefixWord, tailWord_6621486, baseEnd_6621486] using wordTrace_append hprefix tailTrace_6621486
  have hstable : (prefixWord ++ tailWord_6621486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621486).length < 2 ^ (prefixWord ++ tailWord_6621486).sum := by decide
  have hdescent : baseEnd_6621486 < baseStart_6621486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621491 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 6, 4]
def baseStart_6621491 : Nat := 118140960795 + 6621491 * 2 ^ 59
def prefixEnd_6621491 : Nat := 4983230072969 + 3 ^ 40 * 6621491 * 2
def baseEnd_6621491 : Nat := 1133335844140019373236941

theorem tailTrace_6621491 : CollatzResearch.WordTrace tailWord_6621491 prefixEnd_6621491 1133335844140019373236941 := by
  unfold tailWord_6621491
  simp only [CollatzResearch.WordTrace]
  refine ⟨241505617254476442475496327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161003744836317628316997551 241505617254476442475496327)
  ·
    refine ⟨362258425881714663713244491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241505617254476442475496327 362258425881714663713244491)
    ·
      refine ⟨543387638822571995569866737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362258425881714663713244491 543387638822571995569866737)
      ·
        refine ⟨407540729116928996677400053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543387638822571995569866737 407540729116928996677400053)
        ·
          refine ⟨38206943354712093438506255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 407540729116928996677400053 38206943354712093438506255)
          ·
            refine ⟨57310415032068140157759383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38206943354712093438506255 57310415032068140157759383)
            ·
              refine ⟨85965622548102210236639075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57310415032068140157759383 85965622548102210236639075)
              ·
                refine ⟨128948433822153315354958613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85965622548102210236639075 128948433822153315354958613)
                ·
                  refine ⟨6044457835413436657263685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128948433822153315354958613 6044457835413436657263685)
                  ·
                    refine ⟨1133335844140019373236941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044457835413436657263685 1133335844140019373236941)
                    ·
                      rfl

theorem cell23_6621491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 4].length) (baseStart_6621491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621491 prefixEnd_6621491 := by exact prefixLift 6621491
  have htrace : WordTrace (prefixWord ++ tailWord_6621491) baseStart_6621491 baseEnd_6621491 := by
    simpa [prefixWord, tailWord_6621491, baseEnd_6621491] using wordTrace_append hprefix tailTrace_6621491
  have hstable : (prefixWord ++ tailWord_6621491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621491).length < 2 ^ (prefixWord ++ tailWord_6621491).sum := by decide
  have hdescent : baseEnd_6621491 < baseStart_6621491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621498 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_6621498 : Nat := 118140960795 + 6621498 * 2 ^ 59
def prefixEnd_6621498 : Nat := 4983230072969 + 3 ^ 40 * 6621498 * 2
def baseEnd_6621498 : Nat := 3400011126784639592323291

theorem tailTrace_6621498 : CollatzResearch.WordTrace tailWord_6621498 prefixEnd_6621498 3400011126784639592323291 := by
  unfold tailWord_6621498
  simp only [CollatzResearch.WordTrace]
  refine ⟨60376468141362770667750287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161003915043634055114000765 60376468141362770667750287)
  ·
    refine ⟨90564702212044156001625431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60376468141362770667750287 90564702212044156001625431)
    ·
      refine ⟨135847053318066234002438147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90564702212044156001625431 135847053318066234002438147)
      ·
        refine ⟨203770579977099351003657221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135847053318066234002438147 203770579977099351003657221)
        ·
          refine ⟨38206983745706128313185729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203770579977099351003657221 38206983745706128313185729)
          ·
            refine ⟨28655237809279596234889297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38206983745706128313185729 28655237809279596234889297)
            ·
              refine ⟨21491428356959697176166973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28655237809279596234889297 21491428356959697176166973)
              ·
                refine ⟨8059285633859886441062615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21491428356959697176166973 8059285633859886441062615)
                ·
                  refine ⟨12088928450789829661593923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8059285633859886441062615 12088928450789829661593923)
                  ·
                    refine ⟨18133392676184744492390885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12088928450789829661593923 18133392676184744492390885)
                    ·
                      refine ⟨3400011126784639592323291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18133392676184744492390885 3400011126784639592323291)
                      ·
                        rfl

theorem cell23_6621498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_6621498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621498 prefixEnd_6621498 := by exact prefixLift 6621498
  have htrace : WordTrace (prefixWord ++ tailWord_6621498) baseStart_6621498 baseEnd_6621498 := by
    simpa [prefixWord, tailWord_6621498, baseEnd_6621498] using wordTrace_append hprefix tailTrace_6621498
  have hstable : (prefixWord ++ tailWord_6621498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621498).length < 2 ^ (prefixWord ++ tailWord_6621498).sum := by decide
  have hdescent : baseEnd_6621498 < baseStart_6621498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621521 : List Nat := [1, 2, 2, 1, 4, 3, 2, 8]
def baseStart_6621521 : Nat := 118140960795 + 6621521 * 2 ^ 59
def prefixEnd_6621521 : Nat := 4983230072969 + 3 ^ 40 * 6621521 * 2
def baseEnd_6621521 : Nat := 125926775438507148234655

theorem tailTrace_6621521 : CollatzResearch.WordTrace tailWord_6621521 prefixEnd_6621521 125926775438507148234655 := by
  unfold tailWord_6621521
  simp only [CollatzResearch.WordTrace]
  refine ⟨241506711444367757599088417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161004474296245171732725611 241506711444367757599088417)
  ·
    refine ⟨181130033583275818199316313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241506711444367757599088417 181130033583275818199316313)
    ·
      refine ⟨135847525187456863649487235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181130033583275818199316313 135847525187456863649487235)
      ·
        refine ⟨203771287781185295474230853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135847525187456863649487235 203771287781185295474230853)
        ·
          refine ⟨38207116458972242901418285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203771287781185295474230853 38207116458972242901418285)
          ·
            refine ⟨14327668672114591088031857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38207116458972242901418285 14327668672114591088031857)
            ·
              refine ⟨10745751504085943316023893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14327668672114591088031857 10745751504085943316023893)
              ·
                refine ⟨125926775438507148234655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10745751504085943316023893 125926775438507148234655)
                ·
                  rfl

theorem cell23_6621521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 8].length) (baseStart_6621521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621521 prefixEnd_6621521 := by exact prefixLift 6621521
  have htrace : WordTrace (prefixWord ++ tailWord_6621521) baseStart_6621521 baseEnd_6621521 := by
    simpa [prefixWord, tailWord_6621521, baseEnd_6621521] using wordTrace_append hprefix tailTrace_6621521
  have hstable : (prefixWord ++ tailWord_6621521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621521).length < 2 ^ (prefixWord ++ tailWord_6621521).sum := by decide
  have hdescent : baseEnd_6621521 < baseStart_6621521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621525 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_6621525 : Nat := 118140960795 + 6621525 * 2 ^ 59
def prefixEnd_6621525 : Nat := 4983230072969 + 3 ^ 40 * 6621525 * 2
def baseEnd_6621525 : Nat := 1133341663587436995561889

theorem tailTrace_6621525 : CollatzResearch.WordTrace tailWord_6621525 prefixEnd_6621525 1133341663587436995561889 := by
  unfold tailWord_6621525
  simp only [CollatzResearch.WordTrace]
  refine ⟨241506857336353266282234029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161004571557568844188156019 241506857336353266282234029)
  ·
    refine ⟨90565071501132474855837761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241506857336353266282234029 90565071501132474855837761)
    ·
      refine ⟨67923803625849356141878321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90565071501132474855837761 67923803625849356141878321)
      ·
        refine ⟨50942852719387017106408741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67923803625849356141878321 50942852719387017106408741)
        ·
          refine ⟨9551784884885065707451639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50942852719387017106408741 9551784884885065707451639)
          ·
            refine ⟨14327677327327598561177459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9551784884885065707451639 14327677327327598561177459)
            ·
              refine ⟨21491515990991397841766189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14327677327327598561177459 21491515990991397841766189)
              ·
                refine ⟨8059318496621774190662321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21491515990991397841766189 8059318496621774190662321)
                ·
                  refine ⟨6044488872466330642996741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8059318496621774190662321 6044488872466330642996741)
                  ·
                    refine ⟨1133341663587436995561889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044488872466330642996741 1133341663587436995561889)
                    ·
                      rfl

theorem cell23_6621525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_6621525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621525 prefixEnd_6621525 := by exact prefixLift 6621525
  have htrace : WordTrace (prefixWord ++ tailWord_6621525) baseStart_6621525 baseEnd_6621525 := by
    simpa [prefixWord, tailWord_6621525, baseEnd_6621525] using wordTrace_append hprefix tailTrace_6621525
  have hstable : (prefixWord ++ tailWord_6621525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621525).length < 2 ^ (prefixWord ++ tailWord_6621525).sum := by decide
  have hdescent : baseEnd_6621525 < baseStart_6621525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621565 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_6621565 : Nat := 118140960795 + 6621565 * 2 ^ 59
def prefixEnd_6621565 : Nat := 4983230072969 + 3 ^ 40 * 6621565 * 2
def baseEnd_6621565 : Nat := 3400045529988490830185483

theorem tailTrace_6621565 : CollatzResearch.WordTrace tailWord_6621565 prefixEnd_6621565 3400045529988490830185483 := by
  unfold tailWord_6621565
  simp only [CollatzResearch.WordTrace]
  refine ⟨241508316256208353113690149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161005544170805568742460099 241508316256208353113690149)
  ·
    refine ⟨45282809298039066208816903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241508316256208353113690149 45282809298039066208816903)
    ·
      refine ⟨67924213947058599313225355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45282809298039066208816903 67924213947058599313225355)
      ·
        refine ⟨101886320920587898969838033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67924213947058599313225355 101886320920587898969838033)
        ·
          refine ⟨76414740690440924227378525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101886320920587898969838033 76414740690440924227378525)
          ·
            refine ⟨28655527758915346585266947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76414740690440924227378525 28655527758915346585266947)
            ·
              refine ⟨42983291638373019877900421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28655527758915346585266947 42983291638373019877900421)
              ·
                refine ⟨8059367182194941227106329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42983291638373019877900421 8059367182194941227106329)
                ·
                  refine ⟨6044525386646205920329747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8059367182194941227106329 6044525386646205920329747)
                  ·
                    refine ⟨9066788079969308880494621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6044525386646205920329747 9066788079969308880494621)
                    ·
                      refine ⟨3400045529988490830185483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9066788079969308880494621 3400045529988490830185483)
                      ·
                        rfl

theorem cell23_6621565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_6621565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621565 prefixEnd_6621565 := by exact prefixLift 6621565
  have htrace : WordTrace (prefixWord ++ tailWord_6621565) baseStart_6621565 baseEnd_6621565 := by
    simpa [prefixWord, tailWord_6621565, baseEnd_6621565] using wordTrace_append hprefix tailTrace_6621565
  have hstable : (prefixWord ++ tailWord_6621565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621565).length < 2 ^ (prefixWord ++ tailWord_6621565).sum := by decide
  have hdescent : baseEnd_6621565 < baseStart_6621565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621582 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6621582 : Nat := 118140960795 + 6621582 * 2 ^ 59
def prefixEnd_6621582 : Nat := 4983230072969 + 3 ^ 40 * 6621582 * 2
def baseEnd_6621582 : Nat := 3400054259159617263672905

theorem tailTrace_6621582 : CollatzResearch.WordTrace tailWord_6621582 prefixEnd_6621582 3400054259159617263672905 := by
  unfold tailWord_6621582
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188617037143345627132375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161005957531431176678039333 30188617037143345627132375)
  ·
    refine ⟨45282925555715018440698563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30188617037143345627132375 45282925555715018440698563)
    ·
      refine ⟨67924388333572527661047845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45282925555715018440698563 67924388333572527661047845)
      ·
        refine ⟨12735822812544848936446471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67924388333572527661047845 12735822812544848936446471)
        ·
          refine ⟨19103734218817273404669707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12735822812544848936446471 19103734218817273404669707)
          ·
            refine ⟨28655601328225910107004561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19103734218817273404669707 28655601328225910107004561)
            ·
              refine ⟨21491700996169432580253421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28655601328225910107004561 21491700996169432580253421)
              ·
                refine ⟨8059387873563537217595033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21491700996169432580253421 8059387873563537217595033)
                ·
                  refine ⟨6044540905172652913196275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8059387873563537217595033 6044540905172652913196275)
                  ·
                    refine ⟨9066811357758979369794413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6044540905172652913196275 9066811357758979369794413)
                    ·
                      refine ⟨3400054259159617263672905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9066811357758979369794413 3400054259159617263672905)
                      ·
                        rfl

theorem cell23_6621582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6621582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621582 prefixEnd_6621582 := by exact prefixLift 6621582
  have htrace : WordTrace (prefixWord ++ tailWord_6621582) baseStart_6621582 baseEnd_6621582 := by
    simpa [prefixWord, tailWord_6621582, baseEnd_6621582] using wordTrace_append hprefix tailTrace_6621582
  have hstable : (prefixWord ++ tailWord_6621582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621582).length < 2 ^ (prefixWord ++ tailWord_6621582).sum := by decide
  have hdescent : baseEnd_6621582 < baseStart_6621582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621591 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_6621591 : Nat := 118140960795 + 6621591 * 2 ^ 59
def prefixEnd_6621591 : Nat := 4983230072969 + 3 ^ 40 * 6621591 * 2
def baseEnd_6621591 : Nat := 3400058880485507728460363

theorem tailTrace_6621591 : CollatzResearch.WordTrace tailWord_6621591 prefixEnd_6621591 3400058880485507728460363 := by
  unfold tailWord_6621591
  simp only [CollatzResearch.WordTrace]
  refine ⟨241509264554114159554136627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161006176369409439702757751 241509264554114159554136627)
  ·
    refine ⟨362263896831171239331204941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241509264554114159554136627 362263896831171239331204941)
    ·
      refine ⟨135848961311689214749201853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362263896831171239331204941 135848961311689214749201853)
      ·
        refine ⟨50943360491883455530950695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135848961311689214749201853 50943360491883455530950695)
        ·
          refine ⟨76415040737825183296426043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50943360491883455530950695 76415040737825183296426043)
          ·
            refine ⟨114622561106737774944639065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76415040737825183296426043 114622561106737774944639065)
            ·
              refine ⟨85966920830053331208479299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114622561106737774944639065 85966920830053331208479299)
              ·
                refine ⟨128950381245079996812718949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85966920830053331208479299 128950381245079996812718949)
                ·
                  refine ⟨24178196483452499402384803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128950381245079996812718949 24178196483452499402384803)
                  ·
                    refine ⟨36267294725178749103577205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24178196483452499402384803 36267294725178749103577205)
                    ·
                      refine ⟨3400058880485507728460363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36267294725178749103577205 3400058880485507728460363)
                      ·
                        rfl

theorem cell23_6621591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_6621591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621591 prefixEnd_6621591 := by exact prefixLift 6621591
  have htrace : WordTrace (prefixWord ++ tailWord_6621591) baseStart_6621591 baseEnd_6621591 := by
    simpa [prefixWord, tailWord_6621591, baseEnd_6621591] using wordTrace_append hprefix tailTrace_6621591
  have hstable : (prefixWord ++ tailWord_6621591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621591).length < 2 ^ (prefixWord ++ tailWord_6621591).sum := by decide
  have hdescent : baseEnd_6621591 < baseStart_6621591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621605 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 4, 2, 2]
def baseStart_6621605 : Nat := 118140960795 + 6621605 * 2 ^ 59
def prefixEnd_6621605 : Nat := 4983230072969 + 3 ^ 40 * 6621605 * 2
def baseEnd_6621605 : Nat := 3400066069214670673685299

theorem tailTrace_6621605 : CollatzResearch.WordTrace tailWord_6621605 prefixEnd_6621605 3400066069214670673685299 := by
  unfold tailWord_6621605
  simp only [CollatzResearch.WordTrace]
  refine ⟨241509775176063439945146269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161006516784042293296764179 241509775176063439945146269)
  ·
    refine ⟨90566165691023789979429851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241509775176063439945146269 90566165691023789979429851)
    ·
      refine ⟨135849248536535684969144777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90566165691023789979429851 135849248536535684969144777)
      ·
        refine ⟨101886936402401763726858583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135849248536535684969144777 101886936402401763726858583)
        ·
          refine ⟨152830404603602645590287875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101886936402401763726858583 152830404603602645590287875)
          ·
            refine ⟨229245606905403968385431813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152830404603602645590287875 229245606905403968385431813)
            ·
              refine ⟨42983551294763244072268465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229245606905403968385431813 42983551294763244072268465)
              ·
                refine ⟨32237663471072433054201349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42983551294763244072268465 32237663471072433054201349)
                ·
                  refine ⟨6044561900826081197662753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32237663471072433054201349 6044561900826081197662753)
                  ·
                    refine ⟨4533421425619560898247065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6044561900826081197662753 4533421425619560898247065)
                    ·
                      refine ⟨3400066069214670673685299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4533421425619560898247065 3400066069214670673685299)
                      ·
                        rfl

theorem cell23_6621605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_6621605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621605 prefixEnd_6621605 := by exact prefixLift 6621605
  have htrace : WordTrace (prefixWord ++ tailWord_6621605) baseStart_6621605 baseEnd_6621605 := by
    simpa [prefixWord, tailWord_6621605, baseEnd_6621605] using wordTrace_append hprefix tailTrace_6621605
  have hstable : (prefixWord ++ tailWord_6621605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621605).length < 2 ^ (prefixWord ++ tailWord_6621605).sum := by decide
  have hdescent : baseEnd_6621605 < baseStart_6621605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621628 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 7]
def baseStart_6621628 : Nat := 118140960795 + 6621628 * 2 ^ 59
def prefixEnd_6621628 : Nat := 4983230072969 + 3 ^ 40 * 6621628 * 2
def baseEnd_6621628 : Nat := 377786431029969342633077

theorem tailTrace_6621628 : CollatzResearch.WordTrace tailWord_6621628 prefixEnd_6621628 377786431029969342633077 := by
  unfold tailWord_6621628
  simp only [CollatzResearch.WordTrace]
  refine ⟨120755307027490057436616769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161007076036653409915489025 120755307027490057436616769)
  ·
    refine ⟨90566480270617543077462577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120755307027490057436616769 90566480270617543077462577)
    ·
      refine ⟨67924860202963157308096933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90566480270617543077462577 67924860202963157308096933)
      ·
        refine ⟨12735911288055591995268175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67924860202963157308096933 12735911288055591995268175)
        ·
          refine ⟨19103866932083387992902263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12735911288055591995268175 19103866932083387992902263)
          ·
            refine ⟨28655800398125081989353395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19103866932083387992902263 28655800398125081989353395)
            ·
              refine ⟨42983700597187622984030093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28655800398125081989353395 42983700597187622984030093)
              ·
                refine ⟨16118887723945358619011285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42983700597187622984030093 16118887723945358619011285)
                ·
                  refine ⟨377786431029969342633077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16118887723945358619011285 377786431029969342633077)
                  ·
                    rfl

theorem cell23_6621628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_6621628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621628 prefixEnd_6621628 := by exact prefixLift 6621628
  have htrace : WordTrace (prefixWord ++ tailWord_6621628) baseStart_6621628 baseEnd_6621628 := by
    simpa [prefixWord, tailWord_6621628, baseEnd_6621628] using wordTrace_append hprefix tailTrace_6621628
  have hstable : (prefixWord ++ tailWord_6621628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621628).length < 2 ^ (prefixWord ++ tailWord_6621628).sum := by decide
  have hdescent : baseEnd_6621628 < baseStart_6621628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6621633 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6621633 : Nat := 118140960795 + 6621633 * 2 ^ 59
def prefixEnd_6621633 : Nat := 4983230072969 + 3 ^ 40 * 6621633 * 2
def baseEnd_6621633 : Nat := 3400080446672996564135171

theorem tailTrace_6621633 : CollatzResearch.WordTrace tailWord_6621633 prefixEnd_6621633 3400080446672996564135171 := by
  unfold tailWord_6621633
  simp only [CollatzResearch.WordTrace]
  refine ⟨241510796419962000727165553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161007197613308000484777035 241510796419962000727165553)
  ·
    refine ⟨181133097314971500545374165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241510796419962000727165553 181133097314971500545374165)
    ·
      refine ⟨4245306968319644544032207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 181133097314971500545374165 4245306968319644544032207)
      ·
        refine ⟨6367960452479466816048311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4245306968319644544032207 6367960452479466816048311)
        ·
          refine ⟨9551940678719200224072467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367960452479466816048311 9551940678719200224072467)
          ·
            refine ⟨14327911018078800336108701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9551940678719200224072467 14327911018078800336108701)
            ·
              refine ⟨5372966631779550126040763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14327911018078800336108701 5372966631779550126040763)
              ·
                refine ⟨8059449947669325189061145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5372966631779550126040763 8059449947669325189061145)
                ·
                  refine ⟨6044587460751993891795859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8059449947669325189061145 6044587460751993891795859)
                  ·
                    refine ⟨9066881191127990837693789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6044587460751993891795859 9066881191127990837693789)
                    ·
                      refine ⟨3400080446672996564135171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9066881191127990837693789 3400080446672996564135171)
                      ·
                        rfl

theorem cell23_6621633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6621633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6621633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6621633 prefixEnd_6621633 := by exact prefixLift 6621633
  have htrace : WordTrace (prefixWord ++ tailWord_6621633) baseStart_6621633 baseEnd_6621633 := by
    simpa [prefixWord, tailWord_6621633, baseEnd_6621633] using wordTrace_append hprefix tailTrace_6621633
  have hstable : (prefixWord ++ tailWord_6621633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6621633).length < 2 ^ (prefixWord ++ tailWord_6621633).sum := by decide
  have hdescent : baseEnd_6621633 < baseStart_6621633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6621633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
